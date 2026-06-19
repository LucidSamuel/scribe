# syntax=docker/dockerfile:1.7
# Scribe — LLM proof-completion loop for ZK gadgets, Lean kernel as oracle.
#
# Multi-stage build overview:
#   rust-builder  → compiles all workspace crates; extracts release binaries
#   lean-builder  → installs elan + lean toolchain; pre-caches Mathlib oleans via lake exe cache get
#   runtime       → slim Ubuntu 24.04 image; copies binaries + Lean toolchain; ~3.2 GB
#                   (Mathlib oleans are ~2.5 GB; unavoidable for offline proof checking)
#
# OCI labels ---------------------------------------------------------------
# org.opencontainers.image.source  https://github.com/lucidsamuel/scribe
# org.opencontainers.image.title   scribe
# org.opencontainers.image.description  LLM proof-completion loop for ZK gadgets

ARG UBUNTU_VERSION=24.04
ARG RUST_VERSION=1.82

# ── stage 1: rust-builder ─────────────────────────────────────────────────
FROM ubuntu:${UBUNTU_VERSION} AS rust-builder

# Install build essentials; pin apt-get to non-interactive
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        curl \
        pkg-config \
        libssl-dev \
        ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Install Rust via rustup (pinned stable channel)
ARG RUST_VERSION
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH
# hadolint ignore=DL3004,DL4006
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --default-toolchain ${RUST_VERSION} --no-modify-path \
    && rustup show

WORKDIR /build

# Cache dependency compilation: copy manifests first, then source.
# Layer order: Cargo workspace root → each crate manifest → source
COPY Cargo.toml Cargo.lock ./
COPY crates/gadget-ir/Cargo.toml   crates/gadget-ir/Cargo.toml
COPY crates/lean-emit/Cargo.toml   crates/lean-emit/Cargo.toml
COPY crates/proof-pilot/Cargo.toml crates/proof-pilot/Cargo.toml
COPY crates/halva-bridge/Cargo.toml crates/halva-bridge/Cargo.toml
COPY crates/bench/Cargo.toml       crates/bench/Cargo.toml
COPY crates/scribe-cli/Cargo.toml  crates/scribe-cli/Cargo.toml

# Create stub lib/main files so `cargo build` can resolve the dependency graph
# without the full source; replaced by COPY below.
RUN mkdir -p \
        crates/gadget-ir/src \
        crates/lean-emit/src \
        crates/proof-pilot/src \
        crates/halva-bridge/src \
        crates/scribe-cli/src \
        crates/bench/src \
    && for f in \
        crates/gadget-ir/src/lib.rs \
        crates/lean-emit/src/main.rs \
        crates/proof-pilot/src/lib.rs \
        crates/proof-pilot/src/main.rs \
        crates/halva-bridge/src/lib.rs \
        crates/halva-bridge/src/main.rs \
        crates/scribe-cli/src/main.rs \
        crates/bench/src/main.rs; \
    do echo "fn main() {}" > "$f"; done \
    && echo "" > crates/bench/src/lib.rs

# Pre-warm the dependency cache
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/usr/local/cargo/git \
    --mount=type=cache,target=/build/target \
    cargo build --release --workspace 2>/dev/null || true

# Now copy the full source and do the real build
COPY crates/ crates/
COPY prompts/ prompts/

RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/usr/local/cargo/git \
    --mount=type=cache,target=/build/target \
    cargo build --release --workspace \
    && mkdir -p /out/bin \
    # Copy whichever binaries exist; scribe-cli agent delivers `scribe` binary
    && for bin in proof-pilot halva-bridge scribe; do \
        if [ -f "target/release/$bin" ]; then \
            cp "target/release/$bin" /out/bin/; \
        fi; \
    done \
    && ls -lh /out/bin/

# ── stage 2: lean-builder ─────────────────────────────────────────────────
FROM ubuntu:${UBUNTU_VERSION} AS lean-builder

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl \
        git \
        ca-certificates \
        libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager) to a fixed prefix
ENV ELAN_HOME=/opt/elan \
    PATH=/opt/elan/bin:$PATH
# hadolint ignore=DL4006
RUN curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan --version

WORKDIR /lean

# Copy the Lean project (lakefile, toolchain, manifest, sources)
COPY lean/ .

# Pin the toolchain recorded in lean/lean-toolchain (leanprover/lean4:v4.30.0-rc2).
# lean-toolchain sits at /lean/lean-toolchain (WORKDIR /lean, COPY lean/ .)
# hadolint ignore=SC2046
RUN TOOLCHAIN="$(cat lean-toolchain)" \
    && elan toolchain install "$TOOLCHAIN" \
    && elan override set "$TOOLCHAIN"

# Pre-cache Mathlib oleans from the mathlib4 olean server.
# lake exe cache get downloads pre-built .olean files keyed to the lake-manifest rev
# (mathlib rev 53f8a93a7739dd4eb33926f645811ebb6cee21bf at time of image build).
# This is the heaviest step (~2.5 GB) but makes the runtime image self-contained.
# hadolint ignore=SC2015
RUN lake update && lake exe cache get || echo "olean cache unavailable; will build from source"

# Build the ZkGadgets library with the pre-cached oleans
RUN lake build

# ── stage 3: runtime ──────────────────────────────────────────────────────
FROM ubuntu:${UBUNTU_VERSION} AS runtime

LABEL org.opencontainers.image.source="https://github.com/lucidsamuel/scribe" \
      org.opencontainers.image.title="scribe" \
      org.opencontainers.image.description="LLM proof-completion loop for ZK gadgets, Lean kernel as oracle" \
      org.opencontainers.image.licenses="MIT"

ENV DEBIAN_FRONTEND=noninteractive
# Runtime deps: libgmp (Lean), git (lake), curl (backends), ca-certificates (TLS)
RUN apt-get update && apt-get install -y --no-install-recommends \
        libgmp-dev \
        git \
        curl \
        ca-certificates \
        python3 \
        python3-pip \
    && rm -rf /var/lib/apt/lists/*

# ── copy Lean toolchain + oleans ──
COPY --from=lean-builder /opt/elan /opt/elan

# Copy the pre-built Lean project (includes .lake/ with Mathlib oleans)
COPY --from=lean-builder /lean /opt/lean-project

# ── copy Rust release binaries ──
COPY --from=rust-builder /out/bin/ /usr/local/bin/

# ── copy support files ──
COPY prompts/ /opt/scribe/prompts/
COPY examples/ /opt/scribe/examples/

# PATH: elan-managed lake + lean take precedence; /usr/local/bin has scribe, proof-pilot, halva-bridge
ENV PATH="/opt/elan/bin:${PATH}" \
    ELAN_HOME="/opt/elan" \
    LAKE_DIR="/opt/lean-project" \
    SCRIBE_PROMPTS_DIR="/opt/scribe/prompts"

# Verify Lean toolchain is accessible (fail fast if elan copy is broken)
RUN lean --version && lake --version

# Default working directory for user-supplied circuits / proofs
WORKDIR /workspace

# Expose help text as the default CMD; override with any subcommand.
# e.g.  docker run ghcr.io/lucidsamuel/scribe:latest scribe demo
#        docker run -v $(pwd):/workspace ghcr.io/lucidsamuel/scribe:latest \
#                   scribe verify --halva-output /workspace/extracted.lean \
#                                 --spec-file /workspace/spec.lean \
#                                 --output /workspace/Proof.lean
CMD ["scribe", "--help"]
