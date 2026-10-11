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
ARG RUST_VERSION=1.97.1

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

# Build the real workspace; BuildKit retains Cargo dependency and target caches.
COPY Cargo.toml Cargo.lock rust-toolchain.toml ./
COPY crates/ crates/
COPY schema/ schema/
COPY prompts/ prompts/

RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/usr/local/cargo/git \
    --mount=type=cache,target=/build/target \
    cargo build --release --workspace --locked \
    && mkdir -p /out/bin \
    && cp target/release/proof-pilot target/release/scribe /out/bin/

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
# Do not run `lake update` here: the committed lake-manifest.json pins dependency
# revisions that match lean/lean-toolchain. Updating during the image build can
# pull newer Mathlib/Batteries code that requires a different Lean compiler.
# `lake exe cache get` downloads pre-built .olean files keyed to the manifest.
# This is the heaviest step (~2.5 GB) but makes the runtime image self-contained.
# hadolint ignore=SC2015
RUN lake exe cache get || echo "olean cache unavailable; will build from source"

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

# PATH: elan-managed lake + lean take precedence; /usr/local/bin has scribe, proof-pilot
ENV PATH="/opt/elan/bin:${PATH}" \
    ELAN_HOME="/opt/elan" \
    LAKE_DIR="/opt/lean-project" \
    SCRIBE_PROMPTS_DIR="/opt/scribe/prompts" \
    SCRIBE_EXAMPLES_DIR="/opt/scribe/examples"

# Configure and verify the runtime Lean toolchain. The builder stage sets an
# override for /lean, but the runtime image uses /workspace as its default CWD,
# so it also needs a default elan toolchain.
RUN TOOLCHAIN="$(cat /opt/lean-project/lean-toolchain)" \
    && elan default "$TOOLCHAIN" \
    && lean --version \
    && lake --version \
    && rm -rf /opt/lean-project/ZkGadgets/Bench

# Default working directory for user-supplied circuits / proofs
WORKDIR /workspace

# Expose help text as the default CMD; override with any subcommand.
# e.g.  docker run ghcr.io/lucidsamuel/scribe:latest scribe demo
CMD ["scribe", "--help"]
