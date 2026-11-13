# Pinned Orchard target

The files under upstream/ are exact organizer JSON bytes at the revision in
manifest.json. They are data/specification fixtures, not an attack engine.
Their origin is the Layr-Labs/hash-smash repository; the constants identify
zcash/halo2 halo2_poseidon 0.2.0 and the upstream source hash.

The reference verifier is not vendored. Differential tests take its checkout
path explicitly and check the verifier and constant-file hashes before loading
only the organizer permutation module. They do not load or execute candidate
Python, launch judges, or contact Yukon.

From the Scribe repository root, set `ORGANIZER_ROOT` to your pinned organizer
checkout before the differential test:

```sh
python3 scripts/generate-orchard-constants.py --check
python3 scripts/test-orchard-reference.py --organizer-root "$ORGANIZER_ROOT"
cargo run -p scribe-cli -- claim verify --package examples/claims/orchard-model.json --root . --lake-dir lean
```

The differential suite uses seed 20261114 and covers 1,025 cases. Both input and
expected output byte sequences are generated independently by Python using the
organizer's canonical little-endian interface. The executable Lean checker is
separate from the kernel-checked reference vector in Poseidon/Vectors.lean.

submission-review.json is a read-only historical observation of Yukon status
and local candidate hashes. It is not a signed review receipt or reusable proof
certificate. The corresponding audit is docs/hashsmash-audit.md.

Do not derive the full-round count from the profile's full_rounds field, which
contains 56: the explicit round_selection and deployed reference define eight
full rounds plus r partial rounds. Do not derive score projection from the
resource model's legacy time-only prose: the separate pinned scoring policy
defines the time-memory metric.
