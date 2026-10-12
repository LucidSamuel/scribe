#!/usr/bin/env python3
"""Check source binding, fresh Ragu extraction, and the Lean circuit refinement.

Source hashes invalidate stale evidence; they do NOT prove Rust semantics.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "corpus/refinement/ragu-horner-three.binding.json"


def main():
    manifest = json.loads(MANIFEST.read_text())
    for name, expected in manifest["sha256"].items():
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            sys.exit(f"Source binding changed: {name}. Review and reprove; do not silently bless.")
    subprocess.run([
        "cargo", "test", "-p", "frontend-ragu", "--test", "horner_refinement",
        "--locked", "--offline",
    ], cwd=ROOT, check=True)
    subprocess.run([
        "lake", "env", "lean", "ZkGadgets/Refinement/RaguHorner.lean",
    ], cwd=ROOT / "lean", check=True)
    print("PASS: source binding, extracted-model binding, Lean circuit refinement")
    print("BOUNDARY: Ragu Rust semantics and extractor fidelity are not proved here.")


if __name__ == "__main__":
    main()
