#!/usr/bin/env python3
"""Compare Lean with the pinned organizer verifier; never imports candidate programs."""
import argparse
import hashlib
import importlib.util
import json
import random
import subprocess
import sys
import tempfile
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "fixtures/hashsmash/orchard"
P = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001


def reference(checkout):
    manifest = json.loads((FIXTURE / "manifest.json").read_text())
    path = checkout / "verifier/poseidon.py"
    if hashlib.sha256(path.read_bytes()).hexdigest() != manifest["reference_verifier_sha256"]:
        raise ValueError("organizer reference differs from pinned verifier")
    constants = "pareto/orchard-pallas-constants.json"
    if hashlib.sha256((checkout / constants).read_bytes()).hexdigest() != manifest["files"][constants]:
        raise ValueError("organizer constants differ from pinned constants")
    # Load ONLY the pinned organizer reference. Avoid verifier/__init__.py,
    # which imports intake and unrelated verifier modules.
    name = "scribe_organizer_reference"
    package = types.ModuleType(name)
    package.__path__ = []
    errors = types.ModuleType(name + ".errors")
    errors.VerificationError = type("VerificationError", (ValueError,), {})
    sys.modules[name] = package
    sys.modules[name + ".errors"] = errors
    spec = importlib.util.spec_from_file_location(name + ".poseidon", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--organizer-root", type=Path, required=True)
    args = parser.parse_args()
    subprocess.run([sys.executable, str(ROOT / "scripts/generate-orchard-constants.py"), "--check"], check=True)
    ref = reference(args.organizer_root)
    rng = random.Random(20261114)
    cases = [(r, nk, rho) for r in [0, 3, 4, 5, 56]
             for nk, rho in [(0, 0), (1, 2), (P-1, P-1), (0, P-1)]]
    cases += [(i % 57, rng.randrange(P), rng.randrange(P)) for i in range(1000)]
    cases += [(3, P, 0), (3, 0, P), (3, 2**256-1, 0), (57, 0, 0), (100, 1, 2)]
    rows = []
    for r, nk, rho in cases:
        message = nk.to_bytes(32, "little") + rho.to_bytes(32, "little")
        try:
            digest = ref.digest(message, r)
            value = str(int.from_bytes(digest, "little"))
            output_bytes = ",".join(map(str, digest))
        except ref.PoseidonInputError:
            value = "none"
            output_bytes = "none"
        input_bytes = ",".join(map(str, message))
        rows.append(f"{r} {nk} {rho} {value} {input_bytes} {output_bytes}")
    with tempfile.TemporaryDirectory(prefix="scribe-orchard-") as temporary:
        vectors = Path(temporary) / "vectors.txt"
        vectors.write_text("\n".join(rows) + "\n")
        subprocess.run(["lake", "build", "ZkGadgets.Poseidon.CheckVectors"], cwd=ROOT / "lean", check=True)
        subprocess.run(["lake", "env", "lean", "--run", "ZkGadgets/Poseidon/CheckVectors.lean", str(vectors)],
                       cwd=ROOT / "lean", check=True, timeout=180)


if __name__ == "__main__":
    main()
