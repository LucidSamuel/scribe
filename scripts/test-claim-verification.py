#!/usr/bin/env python3
"""Exercise the real CLI and Lean kernel. Run after cargo build -p scribe-cli."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

repo = Path(__file__).resolve().parents[1]
lake = repo / "lean"
bench = lake / "ZkGadgets/Bench"
bench.mkdir(parents=True, exist_ok=True)
binary = repo / "target/debug/scribe"

with tempfile.TemporaryDirectory(prefix="ClaimRegression", dir=bench) as temporary:
    directory = Path(temporary)
    proof = directory / "Proof.lean"
    proof.write_text(
        "theorem claim_good : 1 + 1 = 2 := rfl\n"
        "theorem claim_bad : False := by sorry\n"
        "theorem claim_transitive : False := claim_bad\n"
    )
    package = {
        "schema_version": 1,
        "claim_id": "regression",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=repo, text=True
        ).strip(),
        "toolchain": (lake / "lean-toolchain").read_text().strip(),
        "parameters": {},
        "artifacts": {
            "proof": {
                "path": str(proof.relative_to(repo)),
                "sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
            }
        },
        "propositions": [{
            "declaration": "claim_good",
            "statement": "1 + 1 = 2",
            "artifact_id": "proof",
            "trust": "kernel",
            "axioms": [],
        }],
        "heuristics": [],
        "cost_ledger": [],
    }

    def check(label, mutate, expected_error=None):
        candidate = json.loads(json.dumps(package))
        mutate(candidate)
        path = directory / "package.json"
        path.write_text(json.dumps(candidate))
        result = subprocess.run(
            [str(binary), "claim", "verify", "--package", str(path),
             "--root", str(repo), "--lake-dir", str(lake)],
            cwd=repo, text=True, capture_output=True, timeout=120,
        )
        if expected_error is None:
            assert result.returncode == 0, result.stderr
            receipt = json.loads(result.stdout)
            assert receipt["verification"]["declarations"] == ["claim_good"]
            assert receipt["verification"]["kind"] == "lean_statement_and_axiom_check_v1"
        else:
            assert result.returncode == 3, (label, result.stdout, result.stderr)
            assert not result.stdout, (label, result.stdout)
            assert expected_error in result.stderr, (label, result.stderr)
        print(f"PASS {label}", flush=True)

    check("valid theorem binding", lambda p: None)
    check("wrong statement", lambda p: p["propositions"][0].update(statement="False"),
          "does not match theorem type")
    check("missing declaration", lambda p: p["propositions"][0].update(declaration="missing_claim"),
          "Unknown constant")
    check("axiom declaration mismatch",
          lambda p: p["propositions"][0].update(axioms=["Classical.choice"]),
          "declared axioms do not match")
    check("transitive sorry",
          lambda p: p["propositions"][0].update(declaration="claim_transitive", statement="False"),
          "untrusted axioms")
    check("statement command injection",
          lambda p: p["propositions"][0].update(statement="True\ntheorem injected : True := by trivial"),
          "invalid claim statement")
    check("changed proof hash",
          lambda p: p["artifacts"]["proof"].update(sha256="0" * 64),
          "SHA-256 mismatch")
    check("native trust rejected",
          lambda p: p["propositions"][0].update(trust="native_decide"),
          "native_decide claims are not supported")
    check("toolchain mismatch",
          lambda p: p.update(toolchain="another-toolchain"),
          "package toolchain must equal")
