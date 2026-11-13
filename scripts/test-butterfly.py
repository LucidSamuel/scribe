#!/usr/bin/env python3
"""Exercise the real Butterfly CLI and Lean checker (no model calls).

Build first: cargo build -p scribe-cli
Run: python3 scripts/test-butterfly.py
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=Path("target/debug/scribe"))
    parser.add_argument("--lake-dir", type=Path, default=Path("lean"))
    args = parser.parse_args()
    binary = str(args.binary.resolve())
    lake = str(args.lake_dir.resolve())
    with tempfile.TemporaryDirectory(prefix="butterfly-integration-") as tmp:
        root = Path(tmp)

        def run(command, output, *, candidate=None, lake_dir=lake, expect=0):
            cmd = [binary, "butterfly", command, "--output", str(output), "--lake-dir", lake_dir]
            if candidate is not None:
                source = output.with_suffix(".json")
                source.write_text(json.dumps(candidate))
                cmd += ["--candidate", str(source)]
            completed = subprocess.run(cmd, capture_output=True, text=True, timeout=1000)
            assert completed.returncode == expect, (cmd, completed.returncode, completed.stdout, completed.stderr)
            return json.loads((output / "report.json").read_text()), completed.stdout

        report, text = run("demo", root / "demo")
        assert len(report["cases"]) == 7, report
        assert report["checked_witnesses"] == 4, report
        assert report["safe_false_accusations"] == 0, report
        by_variant = {case["variant"]: case for case in report["cases"]}
        for variant in ["baseline", "boundary_strict", "unreachable_bonus"]:
            assert by_variant[variant]["verification_status"] == "checked_safe", by_variant[variant]
        for variant in ["boundary_relax", "guard_removed", "wrong_debit", "duplicate_credit"]:
            assert by_variant[variant]["verification_status"] == "checked_refutation", by_variant[variant]
        assert "baseline outcome at divergence:" in text
        assert "reserve | alice | bob | treasury | total" in text

        candidate = by_variant["boundary_relax"]["search"]["candidate"]
        checked, _ = run("verify", root / "recheck", candidate=candidate)
        assert checked["verification_status"] == "checked", checked
        # Bypass the Rust precheck and falsify the fixed Lean proposition itself.
        # Lean may still print the final #eval marker after an earlier error;
        # the process status must prevent that marker becoming acceptance.
        source = next((root / "recheck").rglob("Witness.lean")).read_text()
        old = " ≠ total initial"
        assert old in source, source
        altered = root / "FalseWitness.lean"
        altered.write_text(source.replace(old, " = total initial"))
        failed = subprocess.run(["lake", "env", "lean", str(altered)], cwd=lake,
                                capture_output=True, text=True, timeout=120)
        assert failed.returncode != 0, (failed.stdout, failed.stderr)

        for name in ["mutation", "action", "initial", "intermediate", "divergence"]:
            changed = copy.deepcopy(candidate)
            if name == "mutation":
                changed["variant"] = "baseline"
            elif name == "action":
                changed["actions"][-1]["amount"] = 0
            elif name == "initial":
                changed["states"][0]["reserve"] = 7
            elif name == "intermediate":
                changed["states"][1]["reserve"] = 8
            else:
                changed["baseline_divergence"] = 999
            rejected, _ = run("verify", root / name, candidate=changed, expect=3)
            assert rejected["verification_status"] == "rejected", rejected

        unavailable, _ = run("evaluate", root / "missing-lean", lake_dir=str(root / "absent"), expect=3)
        assert unavailable["checked_witnesses"] == 0, unavailable
        assert all(case["verification_status"] == "unavailable" for case in unavailable["cases"]), unavailable
        assert not list((root / "missing-lean").rglob("*.receipt.json"))
        print("PASS: seven checked cases, candidate recheck, Lean rejects false certificate, five tamper rejections, and missing-Lean failure")


if __name__ == "__main__":
    main()
