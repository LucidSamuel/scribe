#!/usr/bin/env python3
"""Kernel-check the fixed polynomial corpus; never score a failed build as refutation."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def validate(timeout=300):
    manifest_path = ROOT / "corpus/protocol/manifest.json"
    manifest = json.loads(manifest_path.read_text())
    try:
        build = subprocess.run(
            ["lake", "build", "ZkGadgets.Protocol.Mutations"], cwd=ROOT / "lean",
            capture_output=True, text=True, timeout=timeout,
        )
        if build.returncode:
            return {"status": "tooling_failure", "diagnostic": build.stdout + build.stderr}
        # Bind the machine-readable statements to the checked reference proofs.
        # Merely compiling a file containing a differently typed theorem is insufficient.
        source = "import ZkGadgets.Protocol.Mutations\nopen Polynomial\n"
        for index, row in enumerate(manifest["roots"]):
            source += f'theorem corpus_positive_{index} : {row["positive"]} := {row["validation"]["positive"]}\n'
            proposition = row["negative"].removeprefix(":").strip()
            source += f'theorem corpus_negative_{index} : ¬ ({proposition}) := {row["validation"]["negative_refutation"]}\n'
            source += f"#audit_axioms corpus_positive_{index}\n#audit_axioms corpus_negative_{index}\n"
        with tempfile.TemporaryDirectory(prefix="scribe-protocol-") as directory:
            path = Path(directory) / "Validate.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                                    capture_output=True, text=True, timeout=timeout)
        if result.returncode:
            return {"status": "tooling_failure", "diagnostic": result.stdout + result.stderr}
    except subprocess.TimeoutExpired:
        return {"status": "budget_exhaustion", "timeout_seconds": timeout}
    except OSError as exc:
        return {"status": "tooling_failure", "diagnostic": str(exc)}
    files = [Path(__file__).resolve(), manifest_path, ROOT / "lean/lean-toolchain", ROOT / "lean/lake-manifest.json",
             ROOT / "lean/ZkGadgets/Audit.lean",
             ROOT / "lean/ZkGadgets/Protocol/EvaluationUniqueness.lean",
             ROOT / "lean/ZkGadgets/Protocol/Mutations.lean"]
    return {"status": "kernel_checked", "corpus_version": manifest["version"],
            "positive_proofs": len(manifest["roots"]),
            "paired_refutations": len(manifest["roots"]),
            "additional_refutations": len(manifest["extra_negative_refutations"]),
            "scope": manifest["scope"],
            "measurement": "fixed reference evidence; no model success or detection-rate claim",
            "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = validate(args.timeout)
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    sys.exit(0 if report["status"] == "kernel_checked" else 1)
