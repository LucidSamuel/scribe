#!/usr/bin/env python3
"""Small, budgeted root-closure experiment. Standard library only; no calls by default."""
import argparse
import hashlib
import json
import os
import signal
import sys
import math
import tempfile
import uuid
import base64
import selectors
import random
import subprocess
import time
import urllib.request
from pathlib import Path

ARMS = ("direct", "decomposition")
DEFAULT_LIMITS = dict(calls=6, input_bytes=12000, output_tokens=1536,
                      seconds=180, retries=1, depth=2, children=3)


def digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


def load_manifest(path):
    data = json.loads(Path(path).read_text())
    data.setdefault("limits", DEFAULT_LIMITS.copy())
    roots = data["roots"]
    if len(roots) != 6 or len({r["id"] for r in roots}) != 6:
        raise ValueError("pilot requires exactly six distinct roots")
    for root in roots:
        for key in ("id", "prefix", "positive", "negative", "leakage", "validation"):
            if not root.get(key):
                raise ValueError(f"{root.get('id')}: missing {key}")
    return data


def schedule(manifest, seed):
    jobs = []
    for root in manifest["roots"]:
        for arm in ARMS:
            for polarity, count in (("positive", 3), ("negative", 1)):
                for repetition in range(count):
                    jobs.append({"root": root["id"], "arm": arm,
                                 "polarity": polarity, "repetition": repetition})
    random.Random(seed).shuffle(jobs)
    for index, job in enumerate(jobs):
        job["id"] = f"{index:02d}-{job['root']}-{job['arm']}-{job['polarity']}-{job['repetition']}"
    return jobs


def source(prefix, statement, proof, refutation=False):
    proposition = f"¬ ({statement})" if refutation else statement
    # Header and proposition are fixed by the manifest; only the proof is generated.
    return ("import ZkGadgets.Audit\n" + prefix + "\n" +
            "set_option maxRecDepth 2048\n" +
            "theorem pilot_root :\n" + indent(proposition) + " :=\n" + indent(proof) +
            "\n#audit_axioms pilot_root\n#print axioms pilot_root\n")


def indent(text):
    return "\n".join("  " + line for line in text.splitlines())


class BudgetExceeded(Exception):
    pass


class Budget:
    def __init__(self, limits):
        self.limits = limits
        self.calls = 0
        self.reserved_usd = 0.0
        self.started = time.monotonic()

    def remaining_seconds(self):
        return self.limits["seconds"] - (time.monotonic() - self.started)

    def reserve(self, prompt):
        l = self.limits
        if len(prompt.encode()) + 512 > l["input_bytes"]:
            raise BudgetExceeded("input byte cap")
        # Reserve the maximum input/output charge BEFORE dispatch, including failures.
        # Live mode is restricted to providers whose input tokenizer emits <= UTF-8 bytes.
        charge = (l["input_bytes"] * l["input_usd_per_million"] +
                  l["output_tokens"] * l["output_usd_per_million"]) / 1e6
        if (self.calls >= l["calls"] or self.remaining_seconds() <= 0 or
                self.reserved_usd + charge > l["usd"] + 1e-12):
            raise BudgetExceeded("aggregate session cap")
        self.calls += 1
        self.reserved_usd += charge


def run_process(argv, timeout, *, cwd=None, env=None, input_text=None, output_limit=48 * 1024 * 1024):
    """Bound wall time and captured bytes; kill the complete worker process group."""
    if timeout <= 0:
        raise BudgetExceeded("wall deadline before worker dispatch")
    deadline = time.monotonic() + timeout
    with tempfile.TemporaryFile() as request:
        if input_text:
            request.write(input_text.encode())
            request.seek(0)
        with subprocess.Popen(argv, cwd=cwd, env=env, stdin=request,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              start_new_session=True) as process, selectors.DefaultSelector() as selector:
            streams = {process.stdout: bytearray(), process.stderr: bytearray()}
            for stream in streams:
                selector.register(stream, selectors.EVENT_READ)
            size = 0
            try:
                while selector.get_map():
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise BudgetExceeded("worker exceeded aggregate wall deadline")
                    for key, _ in selector.select(remaining):
                        chunk = os.read(key.fileobj.fileno(), 65536)
                        if not chunk:
                            selector.unregister(key.fileobj)
                            continue
                        size += len(chunk)
                        if size > output_limit:
                            raise BudgetExceeded("worker output byte cap")
                        streams[key.fileobj].extend(chunk)
                process.wait(timeout=max(0, deadline - time.monotonic()))
                if time.monotonic() >= deadline:
                    raise BudgetExceeded("worker completed after aggregate wall deadline")
            except BaseException as error:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                if isinstance(error, subprocess.TimeoutExpired):
                    raise BudgetExceeded("worker exceeded aggregate wall deadline") from error
                raise
            return (process.returncode, streams[process.stdout].decode(errors="replace"),
                    streams[process.stderr].decode(errors="replace"))


class OpenAIChat:
    def __init__(self, model, key, endpoint, limits):
        self.model, self.key, self.endpoint, self.limits = model, key, endpoint, limits

    def __call__(self, prompt, timeout):
        # Socket timeouts alone do not bound DNS, TLS and a trickling response.
        # Credentials travel through stdin, never argv or retained files.
        request = dict(model=self.model, key=self.key, endpoint=self.endpoint,
                       output_tokens=self.limits["output_tokens"], prompt=prompt)
        code, stdout, stderr = run_process(
            [sys.executable, str(Path(__file__).resolve()), "--http-worker"], timeout,
            input_text=json.dumps(request))
        if code:
            raise RuntimeError("HTTP worker failed: " + stderr[-1000:])
        return json.loads(stdout)


def http_worker():
    args = json.load(sys.stdin)
    payload = {"model": args["model"], "messages": [{"role": "user", "content": args["prompt"]}],
               "max_completion_tokens": args["output_tokens"]}
    request = urllib.request.Request(args["endpoint"], json.dumps(payload).encode(),
                                     {"Authorization": "Bearer " + args["key"],
                                      "Content-Type": "application/json"})
    with urllib.request.urlopen(request) as response:
        result = json.loads(response.read(1_000_000))
    usage = dict(result.get("usage") or {}, response_model=result.get("model"),
                 system_fingerprint=result.get("system_fingerprint"), request_id=result.get("id"))
    print(json.dumps([result["choices"][0]["message"]["content"], usage]))


class Replay:
    def __init__(self, responses):
        self.responses = iter(responses)

    def __call__(self, prompt, timeout):
        del prompt, timeout
        response = next(self.responses)
        return json.dumps(response), {}


def replay_responses(replays, job, root):
    if "fixtures" not in replays:
        return replays.get(job["id"], [])
    fixture = replays["fixtures"].get(root["id"], {})
    required = "refutation" if job["polarity"] == "negative" else "proof"
    if required not in fixture:
        return []
    if job["polarity"] == "negative":
        return [{"refutation": fixture["refutation"]}]
    answer = {"proof": fixture["proof"]}
    if job["arm"] == "direct":
        return [answer]
    return [{"children": [{"statement": root["positive"]}], "proof": "by exact @leaf_0"}, answer]


class IsolationUnavailable(RuntimeError):
    pass


def verifier_source(prefix, proposition):
    # Candidate module is deliberately NOT imported: importing it could replay
    # elaborator extensions/initializers. Only its kernel declarations are read.
    text = ("import ZkGadgets.Audit\nimport Lean.Replay\n" + prefix +
            "\ndef frozenTarget : Prop :=\n" + indent(proposition or "True") + "\n" +
            r"""open Lean Elab Command
unsafe def validateCandidate : CommandElabM Unit := do
  let parts ← readModuleDataParts #["/candidate/Candidate.olean"]
  let some (mod, _) := parts[0]? | throwError "empty candidate artifact"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for n in mod.constNames, ci in mod.constants do
    constants := constants.insert n ci
  let checked ← (← getEnv).replay constants
  let some root := checked.toKernelEnv.find? `pilot_root | throwError "missing pilot_root"
  match root with
  | .thmInfo _ => pure ()
  | _ => throwError "pilot_root is not a theorem"
  let some target := checked.toKernelEnv.find? `frozenTarget | throwError "missing frozen target"
  unless target.levelParams.isEmpty do
    throwError "universe-polymorphic targets are unsupported by this pilot"
  let declaration := Declaration.thmDecl {
    name := `independently_verified_root
    levelParams := []
    type := mkConst `frozenTarget
    value := mkConst `pilot_root (root.levelParams.map (fun _ => Level.zero))
  }
  let checked ← match checked.addDeclCore 0 declaration none with
    | .ok env => pure env
    | .error _ => throwError "candidate does not prove frozen proposition"
  let mut pending := [`independently_verified_root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := checked.toKernelEnv.find? n | throwError "missing dependency {n}"
    if let .axiomInfo _ := ci then
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throwError "untrusted axiom {n}"
    for dependency in ci.getUsedConstantsAsSet do
      pending := dependency :: pending
  IO.println "SCRIBE_KERNEL_REPLAY_ACCEPTED"

run_cmd validateCandidate
""")
    if proposition is None:
        start = text.index("  let some target :=")
        end = text.index("  let mut pending :=", start)
        text = text[:start] + text[end:]
        text = text.replace("let mut pending := [`independently_verified_root]", "let mut pending := [`pilot_root]")
    return text


def docker_image_id(image):
    code, stdout, stderr = run_process(
        ["docker", "image", "inspect", image, "--format", "{{.Id}}"], 15)
    resolved = stdout.strip()
    if code or not resolved.startswith("sha256:"):
        raise IsolationUnavailable("Pinned Docker image unavailable: " + stderr[-1000:])
    return resolved


def container_run(image, mounts, command, timeout):
    name = "scribe-pilot-" + uuid.uuid4().hex
    argv = ["docker", "run", "--rm", "--pull", "never", "--name", name,
            "--network", "none", "--read-only", "--user", "65534:65534",
            "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
            "--env", "GIT_CONFIG_COUNT=1", "--env", "GIT_CONFIG_KEY_0=safe.directory",
            "--env", "GIT_CONFIG_VALUE_0=*",
            "--pids-limit", "64", "--memory", "2g", "--cpus", "2",
            "--tmpfs", "/tmp:rw,nosuid,nodev,noexec,size=64m",
            "--tmpfs", "/work:rw,nosuid,nodev,noexec,size=64m,mode=1777",
            "--workdir", "/opt/lean-project"]
    for source_dir, destination, readonly in mounts:
        mount = f"type=bind,src={source_dir.resolve()},dst={destination}"
        argv += ["--mount", mount + (",readonly" if readonly else "")]
    try:
        result = run_process(argv + [image] + command, timeout)
        if result[0] in (125, 126, 127):
            raise IsolationUnavailable("Container failed to start: " + result[2][-1000:])
        if result[0] == 137:
            raise BudgetExceeded("Container terminated by resource limit or kill signal")
        return result
    finally:
        # Killing the Docker client alone does not stop the container worker.
        code, _, error = run_process(["docker", "rm", "--force", name], 10)
        if code and "No such container" not in error:
            raise IsolationUnavailable("Could not confirm container cleanup: " + error[-1000:])


def docker_checker(image, evidence):
    def check(prefix, statement, proof, refutation, timeout, *, trusted_statement=True):
        deadline = time.monotonic() + timeout
        text = source(prefix, statement, proof, refutation)
        evidence_file = evidence / ("check-" + digest(text))
        evidence_file.with_suffix(".lean").write_text(text)
        with tempfile.TemporaryDirectory(prefix="scribe-candidate-") as temporary:
            root = Path(temporary)
            root.chmod(0o755)
            candidate, artifact, verifier = [root / n for n in ("candidate", "artifact", "verifier")]
            for directory in (candidate, artifact, verifier):
                directory.mkdir(mode=0o777)
                directory.chmod(0o755)
            (candidate / "Candidate.lean").write_text(text)
            # The candidate has no writable host mount. Its output lives in a
            # bounded tmpfs and crosses the boundary as bounded artifact bytes.
            wrapper = ("lake env lean --root=/input -o /work/Candidate.olean /input/Candidate.lean "
                       ">/work/compile.log 2>&1; code=$?; "
                       "if [ \"$code\" -eq 0 ] && [ -f /work/Candidate.olean ] "
                       "&& [ ! -L /work/Candidate.olean ] "
                       "&& [ \"$(stat -c %s /work/Candidate.olean)\" -le 33554432 ]; then "
                       "base64 /work/Candidate.olean; else tail -c 6000 /work/compile.log >&2; exit 1; fi")
            code, stdout, stderr = container_run(image, [(candidate, "/input", True)],
                ["sh", "-c", wrapper], deadline - time.monotonic())
            evidence_file.with_suffix(".candidate.log").write_text(stderr)
            if code:
                return False, stderr[-6000:] + "\nNo regular compiled candidate artifact."
            try:
                payload = base64.b64decode("".join(stdout.split()), validate=True)
            except ValueError:
                return False, "Candidate returned malformed artifact encoding."
            if len(payload) > 32 * 1024 * 1024:
                return False, "Candidate artifact exceeds byte cap."
            (artifact / "Candidate.olean").write_bytes(payload)
            proposition = f"¬ ({statement})" if refutation else statement
            trusted_source = verifier_source(prefix, proposition if trusted_statement else None)
            (verifier / "Verify.lean").write_text(trusted_source)
            evidence_file.with_suffix(".verifier.lean").write_text(trusted_source)
            code, stdout, stderr = container_run(image,
                [(artifact, "/candidate", True), (verifier, "/verifier", True)],
                ["lake", "env", "lean", "/verifier/Verify.lean"], deadline - time.monotonic())
            evidence_file.with_suffix(".verifier.log").write_text(stdout + stderr)
            passed = code == 0 and "SCRIBE_KERNEL_REPLAY_ACCEPTED" in stdout.splitlines()
            return passed, (stdout + stderr)[-6000:]
    return check


def lean_checker(lake_dir, evidence, *, trusted_local_replay=False):
    if not trusted_local_replay:
        raise IsolationUnavailable("Untrusted Lean execution is disabled: an isolated candidate "
                                   "worker and protected independent verifier are not configured")

    def check(prefix, statement, proof, refutation, timeout, *, trusted_statement=True):
        deadline = time.monotonic() + timeout
        proposition = f"¬ ({statement})" if refutation else statement
        text = source(prefix, statement, proof, refutation)
        module = "Candidate_" + digest(text)
        path = evidence / (module + ".lean")
        artifact = path.with_suffix(".olean")
        verified = evidence / ("Verified_" + digest(text) + ".lean")
        verified_artifact = verified.with_suffix(".olean")
        path.write_text(text)
        for stale in (artifact, verified_artifact):
            stale.unlink(missing_ok=True)
        env = os.environ.copy()
        env["LEAN_PATH"] = str(evidence.resolve()) + os.pathsep + env.get("LEAN_PATH", "")

        def compile_file(input_path, output_path, trust=False):
            argv = ["lake", "env", "lean", "--root=" + str(evidence.resolve())]
            if trust:
                argv.append("--trust=0")
            argv += ["-o", str(output_path.resolve()), str(input_path.resolve())]
            code, stdout, stderr = run_process(argv, deadline - time.monotonic(),
                                               cwd=lake_dir, env=env)
            output = stdout + stderr
            input_path.with_suffix(".log").write_text(output)
            # An early exit, including an exit that prints a forged audit message,
            # cannot substitute for a newly emitted compiled declaration artifact.
            return code == 0 and output_path.is_file(), output

        passed, output = compile_file(path, artifact)
        if not passed:
            return False, output[-6000:] + "\nCandidate did not produce a checked artifact."
        # Write this fixed verifier AFTER candidate execution. It checks the exact
        # original proposition, rechecks imported declarations and audits axioms.
        # This is defense in depth for TRUSTED replay, not filesystem isolation.
        verified.write_text(f"import {module}\nimport ZkGadgets.Audit\n" + prefix +
                            "\ntheorem independently_verified_root :\n" + indent(proposition) +
                            " := @pilot_root\n#audit_axioms independently_verified_root\n")
        passed, verification_output = compile_file(verified, verified_artifact, trust=True)
        return passed, verification_output[-6000:]
    return check


def run_session(root, job, limits, provider, checker, evidence):
    budget = Budget(limits)
    events = []
    statement = root[job["polarity"]]
    root_closed = False
    outcome = "stalled"
    failure = None

    def solve(proposition, depth=0):
        nonlocal root_closed
        feedback = ""
        for attempt in range(limits["retries"] + 1):
            if budget.remaining_seconds() <= 0:
                raise BudgetExceeded("wall clock")
            splitting = job["arm"] == "decomposition" and depth < limits["depth"]
            prompt = (
                "Return JSON only. Prove the fixed Lean proposition or refute it. "
                'Use {"proof":"by ..."} or {"refutation":"by ..."}. '
                "A refutation must prove the negation of the whole proposition. "
                + (f'Or return {{"children":[{{"statement":"..."}}],"proof":"by ..."}} '
                   f"with at most {limits['children']} independently provable children. "
                   "Recomposition proof may use local have declarations named leaf_0, leaf_1, etc. "
                   if splitting else "Do not split into children. ") +
                "Never use sorry, custom axioms or native_decide.\n" +
                "Context:\nimport ZkGadgets.Audit\n" + root["prefix"] +
                "\nFixed proposition:\n" + proposition + "\nPrevious feedback:\n" + feedback)
            budget.reserve(prompt)
            text, usage = provider(prompt, budget.remaining_seconds())
            if budget.remaining_seconds() <= 0:
                raise BudgetExceeded("provider completed after session deadline")
            event = {"depth": depth, "attempt": attempt, "prompt_sha256": digest(prompt),
                     "response": text, "usage": usage}
            events.append(event)
            try:
                answer = json.loads(text)
                if not isinstance(answer, dict):
                    raise ValueError("response must be object")
                refutation = "refutation" in answer
                proof = answer.get("refutation" if refutation else "proof")
                if not isinstance(proof, str) or not proof.strip():
                    raise ValueError("missing proof")
                children = answer.get("children", [])
                if children:
                    if refutation or not splitting or len(children) > limits["children"]:
                        raise ValueError("illegal decomposition")
                    child_proofs = []
                    for index, child in enumerate(children):
                        child_statement = child["statement"]
                        if not isinstance(child_statement, str) or not child_statement.strip():
                            raise ValueError("empty child statement")
                        child_proof, child_refuted = solve(child_statement, depth + 1)
                        if child_proof is None or child_refuted:
                            raise ValueError("child failed; root remains open")
                        child_proofs.append(f"have leaf_{index} :\n{indent(child_statement)} :=\n{indent(child_proof)}")
                    proof = "by\n" + "\n".join(indent(p) for p in child_proofs) + "\n  exact (\n" + indent(indent(proof)) + "\n  )"
                passed, feedback = checker(root["prefix"], proposition, proof, refutation,
                                           budget.remaining_seconds(), trusted_statement=depth == 0)
                if budget.remaining_seconds() <= 0:
                    raise BudgetExceeded("checker completed after session deadline")
                event["kernel_passed"] = passed
                event["refutation"] = refutation
                event["feedback"] = feedback
                if passed:
                    if depth == 0:
                        root_closed = not refutation
                    return proof, refutation
            except (ValueError, KeyError, TypeError) as error:
                feedback = str(error)
                event["feedback"] = feedback
        return None, False

    try:
        proof, refuted = solve(statement)
        if budget.remaining_seconds() <= 0:
            root_closed = False
            raise BudgetExceeded("session completed after deadline")
        if proof is not None:
            outcome = "checked_refutation" if refuted else "root_closed"
    except BudgetExceeded as error:
        outcome, failure = "budget_exhausted", str(error)
    except Exception as error:
        outcome, failure = "tool_failure", f"{type(error).__name__}: {error}"
    result = dict(job, outcome=outcome, root_closed=root_closed,
                  calls=budget.calls, reserved_usd=budget.reserved_usd,
                  seconds=time.monotonic() - budget.started, failure=failure,
                  statement_sha256=digest(statement), leakage=root["leakage"], events=events)
    (evidence / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def report(results):
    # Paired root-level bootstrap; leaves and repeated sessions are not independent roots.
    roots = sorted({r["root"] for r in results})
    pairs = []
    rows = []
    for root in roots:
        row = {"root": root}
        for arm in ARMS:
            positive = [r for r in results if r["root"] == root and r["arm"] == arm and r["polarity"] == "positive"]
            row[arm] = {"closed": sum(r["outcome"] == "root_closed" for r in positive), "n": len(positive)}
        if all(row[a]["n"] == 3 for a in ARMS):
            pairs.append(row["decomposition"]["closed"] / 3 - row["direct"]["closed"] / 3)
        rows.append(row)
    ci = None
    if len(pairs) == 6:
        rng = random.Random(20261009)
        values = sorted(sum(rng.choices(pairs, k=6)) / 6 for _ in range(10000))
        ci = {"mean_difference": sum(pairs) / 6, "bootstrap_95_percent": [values[249], values[9749]],
              "warning": "Descriptive only: six related roots, not an independent representative protocol sample."}
    by_arm = {}
    for arm in ARMS:
        arm_results = [r for r in results if r["arm"] == arm]
        positives = [r for r in arm_results if r["polarity"] == "positive"]
        negatives = [r for r in arm_results if r["polarity"] == "negative"]
        by_arm[arm] = {
            "positive_sessions": len(positives),
            "positive_root_closures": sum(r["outcome"] == "root_closed" for r in positives),
            "negative_sessions": len(negatives),
            "checked_negative_refutations": sum(r["outcome"] == "checked_refutation" for r in negatives),
            "calls": sum(r["calls"] for r in arm_results),
            "seconds": sum(r["seconds"] for r in arm_results)}
    return {"sessions": len(results), "roots": rows, "by_arm": by_arm, "paired_root_uncertainty": ci,
            "negative_refutations": sum(r["polarity"] == "negative" and r["outcome"] == "checked_refutation" for r in results),
            "negative_false_acceptances": sum(r["polarity"] == "negative" and r["outcome"] == "root_closed" for r in results),
            "positive_refutations": sum(r["polarity"] == "positive" and r["outcome"] == "checked_refutation" for r in results),
            "outcomes": {o: sum(r["outcome"] == o for r in results) for o in ("root_closed", "checked_refutation", "stalled", "budget_exhausted", "tool_failure")},
            "reserved_usd": sum(r["reserved_usd"] for r in results),
            "seconds": sum(r["seconds"] for r in results),
            "reported_prompt_tokens": sum(e.get("usage", {}).get("prompt_tokens", 0) for r in results for e in r["events"]),
            "reported_completion_tokens": sum(e.get("usage", {}).get("completion_tokens", 0) for r in results for e in r["events"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest")
    parser.add_argument("--mode", choices=("plan", "replay", "live"), default="plan")
    parser.add_argument("--output", default=".local/protocol-pilot")
    parser.add_argument("--lake-dir", default="lean")
    parser.add_argument("--replay", help="JSON mapping job IDs to response arrays")
    parser.add_argument("--model")
    parser.add_argument("--docker-image", help="Existing pinned Scribe image; required for untrusted/live proofs")
    parser.add_argument("--trusted-local-replay", action="store_true",
                        help="Acknowledge replay Lean is trusted local code, not sandboxed")
    parser.add_argument("--job", action="append", help="Run only this job ID; report remains explicitly partial")
    parser.add_argument("--endpoint", default="https://api.openai.com/v1/chat/completions")
    parser.add_argument("--input-price", type=float, default=0)
    parser.add_argument("--output-price", type=float, default=0)
    parser.add_argument("--session-usd", type=float, default=0)
    parser.add_argument("--seed", type=int, default=20261009)
    parser.add_argument("--confirm-byte-token-bound", action="store_true",
                        help="Confirm selected model uses <= UTF-8 bytes + 512 input tokens and honors completion cap")
    args = parser.parse_args()
    if args.mode == "live" and not args.docker_image:
        parser.error("Live mode requires --docker-image for isolated candidate execution "
                     "and independent kernel replay. No provider call was made.")
    if args.mode == "replay" and not args.trusted_local_replay and not args.docker_image:
        parser.error("Replay executes trusted local Lean code; pass --trusted-local-replay "
                     "only for reviewed fixtures. Untrusted replay is disabled.")
    manifest = load_manifest(args.manifest)
    limits = dict(manifest["limits"], input_usd_per_million=args.input_price,
                  output_usd_per_million=args.output_price, usd=args.session_usd)
    for key in ("calls", "input_bytes", "output_tokens", "seconds", "children"):
        if not math.isfinite(limits[key]) or limits[key] <= 0:
            parser.error(f"{key} must be positive")
    if limits["depth"] < 0 or limits["retries"] < 0:
        parser.error("depth/retries cannot be negative")
    if any(not math.isfinite(v) or v < 0 for v in (args.input_price, args.output_price, args.session_usd)):
        parser.error("prices and budget cannot be negative")
    jobs = schedule(manifest, args.seed)
    if args.job:
        known = {j["id"] for j in jobs}
        if not set(args.job) <= known:
            parser.error("unknown --job ID; inspect plan first")
        jobs = [j for j in jobs if j["id"] in args.job]
    plan = {"model": args.model, "mode": args.mode, "seed": args.seed, "limits": limits,
            "manifest_sha256": digest(Path(args.manifest).read_text()), "jobs": jobs,
            "full_pilot_sessions": 48, "selected_sessions": len(jobs),
            "maximum_reserved_usd": len(jobs) * min(limits["usd"], limits["calls"] *
                (limits["input_bytes"] * args.input_price + limits["output_tokens"] * args.output_price) / 1e6)}
    if args.mode == "plan":
        print(json.dumps(plan, indent=2))
        return
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    if (output / "plan.json").exists():
        parser.error("output already has a plan; use a fresh directory to preserve evidence")
    if args.mode == "live":
        if not args.confirm_byte_token_bound:
            parser.error("live requires --confirm-byte-token-bound; unsupported tokenizers/providers cannot be budgeted safely")
        if not args.model or args.input_price <= 0 or args.output_price <= 0 or args.session_usd <= 0:
            parser.error("live requires model, current positive token prices and explicit per-session USD cap")
        provider = OpenAIChat(args.model, os.environ["OPENAI_API_KEY"], args.endpoint, limits)
    else:
        if not args.replay:
            parser.error("replay requires --replay")
        replays = json.loads(Path(args.replay).read_text())
    isolated_image = docker_image_id(args.docker_image) if args.docker_image else None
    plan["isolation"] = {"image_id": isolated_image, "trusted_local_replay": not bool(isolated_image)}
    def checker_for(directory):
        return docker_checker(isolated_image, directory) if isolated_image else lean_checker(
            args.lake_dir, directory, trusted_local_replay=True)
    plan["environment"] = {}
    for path in (Path(args.lake_dir) / "lean-toolchain", Path(args.lake_dir) / "lake-manifest.json",
                 Path(args.lake_dir) / "ZkGadgets/Audit.lean", Path(__file__)):
        plan["environment"][str(path)] = digest(path.read_text())
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (output / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    # Fail before any inference if the fixed imports or axiom checker do not compile.
    checked_prefixes = set()
    for root in manifest["roots"]:
        if root["prefix"] in checked_prefixes:
            continue
        checked_prefixes.add(root["prefix"])
        preflight = output / ("preflight-" + root["id"])
        preflight.mkdir()
        valid, feedback = checker_for(preflight)(root["prefix"], "True", "by trivial", False, 120)
        if not valid:
            raise RuntimeError("Lean preflight failed: " + feedback)
    roots = {r["id"]: r for r in manifest["roots"]}
    results = []
    for job in jobs:
        evidence = output / job["id"]
        evidence.mkdir()
        selected_provider = provider if args.mode == "live" else Replay(replay_responses(replays, job, roots[job["root"]]))
        results.append(run_session(roots[job["root"]], job, limits, selected_provider,
                                   checker_for(evidence), evidence))
        summary = dict(report(results), mode=args.mode, empirical=args.mode == "live",
                       complete_pilot=len(results) == 48, full_pilot_sessions=48)
        if args.mode == "replay":
            summary["paired_root_uncertainty"] = None
        (output / "report.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(job["id"], results[-1]["outcome"], flush=True)


if __name__ == "__main__":
    if sys.argv[1:] == ["--http-worker"]:
        http_worker()
    else:
        main()
