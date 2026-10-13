# Protocol root-closure pilot

`python3 scripts/protocol_pilot.py corpus/protocol/manifest.json` prints the
randomized 48-session schedule without inference. Six root families each have
three positive sessions and one certified-negative session in each arm. Both
arms use the same model and aggregate limits. Direct sessions may use Lean
`have`; the treatment is explicit recursive model calls.

Success requires checking the **original root after recomposition**. Solved
leaves never count as successes. Refutation requires a checked negation of the
whole root; a compiler error, timeout or failed search is not a refutation.

## Acceptance boundary

Live mode requires an existing Docker image supplied with `--docker-image`.
Missing images or unavailable Docker fail before inference; there is no automatic
fallback to unsandboxed execution. The image is resolved to an immutable ID and
recorded. The current validated image is `scribe:pilot-isolated` (derived from `scribe:cleanup-validated`).

The candidate runs as an unprivileged user in a container with networking off,
read-only root and dependencies, all capabilities dropped, no new privileges,
64-process/2-GiB/two-CPU limits and bounded writable tmpfs. Its only host mount
is its input source, read-only. A compiler exit code or printed audit message
cannot establish success: a fresh, bounded compiled artifact must be returned.

A fresh verifier container receives only that artifact and verifier source as
read-only inputs. It **does not import the candidate module or execute its
elaborator extensions/initializers**. It reads the compiled declarations as
data and replays them through Lean's kernel using `Lean.Environment.replay`
(the mechanism used by `leanchecker`). It then checks the root against the
frozen manifest proposition and traverses the actual declaration dependencies,
allowing only `propext`, `Classical.choice` and `Quot.sound` as axioms. Its receipt
is emitted by this trusted verifier after all checks, never by candidate code.
A fabricated artifact proving a different type or depending on a new axiom is
rejected. The trusted computing base includes the pinned image, Lean's kernel
and compiled-artifact reader, this verifier, and Docker isolation.

Model-generated leaf propositions are not inserted into trusted verifier source:
Lean type expressions can themselves contain metaprograms. Intermediate leaf
checks establish kernel validity and permitted axioms. Their declared types
are enforced when the complete proof is recomposed and checked against the
frozen original root. Leaf checks alone are not acceptance evidence.

Frozen targets must have no universe parameters, as in the current six-root
manifest. Universe-polymorphic targets are explicitly rejected by the verifier.

For reviewed local fixtures only, `--trusted-local-replay` permits host execution.
This explicit mode emits an artifact and separately compiles a frozen-type and
axiom check with `--trust=0`, but it is **not isolation** and must not be used for
untrusted Lean. It cannot enable live mode. Replay reports are non-empirical.

## Budgets and evidence

Defaults per session: six requests, 12,000 input-token reservation (including
512 for chat framing), 1,536 completion tokens/request, 180 seconds, depth two,
three children/split, one retry/node. Decomposition, failed calls, child proofs
and recomposition share the limits. Recomposition is supplied in the split
response; there is no free final model request.

Network calls run in killable workers; socket timeouts are not treated as total
deadlines. Every worker has an aggregate wall timeout and captured-output cap.
Docker containers are explicitly removed on timeout. Time is checked again
after inference and verification before accepting a result. Container cleanup
may add bounded shutdown overhead; it cannot turn an overdue proof into success.

Evidence records order/seed, requested and returned model identifiers, manifest
and environment hashes, pinned image ID, frozen statements, responses, usage,
conservative charge reservations, Lean inputs/logs and outcomes. Sessions reuse
no provider conversation. A fresh output directory is required.

Raw paired per-root counts are primary. Descriptive bootstrap intervals resample
six root-level differences, not correlated leaves or 36 independent problems.
These related lemmas are a small dependency family with Mathlib answers already
available; this is not a contamination-free benchmark. Positives use a generic
field and negatives specialize to `ZMod 5`, a difficulty confound. No result
establishes an RS proximity gap or broad protocol superiority.

## Validation without inference

The derived image grants read access to cached Lean files for the unprivileged
container user. Build it locally from the existing base image (no source context
is sent):

```sh
docker build --tag scribe:pilot-isolated - < benchmark/protocol-pilot/Dockerfile
```

```sh
python3 -m unittest discover -s scripts/tests -v
python3 scripts/validate_protocol_corpus.py
SCRIBE_PILOT_DOCKER_TESTS=1 python3 -m unittest discover -s scripts/tests -v
python3 scripts/protocol_pilot.py corpus/protocol/manifest.json --mode replay \
  --docker-image scribe:pilot-isolated \
  --replay benchmark/protocol-pilot/smoke-replay.json \
  --job 16-evaluation_unique-decomposition-positive-0 \
  --job 33-evaluation_unique-direct-negative-0 \
  --output .local/protocol-pilot-smoke
```

The Docker regressions reject the real early-exit bypass, a forged artifact with
the wrong proposition, and a forged artifact using a new axiom; they also accept
a good proof. Unit tests cover overdue provider/checker results, worker deadlines,
output bounds, shared budgets and root recomposition. Set `SCRIBE_PILOT_IMAGE`
to change the integration-test image. Tests do not make model calls.

Omit both `--job` flags for the full replay. Its hand-written proofs and redundant
one-child splits validate orchestration, never empirical model performance.
For reviewed host replay, replace `--docker-image ...` with
`--trusted-local-replay`. Missing replay responses are tool failures.

## Live run after agreeing a model and budget

Set `MODEL`, `INPUT_PRICE`, `OUTPUT_PRICE` and `SESSION_CAP` to the approved fixed
model, current USD-per-million-token prices, and per-session USD ceiling.
Supply `OPENAI_API_KEY` through the environment, not a command argument.

```sh
python3 scripts/protocol_pilot.py corpus/protocol/manifest.json --mode live \
  --docker-image scribe:pilot-isolated \
  --model "$MODEL" --input-price "$INPUT_PRICE" --output-price "$OUTPUT_PRICE" \
  --session-usd "$SESSION_CAP" --confirm-byte-token-bound \
  --output .local/protocol-pilot-live
```

Confirm that the provider honors `max_completion_tokens` including hidden
reasoning and tokenizes this single textual message using at most UTF-8 bytes
plus 512 framing tokens. No tools, multimodal inputs or server-side augmentation
are supported. Prices must cover every billable token category. Reservations
are conservative estimates, not measured billing; failed requests still consume
their reservation. At full defaults the bound is 3.456M input plus 442,368
completion tokens, or
`min(48 × SESSION_CAP, 3.456 × INPUT_PRICE + 0.442368 × OUTPUT_PRICE)` USD.
Plan mode accepts the same price arguments without contacting a provider.
No live inference has been run by these changes.
