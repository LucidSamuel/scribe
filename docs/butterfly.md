# Butterfly: a changed rule and a checked counterexample

Butterfly is Scribe's finite resource-trading demonstration. It searches typed
rule variants, then asks Lean to check the concrete trace independently of the
Rust search. It uses no model service or API key.

```sh
cargo run -p scribe-cli -- butterfly demo --output /tmp/butterfly-demo
cargo run -p scribe-cli -- butterfly evaluate --output /tmp/butterfly-evaluation
```

Run from the repository root with the repository's Lean/Lake toolchain and
dependencies installed. `--lake-dir` selects the trusted local Lean project.
The output directory must not already exist: old verification evidence must not
be mistaken for a new result. Each run writes `report.json`, `summary.txt`, a self-contained `report.html`,
and the checker evidence. Open `report.html` locally to compare the original and
mutant rules, inspect the trace and baseline divergence, and follow evidence links.
The report uses no remote assets or scripts. `demo` includes candidate states and actions in the terminal;
`evaluate` prints a compact per-variant summary. Both run the same seven variants.

Search limits are per variant: `--max-depth 6 --max-nodes 20000 --max-edges 500000
--seconds 10`. `--check-seconds 120` separately bounds each Lean verification.
A completed evaluation command is not a safety verdict; read each case's verdict.

## The model

The state contains a reserve, Alice's holdings, Bob's holdings, and a treasury.
Initially the reserve holds eight units and the other accounts are empty. Each
account is capped at eight units. The invariant counts all four accounts:

`reserve + alice + bob + treasury = 8`.

Issuance moves units from the reserve to a player. Trading transfers a positive
amount to the other player and charges a one-unit fee into the treasury. Thus
issuance and fees are accounted for explicitly; neither secretly creates or
destroys resources. The action alphabet has two accounts, issue/trade operations,
and amounts one through eight.

The baseline trade guard is `amount < balance`. This guarantees enough funds for
both the transfer and the fee. Lean natural subtraction truncates at zero, so
relaxing the guard to `amount ≤ balance` allows a trade that credits the recipient
and treasury without fully debiting the sender. This is a deliberate model of
a boundary-sensitive rule, not a claim that every strict-to-nonstrict edit is a bug.

| Variant | Single rule change | Evaluation class |
| --- | --- | --- |
| `baseline` | None | Safe control |
| `boundary_relax` | Trade guard `<` becomes `≤` | Harmful |
| `guard_removed` | Trade affordability guard becomes true | Harmful |
| `wrong_debit` | Debit `amount + 1` becomes `amount` | Harmful |
| `duplicate_credit` | Recipient credit `amount` becomes `2 × amount` | Harmful |
| `boundary_strict` | Trade guard becomes `amount + 1 < balance` | Safe control |
| `unreachable_bonus` | Double credit only for `amount > 8` | Unreachable fault |

Each mutation is one typed rule-site replacement, not necessarily one AST node
edit. These are fixed semantic variants, not a general-purpose AST mutation
engine. The Lean model proves baseline conservation for every accepted trace,
not just the traces visited by search. The fixed cap keeps the demonstration's
search space finite. Results concern this model, not a real deployed economy.

## What evidence means

Rust breadth-first search is an untrusted candidate producer. A candidate includes
the mutation ID, actions, every state including the initial state, and the first
action at which the baseline rejects the transition or produces a different state.
The checker must bind all these fields to the fixed Lean model and verify that
the final total differs from eight. Mutation labels and expected corpus classes
cannot turn a candidate into a checked result.

Lean checks fixed generated propositions over typed values, using the trusted
local model. The interface does not accept arbitrary proof text or Lean source
from a model or an uploaded package. Verification is local trusted-code execution;
it is not the protocol pilot's isolated executor for untrusted generated Lean.

Keep these claims separate:

- **Candidate found:** the Rust search reports a violating trace.
- **Checked counterexample:** the independent Lean check accepts the exact
  mutation, trace, baseline divergence, and invariant violation.
- **No witness found:** unknown within the reported search bounds. A depth limit,
  timeout, or even Rust's finite-frontier exhaustion is not a kernel proof of safety.
- **Baseline conservation:** the separately checked general Lean theorem.
- **Checked safe control:** an independent universal conservation theorem for
  `baseline`, `boundary_strict`, or `unreachable_bonus`. `checked_safe` comes
  from checking that theorem, never from failing to find an exploit.

The report records search work and verdicts. Checked witness yield is measured
against the four planted harmful variants. The three safe controls can be
accepted only by the separate general theorem checks. A checked accusation against a safe
control is an alarm requiring investigation. The unreachable-fault control checks
whether the harness confuses a suspicious rule with a reachable exploit.

Breadth-first ordering can supply an algorithmic observation about trace length
within this action alphabet. The witness theorem does not certify shortestness,
global minimality of the rule change, or empirical discovery power beyond these
hand-designed examples. There is no promised five-step exploit.

Each discovered candidate is also exported as `candidates/<variant>.json`,
including candidates whose verification fails. Its presence alone is not proof;
consult the recorded verification status. Recheck the boundary candidate with:

```sh
cargo run -p scribe-cli -- butterfly verify --candidate /tmp/butterfly-demo/candidates/boundary_relax.json --output /tmp/butterfly-recheck
```

This accepts typed mutation/action/state data only. Altering the mutation, initial
state, intermediate states, action, or divergence claim must either produce a
different valid certificate or be rejected; an earlier receipt cannot validate
changed bytes. Missing Lean tooling leaves verification unavailable and exits
with code 3. `verify` also exits 3 for a rejected candidate. Normal `demo` and
`evaluate` completion exits 0; the saved per-case verdicts carry the semantic result.
