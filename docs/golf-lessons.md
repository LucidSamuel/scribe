# Golf prover lessons — accumulated from past attempts

Rules distilled from real failures of the automated prover. Injected into every
proof attempt. Maintained by `scribe golf learn`; hand-edits are allowed and
preserved when they generalize.

- **Indent the proof body**: emit every tactic line indented two spaces relative
  to the theorem header — the body is spliced verbatim after `:= by`, and
  flush-left tactics make fragile parses and merge into the next declaration.
  *Trigger:* `unexpected token` right after the patched theorem, or the next
  theorem's name appearing in this theorem's errors.
- **Copy `circuit_proof_start` unfold lists exactly**: include EVERY name the
  obligation needs — for completeness that is `[main, ProverAssumptions,
  ProverSpec, <each child .circuit/.Spec/.Assumptions>]`. Dropping
  `ProverAssumptions` leaves `h_assumptions` folded and unusable.
  *Trigger:* `h_assumptions` has an opaque `ProverAssumptions …` type in the
  goal display.
- **Rewrite hypotheses toward the goal's eval form, not the goal toward the
  hypothesis**: after `circuit_proof_start`, goals mention
  `Expression.eval env input_var…` while `h_assumptions`/`h_input` mention
  `input…`. Use `rwa [← h_input, Vector.getElem_map] at this` (transport the
  hypothesis), not `rw [← Vector.getElem_map, h_input]` on the goal.
  *Trigger:* `Did not find an occurrence of the pattern input_…` in the target
  expression containing `Expression.eval env`.
