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
  hypothesis, and never reverse `Vector.getElem_map`**: after
  `circuit_proof_start`, goals mention `Expression.eval env input_var…` while
  `h_assumptions`/`h_input` mention `input…`. Build the bridge with
  `Vector.getElem_map` applied forward only — e.g.
  `rwa [← h_input, Vector.getElem_map] at this` or a `have hbridge := by rw
  [← h_input, Vector.getElem_map]` — then `rw [hbridge]`/use the hypothesis.
  Using `← Vector.getElem_map` (reversed) produces a pattern headed by a
  metavariable (`?f ?xs[?m]`) that `rw` can never match, on a goal or a `have`.
  *Trigger:* `Did not find an occurrence of the pattern input_…` when
  rewriting the goal directly, or `Invalid rewrite argument: The pattern to
  be substituted is a metavariable`.
- **Use the exact flattened identifier from the diagnostic, never guessed
  dot-field syntax**: structured circuit variables (buffers, vectors nested
  in records) are NOT accessible as `input.field`/`input_var.field` in the
  elaborated goal — the actual bound name is a flattened identifier such as
  `input_buffer` / `input_var_buffer`. Before writing a `have`/`rw` that
  names such a variable, copy the identifier verbatim from the most recent
  error's goal display; do not reconstruct it from the source-level struct
  shape.
  *Trigger:* `unknownIdentifier` on a dotted access (e.g. `x.buffer`,
  `x.field[i]`) immediately after a prior iteration's diagnostic showed the
  same value as a single flattened name (e.g. `x_buffer`).
