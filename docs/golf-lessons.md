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
  hypothesis, and never reverse `Vector.getElem_map`; if a correctly-directioned
  `rw` still can't find the pattern, switch to `simp only` for the same
  lemmas**: after `circuit_proof_start`, goals mention `Expression.eval env
  input_var…` while `h_assumptions`/`h_input` mention `input…`. Build the
  bridge with `Vector.getElem_map` applied forward only — e.g. `rwa [← h_input,
  Vector.getElem_map] at this` or a `have hbridge := by rw [← h_input,
  Vector.getElem_map]` — then `rw [hbridge]`/use the hypothesis. Using
  `← Vector.getElem_map` (reversed) produces a pattern headed by a metavariable
  (`?f ?xs[?m]`) that `rw` can never match, on a goal or a `have`. If the
  direction is already correct per this rule but `rw`/`rw [← hbridge]` still
  reports the same "did not find an occurrence" failure on a second attempt,
  the blocker is usually a coercion mismatch (`↑i` vs `i`/`i.val`/`Fin.val i`)
  between the index in the goal and the index in the hypothesis — `rw` needs a
  syntactic match and coercion nodes defeat it even when the terms are
  definitionally equal. Replace the `rw` chain with `simp only [h_input,
  Vector.getElem_map]` (optionally add the hypothesis/`exact` as a further simp
  lemma or a trailing `exact`/`exact h_assumptions i`), since `simp` normalizes
  through coercions that `rw` won't.
  *Trigger:* `Did not find an occurrence of the pattern input_…` when
  rewriting the goal directly, `Invalid rewrite argument: The pattern to be
  substituted is a metavariable`, or the identical "did not find an occurrence
  of the pattern" error recurring across successive iterations despite
  swapping between direct `rw` and a staged `have hbridge := by rw [...]`.
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
