# proof-pilot

**A kernel-arbitrated LLM proof-completion loop for Lean 4, with anti-cheat and
deterministic replay.**

Point it at a Lean file with a `sorry` and an LLM backend. The loop edits the
proof body, compiles the exact target file with `lake build`, feeds the errors
(or structured LSP goal states) back to the model, and repeats until the **Lean
kernel** accepts or the budget runs out. The model writes the proof; the kernel
decides.

```sh
proof-pilot MyProject/Theorem.lean --lake-dir MyProject --max-iters 10
```

## Why trust the output

- **The kernel is the oracle.** Success is `lake build` exiting clean on the
  exact target file — never the model's claim of success.
- **Anti-cheat.** The patcher structurally cannot modify the theorem statement:
  everything up to `:= by` comes from the file, the model only fills the body,
  and the splice is bounded by the next top-level command. A token-aware scan
  (comment- and string-skipping) rejects `sorry`, `axiom`, and `native_decide`
  in anything that would be spliced.
- **Deterministic replay.** Every session produces a journal (optionally saved
  as versioned JSON) recording each iteration — prompt, response, patch, build
  output, and under best-of-n every candidate plus which one was accepted.
  `--replay transcript.json` re-applies a session without calling any LLM, and
  refuses on Lean-toolchain or Mathlib-revision mismatch unless you pass
  `--allow-toolchain-mismatch`.
- **Best-of-n sampling, soundness-free.** `--samples-per-iter K` fires K
  attempts per iteration and lets the kernel filter: candidates are hash-
  deduplicated, tried shortest-first, and the first to build wins. A wrong
  candidate costs a build, never a false acceptance.

## Backends

`claude` (Claude CLI, default) · `anthropic` (Messages API) · `openai` ·
any OpenAI-compatible endpoint (`openai-compat`, vLLM, ollama, hosted provers)
via `--backend`, `--model`, `--api-key`, `--base-url`.

## Feedback modes

Default is raw `lake build` output. `--lsp` switches to structured Lean
language-server feedback — goal states, hypotheses, tactic probes, and lemma
search — via a bundled Python bridge over
[`leanclient`](https://pypi.org/project/leanclient/). Final verification always
uses `lake build` regardless of mode.

## Extras

- `--notes NOTES.md` — a human-readable debugging report mapping common Lean
  error shapes to concrete guidance (embedders can attach their own
  worked-example citations via `notes::NotesStyle`).
- `--save-transcript session.json` — versioned JSON transcript with toolchain
  and Mathlib-revision pinning.

## Provenance

Extracted from [scribe](https://github.com/LucidSamuel/scribe), where this loop
proves soundness theorems for zero-knowledge circuit gadgets — and runs
*adversarially* (proving negations to hunt counterexamples), which works
unchanged because refutations answer to the same kernel. The loop itself is
domain-agnostic: it needs a Lake project and a theorem, not any particular
mathematics.

## License

MIT
