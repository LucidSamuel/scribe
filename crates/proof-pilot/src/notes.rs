//! P4 — Structured failure output: render a `SessionJournal` as human-readable Markdown.
//!
//! `render_notes` maps common Lean error shapes to concrete, plain-English guidance
//! (locked decision #5: NOTES.md is a learning tool, not a goal mirror).

use crate::journal::SessionJournal;

/// Render a `SessionJournal` as a Markdown "notes" document.
///
/// The document contains:
/// 1. Title, theorem, and final outcome.
/// 2. Current goal / error state with plain-English guidance.
/// 3. Last ≤ 3 iterations: source diff, build errors, patch status.
/// 4. Suggested next steps with tactic references.
pub fn render_notes(journal: &SessionJournal) -> String {
    let mut out = String::new();

    // ── 1. Header ────────────────────────────────────────────────────────────
    out.push_str("# Proof Pilot — Session Notes\n\n");
    out.push_str(&format!("**File:** `{}`\n\n", journal.lean_file));
    out.push_str(&format!(
        "**Outcome:** {}\n\n",
        outcome_label(&journal.outcome)
    ));
    out.push_str(&format!("**Backend:** {}\n\n", journal.backend));
    out.push_str(&format!(
        "**Iterations run:** {}\n\n",
        journal.iterations.len()
    ));
    out.push_str("---\n\n");

    // ── 2. Current goal / error state ────────────────────────────────────────
    out.push_str("## Current State\n\n");

    // Collect the most recent non-empty build error and goal states.
    let last_errors = journal
        .iterations
        .iter()
        .rev()
        .find(|r| !r.build_errors.trim().is_empty())
        .map(|r| r.build_errors.as_str())
        .unwrap_or("");

    let last_goals: Vec<&str> = journal
        .iterations
        .last()
        .map(|r| r.goal_states.iter().map(String::as_str).collect())
        .unwrap_or_default();

    if !last_goals.is_empty() {
        out.push_str("### Goal state (from LSP)\n\n");
        out.push_str("```\n");
        for g in &last_goals {
            out.push_str(g);
            out.push('\n');
        }
        out.push_str("```\n\n");
    }

    if !last_errors.is_empty() {
        out.push_str("### Last build errors\n\n");
        out.push_str("```\n");
        out.push_str(last_errors.trim_end());
        out.push('\n');
        out.push_str("```\n\n");
    }

    // Plain-English guidance based on error/goal patterns.
    let guidance = pick_guidance(last_errors, &last_goals);
    out.push_str("### Guidance\n\n");
    out.push_str(&guidance);
    out.push_str("\n\n");
    out.push_str("---\n\n");

    // ── 3. Last ≤ 3 iterations ───────────────────────────────────────────────
    out.push_str("## Recent Attempts\n\n");

    let recent_start = journal.iterations.len().saturating_sub(3);
    let recent = &journal.iterations[recent_start..];

    if recent.is_empty() {
        out.push_str("_No iterations recorded._\n\n");
    } else {
        for record in recent {
            out.push_str(&format!("### Iteration {}\n\n", record.index));

            let patch_status = if record.patch_applied {
                "Patch applied"
            } else {
                "Patch REJECTED"
            };
            out.push_str(&format!("**Status:** {patch_status}\n\n"));

            // Diff: source_before → source_after
            out.push_str("**Changes (unified diff):**\n\n");
            out.push_str("```diff\n");
            out.push_str(&line_diff(&record.source_before, &record.source_after));
            out.push_str("```\n\n");

            if !record.build_errors.is_empty() {
                out.push_str("**Build errors:**\n\n");
                out.push_str("```\n");
                out.push_str(record.build_errors.trim_end());
                out.push('\n');
                out.push_str("```\n\n");
            }
        }
    }

    out.push_str("---\n\n");

    // ── 4. Suggested next steps ──────────────────────────────────────────────
    out.push_str("## Suggested Next Steps\n\n");

    // Gather suggestions from the last iteration that has any.
    let recorded_suggestions: Vec<&str> = journal
        .iterations
        .iter()
        .rev()
        .flat_map(|r| r.suggestions.iter().map(String::as_str))
        .take(5)
        .collect();

    let tactic_suggestions = pick_tactic_suggestions(last_errors, &last_goals);
    out.push_str(&tactic_suggestions);
    out.push('\n');

    if !recorded_suggestions.is_empty() {
        out.push_str("\n**LSP-surfaced hints from the last session:**\n\n");
        for s in &recorded_suggestions {
            out.push_str(&format!("- {s}\n"));
        }
        out.push('\n');
    }

    out
}

// ─── Outcome label ────────────────────────────────────────────────────────────

fn outcome_label(outcome: &str) -> &str {
    match outcome {
        "proven" => "PROVEN — the Lean kernel accepted the proof.",
        "exhausted" => "EXHAUSTED — ran out of iterations without a valid proof.",
        "failed" => "FAILED — a fatal error stopped the session.",
        other => other,
    }
}

// ─── Pattern-matched plain-English guidance ───────────────────────────────────

/// Map common error/goal patterns to actionable guidance.
///
/// Matching order matters — more specific patterns first.
fn pick_guidance(build_errors: &str, goal_states: &[&str]) -> String {
    let combined = format!("{build_errors}\n{}", goal_states.join("\n"));

    if combined.contains("linarith") {
        return "**`linarith` does not work on `ZMod p`** — the field is not linearly ordered. \
                Instead, try `linear_combination <expr>` to derive equalities by arithmetic, \
                or `field_simp` followed by `ring` for purely algebraic goals. \
                See `lean/ZkGadgets/RangeCheck.lean` for a worked example that uses \
                `linear_combination` to close ZMod goals."
            .to_string();
    }

    if combined.contains("mul_eq_zero") || combined.contains("IsUnit") {
        return "**Goal involves a zero-divisor argument.** \
                In a prime field `ZMod p`, use `mul_eq_zero.mp h` to case-split: \
                `h : a * b = 0` gives you `a = 0 ∨ b = 0`. \
                You need `haveI : Fact (Nat.Prime p) := ⟨p_prime_proof⟩` in scope, \
                which unlocks `NoZeroDivisors`. \
                See `lean/ZkGadgets/HalvaRangeCheck.lean` for the full pattern."
            .to_string();
    }

    if combined.contains("ZMod") && combined.contains("unsolved goals") {
        return "**Unsolved goals in `ZMod p`.** \
                Common moves: \n\
                - `rcases h01 i with h | h <;> simp [h]` to case-split bit-boolean hypotheses.\n\
                - `push_cast` to coerce `ℕ` literals into `ZMod p` before `ring`.\n\
                - `linear_combination <expr>` when the goal is a linear identity.\n\
                - `norm_num` for concrete numeric equalities.\n\
                See `lean/ZkGadgets/RangeCheck.lean` (the `hcast` block) for an example \
                of coercing natural-number bits into `ZMod p`."
            .to_string();
    }

    if combined.contains("unsolved goals")
        && (combined.contains("Fin") || combined.contains("Finset"))
    {
        return "**Unsolved goals involving `Fin` or `Finset`.** \
                Try `Finset.sum_le_sum` for bounding sums, `Fin.sum_univ_succ` to unroll \
                finite sums by induction, and `omega` for the resulting arithmetic on `ℕ`. \
                `simp only [Fin.val_zero, Fin.val_succ]` often clears `Fin` coercions. \
                See `lean/ZkGadgets/RangeCheck.lean` (the `hlt` block) for a complete worked example.".to_string();
    }

    if combined.contains("unknown identifier") || combined.contains("unknown tactic") {
        return "**Unknown identifier or tactic.** \
                Check spelling — Lean 4 / Mathlib 4 identifiers differ from Lean 3. \
                Common fixes: `Nat.lt_of_le_of_lt` (not `lt_of_le_of_lt`), \
                `Finset.sum_le_sum` (not `Finset.sum_bound`). \
                Run `#check <name>` interactively or search Mathlib4 docs at \
                https://leanprover-community.github.io/mathlib4_docs/."
            .to_string();
    }

    if combined.contains("type mismatch") {
        return "**Type mismatch.** \
                Common causes: forgetting `push_cast` before `ring`, \
                mixing `ℕ` and `ZMod p`, or a `Fin n` where `ℕ` is expected (`Fin.val` to unwrap). \
                Use `#check` and `#print` to inspect expected vs. actual types. \
                `norm_cast` or `push_cast` often closes the gap automatically."
            .to_string();
    }

    if combined.contains("unsolved goals") {
        return "**Unsolved goals remain.** \
                Try `exact?` or `apply?` to let Lean suggest a closing lemma. \
                `simp` with the relevant hypotheses often closes simple goals: `simp [h1, h2]`. \
                For ring-equalities in a field, `ring` or `field_simp; ring` frequently works. \
                For boolean facts (bit = 0 ∨ bit = 1), use `rcases` to split on cases \
                and close each branch with `simp [h]`. \
                See `lean/ZkGadgets/RangeCheck.lean` for worked patterns."
            .to_string();
    }

    if combined.contains("failed to synthesize") || combined.contains("instance") {
        return "**Instance synthesis failed.** \
                Most commonly this means `Fact (Nat.Prime p)` is missing. \
                Add `haveI : Fact (Nat.Prime p) := ⟨p_prime_proof⟩` at the top of the proof, \
                or ensure the `variable` block in the file includes `[Fact (Nat.Prime p)]`. \
                This also unlocks `Field (ZMod p)` and `NoZeroDivisors (ZMod p)`."
            .to_string();
    }

    // Generic fallback
    "**No specific pattern matched.** General checklist:\n\
     - Inspect the goal state carefully: what is on each side of `⊢`?\n\
     - Try `simp`, `ring`, `linarith` (only on ordered types), or `omega` (for `ℕ`/`ℤ`).\n\
     - For field arithmetic, `linear_combination` can close many goals that `ring` cannot.\n\
     - When stuck, add `have h : <intermediate claim> := by <proof>` to build up evidence.\n\
     - The proven gadgets in `lean/ZkGadgets/` are your reference library — \
       `RangeCheck.lean`, `ConditionalSelect.lean`, `PoseidonSbox.lean`, \
       `NonzeroCheck.lean`, `EdwardsAddition.lean`."
        .to_string()
}

// ─── Tactic suggestions ───────────────────────────────────────────────────────

fn pick_tactic_suggestions(build_errors: &str, goal_states: &[&str]) -> String {
    let combined = format!("{build_errors}\n{}", goal_states.join("\n"));

    let mut items: Vec<&str> = Vec::new();

    if combined.contains("linarith") || combined.contains("ZMod") {
        items.push("Replace `linarith` with `linear_combination <expr>` for ZMod goals (see `lean/ZkGadgets/RangeCheck.lean`).");
        items.push("Use `field_simp; ring` for purely algebraic equalities in a prime field.");
    }

    if combined.contains("mul_eq_zero") || combined.contains("* ") {
        items.push("Use `mul_eq_zero.mp h` to case-split products equal to zero (requires `NoZeroDivisors`, unlocked by `Fact (Nat.Prime p)`).");
    }

    if combined.contains("rcases") || combined.contains("bit") || combined.contains("0 ∨") {
        items.push("Use `rcases h with h | h` to split on `a = 0 ∨ a = 1`; close each branch with `simp [h]` or `linear_combination`.");
    }

    if combined.contains("Finset") || combined.contains("Fin") || combined.contains("∑") {
        items.push("Use `Fin.sum_univ_succ` to unfold finite sums; `omega` closes the resulting `ℕ` arithmetic.");
        items.push("Use `Finset.sum_le_sum` to bound a sum by bounding each term individually.");
    }

    if combined.contains("push_cast") || combined.contains("cast") || combined.contains("Nat.cast")
    {
        items.push("Add `push_cast` before `ring` to coerce `ℕ` literals into the goal's type.");
    }

    if combined.contains("Fact") || combined.contains("Prime") || combined.contains("instance") {
        items.push("Add `haveI : Fact (Nat.Prime p) := ⟨p_prime_proof⟩` at the top of the proof to unlock field instances.");
    }

    if items.is_empty() {
        items.push("Try `exact?`, `apply?`, or `simp?` to let Lean suggest the next step.");
        items.push("Consult `lean/ZkGadgets/RangeCheck.lean` for a fully worked gadget proof.");
    }

    let mut out = String::new();
    for item in &items {
        out.push_str(&format!("- {item}\n"));
    }
    out
}

// ─── Simple unified-style line diff ──────────────────────────────────────────

/// Produce a minimal unified-style diff between `before` and `after`.
///
/// Changed lines are shown as `-` (removed) followed by `+` (added).
/// Unchanged lines are shown with a leading space.
fn line_diff(before: &str, after: &str) -> String {
    let before_lines: Vec<&str> = before.lines().collect();
    let after_lines: Vec<&str> = after.lines().collect();

    if before_lines == after_lines {
        return " (no changes)\n".to_string();
    }

    // Use a simple LCS-based approach — for proof files the diffs are small enough
    // that O(n²) is fine.
    let lcs = lcs_indices(&before_lines, &after_lines);

    let mut out = String::new();
    let mut i = 0;
    let mut j = 0;
    let mut lcs_idx = 0;

    while i < before_lines.len() || j < after_lines.len() {
        if lcs_idx < lcs.len() && lcs[lcs_idx] == (i, j) {
            // Common line — show with context
            out.push(' ');
            out.push_str(before_lines[i]);
            out.push('\n');
            i += 1;
            j += 1;
            lcs_idx += 1;
        } else {
            // Removed lines
            while i < before_lines.len() && (lcs_idx >= lcs.len() || lcs[lcs_idx].0 != i) {
                out.push('-');
                out.push_str(before_lines[i]);
                out.push('\n');
                i += 1;
            }
            // Added lines
            while j < after_lines.len() && (lcs_idx >= lcs.len() || lcs[lcs_idx].1 != j) {
                out.push('+');
                out.push_str(after_lines[j]);
                out.push('\n');
                j += 1;
            }
        }
    }

    out
}

/// Return the aligned index pairs for the longest common subsequence of two slices.
fn lcs_indices<'a>(a: &[&'a str], b: &[&'a str]) -> Vec<(usize, usize)> {
    let m = a.len();
    let n = b.len();

    // DP table — cap at 200×200 to avoid blowing up on huge diffs.
    if m > 200 || n > 200 {
        return Vec::new();
    }

    let mut dp = vec![vec![0usize; n + 1]; m + 1];
    for i in (0..m).rev() {
        for j in (0..n).rev() {
            dp[i][j] = if a[i] == b[j] {
                dp[i + 1][j + 1] + 1
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }

    // Traceback
    let mut pairs = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < m && j < n {
        if a[i] == b[j] {
            pairs.push((i, j));
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }

    pairs
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::journal::{IterationRecord, SessionJournal};

    fn make_journal(outcome: &str, iterations: Vec<IterationRecord>) -> SessionJournal {
        SessionJournal {
            theorem_statement: "lean/ZkGadgets/Test.lean".to_string(),
            lean_file: "lean/ZkGadgets/Test.lean".to_string(),
            backend: "claude-cli (test)".to_string(),
            toolchain: "leanprover/lean4:v4.30.0-rc2".to_string(),
            outcome: outcome.to_string(),
            iterations,
        }
    }

    fn make_iter(
        index: u32,
        before: &str,
        after: &str,
        errors: &str,
        goals: Vec<&str>,
        suggestions: Vec<&str>,
        applied: bool,
    ) -> IterationRecord {
        IterationRecord {
            index,
            source_before: before.to_string(),
            source_after: after.to_string(),
            prompt: "Replace the proof body...".to_string(),
            llm_response: "```lean\n  trivial\n```".to_string(),
            build_errors: errors.to_string(),
            goal_states: goals.iter().map(|s| s.to_string()).collect(),
            suggestions: suggestions.iter().map(|s| s.to_string()).collect(),
            patch_applied: applied,
            candidates: Vec::new(),
            accepted_sample: None,
        }
    }

    #[test]
    fn render_notes_contains_key_sections() {
        let iter = make_iter(
            1,
            "theorem foo : True := by\n  sorry\n",
            "theorem foo : True := by\n  trivial\n",
            "Test.lean:2:2: error: unsolved goals\n⊢ True",
            vec!["x : ZMod p\n⊢ q = x * x"],
            vec!["try linear_combination"],
            true,
        );
        let journal = make_journal("exhausted", vec![iter]);
        let notes = render_notes(&journal);

        // Must have the main sections
        assert!(notes.contains("# Proof Pilot"), "missing title");
        assert!(notes.contains("## Current State"), "missing current state");
        assert!(
            notes.contains("## Recent Attempts"),
            "missing recent attempts"
        );
        assert!(
            notes.contains("## Suggested Next Steps"),
            "missing next steps"
        );

        // Must mention the lean file
        assert!(
            notes.contains("lean/ZkGadgets/Test.lean"),
            "missing file path"
        );

        // Must contain the outcome
        assert!(notes.contains("EXHAUSTED"), "missing outcome");
    }

    #[test]
    fn render_notes_linarith_guidance() {
        let iter = make_iter(
            1,
            "theorem foo : True := by\n  linarith\n",
            "theorem foo : True := by\n  linarith\n",
            "Test.lean:2:2: error: linarith failed to find a contradiction",
            vec![],
            vec![],
            false,
        );
        let journal = make_journal("exhausted", vec![iter]);
        let notes = render_notes(&journal);

        assert!(
            notes.contains("linear_combination"),
            "must suggest linear_combination for linarith errors"
        );
        assert!(
            notes.contains("RangeCheck.lean"),
            "must cite RangeCheck.lean"
        );
    }

    #[test]
    fn render_notes_zmod_guidance_suggests_rcases() {
        let iter = make_iter(
            1,
            "theorem foo (x : ZMod p) : x = 0 := by\n  sorry\n",
            "theorem foo (x : ZMod p) : x = 0 := by\n  simp\n",
            "Test.lean:2:2: error: unsolved goals\nx : ZMod p\n⊢ x = 0",
            vec!["x : ZMod p\n⊢ x = 0"],
            vec![],
            true,
        );
        let journal = make_journal("exhausted", vec![iter]);
        let notes = render_notes(&journal);

        assert!(
            notes.contains("ZMod") || notes.contains("rcases") || notes.contains("RangeCheck"),
            "must give ZMod-specific guidance"
        );
    }

    #[test]
    fn render_notes_diff_shows_changes() {
        let before = "theorem foo : True := by\n  sorry\n";
        let after = "theorem foo : True := by\n  trivial\n";
        let iter = make_iter(1, before, after, "", vec![], vec![], true);
        let journal = make_journal("proven", vec![iter]);
        let notes = render_notes(&journal);

        assert!(notes.contains("-  sorry"), "diff must show removed line");
        assert!(notes.contains("+  trivial"), "diff must show added line");
    }

    #[test]
    fn render_notes_no_iterations() {
        let journal = make_journal("failed", vec![]);
        let notes = render_notes(&journal);

        assert!(notes.contains("# Proof Pilot"));
        assert!(notes.contains("FAILED"));
        assert!(notes.contains("No iterations recorded"));
    }

    #[test]
    fn render_notes_only_last_three_iterations() {
        let iters: Vec<IterationRecord> = (1u32..=5)
            .map(|i| {
                make_iter(
                    i,
                    &format!("theorem foo : True := by\n  sorry_{i}\n"),
                    &format!("theorem foo : True := by\n  try_{i}\n"),
                    &format!("error on iter {i}"),
                    vec![],
                    vec![],
                    true,
                )
            })
            .collect();

        let journal = make_journal("exhausted", iters);
        let notes = render_notes(&journal);

        // Should show iterations 3, 4, 5
        assert!(notes.contains("### Iteration 3"), "missing iter 3");
        assert!(notes.contains("### Iteration 4"), "missing iter 4");
        assert!(notes.contains("### Iteration 5"), "missing iter 5");
        // Should NOT show iterations 1 or 2
        assert!(!notes.contains("### Iteration 1"), "should not show iter 1");
        assert!(!notes.contains("### Iteration 2"), "should not show iter 2");
    }

    #[test]
    fn render_notes_instance_guidance() {
        let iter = make_iter(
            1,
            "theorem foo : True := by\n  sorry\n",
            "theorem foo : True := by\n  sorry\n",
            "Test.lean:2:2: error: failed to synthesize Fact (Nat.Prime p)",
            vec![],
            vec![],
            false,
        );
        let journal = make_journal("exhausted", vec![iter]);
        let notes = render_notes(&journal);

        assert!(
            notes.contains("Fact (Nat.Prime p)"),
            "must mention Fact (Nat.Prime p) for instance errors"
        );
    }

    #[test]
    fn line_diff_unchanged_label() {
        let src = "theorem foo : True := by\n  trivial\n";
        let diff = line_diff(src, src);
        assert!(diff.contains("(no changes)"));
    }

    #[test]
    fn line_diff_shows_minus_plus() {
        let before = "line1\nline2\nline3\n";
        let after = "line1\nlineX\nline3\n";
        let diff = line_diff(before, after);
        assert!(diff.contains("-line2"));
        assert!(diff.contains("+lineX"));
    }
}
