use std::collections::{BTreeSet, HashMap, HashSet};

use circuit_ir::{CircuitIR, Constraint, Term};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EmitError {
    InvalidIdentifier { kind: &'static str, name: String },
    DuplicateWitnessId(usize),
    UnknownWitnessId { constraint: String, id: usize },
    DuplicateConstraintLabel(String),
    NonLinearDefinition { definition: String },
    MissingSpec,
}

impl std::fmt::Display for EmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitError::InvalidIdentifier { kind, name } => {
                write!(f, "invalid Lean identifier for {}: {}", kind, name)
            }
            EmitError::DuplicateWitnessId(id) => write!(f, "duplicate variable id: {}", id),
            EmitError::UnknownWitnessId { constraint, id } => {
                write!(
                    f,
                    "constraint {} references unknown variable id {}",
                    constraint, id
                )
            }
            EmitError::DuplicateConstraintLabel(label) => {
                write!(f, "duplicate generated constraint label: {}", label)
            }
            EmitError::NonLinearDefinition { definition } => {
                write!(
                    f,
                    "definition {} is not linear (a term multiplies variables)",
                    definition
                )
            }
            EmitError::MissingSpec => {
                write!(f, "circuit has no soundness_spec — nothing to refute")
            }
        }
    }
}

impl std::error::Error for EmitError {}

/// Emit the variable binder lines: public and private variables as distinct
/// binder groups (the verifier sees the former; the prover knows the latter).
fn variable_binders(circuit: &CircuitIR) -> String {
    let mut out = String::new();
    let public: Vec<&str> = circuit.public.iter().map(|v| v.name.as_str()).collect();
    let private: Vec<&str> = circuit.private.iter().map(|v| v.name.as_str()).collect();
    if !public.is_empty() {
        out.push_str(&format!("    ({} : ZMod p)\n", public.join(" ")));
    }
    if !private.is_empty() {
        out.push_str(&format!("    ({} : ZMod p)\n", private.join(" ")));
    }
    out
}

/// Render each definition as a `(name, linear expression)` pair, in order,
/// extending `by_id` as it goes so later definitions and the constraints can
/// reference earlier ones. Definitions share the variable id namespace; a
/// definition referencing a later definition is an error.
fn definition_lets<'a>(
    circuit: &'a CircuitIR,
    by_id: &mut HashMap<usize, &'a str>,
) -> Result<Vec<(&'a str, String)>, EmitError> {
    let mut lets = Vec::with_capacity(circuit.definitions.len());
    for def in &circuit.definitions {
        validate_user_ident("definition", &def.name)?;
        for term in &def.terms {
            if term.vars.len() > 1 {
                return Err(EmitError::NonLinearDefinition {
                    definition: def.name.clone(),
                });
            }
        }
        let expr = emit_terms(&def.terms, by_id, &def.name)?;
        if by_id.insert(def.id, def.name.as_str()).is_some() {
            return Err(EmitError::DuplicateWitnessId(def.id));
        }
        lets.push((def.name.as_str(), expr));
    }
    Ok(lets)
}

/// Emit a decomposed Lean 4 proof scaffold with helper lemmas.
///
/// For circuits with multiple constraints, this emits intermediate helper
/// lemmas that break the proof into smaller steps the LLM can tackle
/// independently. Each constraint gets a lemma that extracts a useful equality
/// from `expr = 0`. The main theorem then uses these helpers.
pub fn emit_lean_decomposed(circuit: &CircuitIR) -> Result<String, EmitError> {
    // Only decompose if there are ≥2 constraints and a soundness spec.
    if circuit.constraints.len() < 2 || circuit.soundness_spec.is_none() {
        return emit_lean(circuit);
    }

    let var_names: Vec<&str> = circuit.variables().map(|v| v.name.as_str()).collect();
    let mut by_id = name_map(circuit)?;
    let lets = definition_lets(circuit, &mut by_id)?;

    // Which definitions each constraint reaches, *transitively*: a helper
    // lemma is a standalone theorem, so its statement must restate — as a
    // `let` prefix — every definition its constraint depends on, following
    // chains where a definition's terms reference earlier definitions' ids.
    // And nothing more: a definition-free constraint keeps a `let`-free
    // statement, so definition-free circuits emit byte-identically to the
    // pre-F1 output. `definition_lets` already rejected forward references,
    // so a referenced definition's closure is always computed before use,
    // and BTreeSet's ascending-index order *is* dependency order.
    let def_index: HashMap<usize, usize> = circuit
        .definitions
        .iter()
        .enumerate()
        .map(|(i, d)| (d.id, i))
        .collect();
    let mut def_closures: Vec<BTreeSet<usize>> = Vec::with_capacity(circuit.definitions.len());
    for (i, def) in circuit.definitions.iter().enumerate() {
        let mut reach = BTreeSet::from([i]);
        for &id in def.terms.iter().flat_map(|t| &t.vars) {
            if let Some(&j) = def_index.get(&id) {
                reach.extend(def_closures[j].iter().copied());
            }
        }
        def_closures.push(reach);
    }
    let constraint_reach = |c: &Constraint| -> BTreeSet<usize> {
        let mut reach = BTreeSet::new();
        for &id in c.terms.iter().flat_map(|t| &t.vars) {
            if let Some(&j) = def_index.get(&id) {
                reach.extend(def_closures[j].iter().copied());
            }
        }
        reach
    };
    let gadget_ident = sanitize_generated_ident(&circuit.name, "gadget");
    let theorem_name = format!("{}_sound", gadget_ident);
    let constraint_labels = generated_constraint_labels(circuit)?;

    let mut out = String::new();

    // -- imports
    out.push_str("import ZkGadgets.Field\n");
    out.push_str("import ZkGadgets.Audit\n");
    out.push_str("import Mathlib.Data.ZMod.Basic\n");
    out.push_str("import Mathlib.Algebra.Field.ZMod\n");
    // The tactics the system prompt teaches (`linear_combination`, `ring`) must
    // be importable, or every model proof fails with "unknown tactic".
    out.push_str("import Mathlib.Tactic.Ring\n");
    out.push_str("import Mathlib.Tactic.LinearCombination\n\n");

    // -- doc comment
    out.push_str(&format!("/-!\n# {}\n\n", circuit.name));
    out.push_str(
        "Auto-generated by lean-emit (decomposed mode). Do not edit the theorem statement.\n\n",
    );
    if !lets.is_empty() {
        out.push_str("Definitions:\n");
        for (name, expr) in &lets {
            out.push_str(&format!("  {} := {}\n", name, expr));
        }
        out.push('\n');
    }
    out.push_str("Constraints:\n");
    for c in &circuit.constraints {
        out.push_str(&format!(
            "  {} : {} = 0\n",
            c.label,
            emit_constraint_expr(c, &by_id)?
        ));
    }
    if let Some(spec) = &circuit.soundness_spec {
        out.push_str(&format!("\nSoundness: {}\n", spec));
    }
    out.push_str("-/\n\n");

    // -- field variable
    out.push_str("variable (p : ℕ) [Fact (Nat.Prime p)]\n\n");

    // -- helper lemmas: extract useful equalities from each constraint
    for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
        let expr = emit_constraint_expr(c, &by_id)?;
        let rearranged = rearrange_constraint(c, &by_id)?;
        let reached = constraint_reach(c);

        out.push_str(&format!(
            "/-- Extract useful equality from constraint `{}`. -/\n",
            label
        ));
        out.push_str(&format!("lemma {}_extract_{}\n", gadget_ident, label));
        out.push_str(&format!("    ({} : ZMod p)\n", var_names.join(" ")));
        if reached.is_empty() {
            out.push_str(&format!("    (h : {} = 0) :\n", expr));
            out.push_str(&format!("    {} := by\n  sorry\n\n", rearranged));
        } else {
            // The constraint mentions definition names, so the helper's
            // statement restates exactly the definitions it reaches as a
            // `let` prefix (the main theorem's kernel-validated shape),
            // followed by the constraint antecedent.
            out.push_str("    : ");
            for (i, &d) in reached.iter().enumerate() {
                if i > 0 {
                    out.push_str("      ");
                }
                let (name, dexpr) = &lets[d];
                out.push_str(&format!("let {} := {}\n", name, dexpr));
            }
            out.push_str(&format!("      (h : {} = 0) →\n", expr));
            out.push_str(&format!("      {} := by\n  sorry\n\n", rearranged));
        }
    }

    // -- main theorem
    out.push_str(&format!("theorem {}\n", theorem_name));
    out.push_str(&format!("    ({} : ZMod p)\n", var_names.join(" ")));

    for h in &circuit.hypotheses {
        out.push_str(&format!("    ({} : {})\n", h.name, h.lean_type));
    }

    if lets.is_empty() {
        for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
            let expr = emit_constraint_expr(c, &by_id)?;
            out.push_str(&format!("    (h_{} : {} = 0)\n", label, expr));
        }

        let conclusion = match &circuit.soundness_spec {
            Some(spec) => format!("    : {}", spec),
            None => "    : True".to_string(),
        };
        out.push_str(&conclusion);
    } else {
        // Same shape as `emit_lean`'s definitions branch (kernel-validated in
        // Phase A): the full `let` chain opens the conclusion, constraints
        // follow as named antecedent binders.
        out.push_str("    : ");
        for (i, (name, expr)) in lets.iter().enumerate() {
            if i > 0 {
                out.push_str("      ");
            }
            out.push_str(&format!("let {} := {}\n", name, expr));
        }
        for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
            let expr = emit_constraint_expr(c, &by_id)?;
            out.push_str(&format!("      (h_{} : {} = 0) →\n", label, expr));
        }
        let spec = circuit.soundness_spec.as_deref().unwrap_or("True");
        out.push_str(&format!("      {}", spec));
    }
    out.push_str(" := by\n");

    // -- proof skeleton with helper lemma applications
    if !lets.is_empty() {
        // The `let` chain and the constraint antecedents live in the
        // conclusion, so bring them into scope before the helper calls.
        let def_names: Vec<&str> = lets.iter().map(|(name, _)| *name).collect();
        let h_names: Vec<String> = constraint_labels
            .iter()
            .map(|label| format!("h_{}", label))
            .collect();
        out.push_str(&format!(
            "  intro {} {}\n",
            def_names.join(" "),
            h_names.join(" ")
        ));
    }
    for label in &constraint_labels {
        out.push_str(&format!(
            "  have h_{}_eq := {}_extract_{} p {} h_{}\n",
            label,
            gadget_ident,
            label,
            var_names.join(" "),
            label
        ));
    }
    out.push_str("  sorry\n");

    // -- audit gate: the main theorem (and, transitively, every helper lemma it
    // uses) must rest only on the trusted kernel axioms for the build to pass.
    out.push_str(&audit_gate(&theorem_name));

    Ok(out)
}

/// Smallest prime strictly greater than or equal to `n` (trial division —
/// refutation primes are tiny).
fn next_prime_at_least(n: u64) -> u64 {
    let mut candidate = n.max(2);
    loop {
        let mut is_prime = candidate >= 2;
        let mut d = 2u64;
        while d * d <= candidate {
            if candidate.is_multiple_of(d) {
                is_prime = false;
                break;
            }
            d += 1;
        }
        if is_prime {
            return candidate;
        }
        candidate += 1;
    }
}

/// The field size for a refutation probe: the smallest prime satisfying every
/// `p > N` hypothesis the circuit declares, and at least `min` (a floor like 5
/// keeps degenerate tiny fields out). A refutation at one valid prime refutes
/// the generic theorem.
pub fn refutation_prime(circuit: &CircuitIR, min: u64) -> u64 {
    let mut lower = min.max(2);
    for h in &circuit.hypotheses {
        let t = h.lean_type.trim();
        if let Some(rest) = t.strip_prefix("p").map(str::trim_start) {
            if let Some(bound) = rest.strip_prefix('>').map(str::trim) {
                if let Ok(n) = bound.parse::<u64>() {
                    lower = lower.max(n + 1);
                }
            }
        }
    }
    next_prime_at_least(lower)
}

/// Replace the standalone identifier `p` in a spec / hypothesis string with a
/// concrete prime literal (`p > 256` → `257 > 256`; `exp` stays untouched).
fn substitute_p(s: &str, prime: u64) -> String {
    let chars: Vec<char> = s.chars().collect();
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    let mut out = String::new();
    for (i, &c) in chars.iter().enumerate() {
        let standalone_p = c == 'p'
            && (i == 0 || !is_ident(chars[i - 1]))
            && (i + 1 == chars.len() || !is_ident(chars[i + 1]));
        if standalone_p {
            out.push_str(&prime.to_string());
        } else {
            out.push(c);
        }
    }
    out
}

/// Emit a **refutation scaffold**: the circuit's soundness statement at a
/// concrete small prime, negated, with a `sorry` body for the adversarial loop
/// to fill.
///
/// ```text
/// theorem <name>_refuted :
///     ¬ (∀ (vars : ZMod <prime>), hyps → constraints → spec) := by
///   sorry
/// ```
///
/// A kernel-accepted proof of this theorem is a concrete counterexample: values
/// satisfying every constraint while violating the spec — the circuit is
/// under-constrained (or the spec is wrong). Exhausting the budget without one
/// is evidence, not proof, that the spec survives attack. The `#audit_axioms`
/// gate holds refutations to the same axiom standard as proofs.
pub fn emit_refutation(circuit: &CircuitIR, prime: u64) -> Result<String, EmitError> {
    let spec = circuit
        .soundness_spec
        .as_ref()
        .ok_or(EmitError::MissingSpec)?;
    let var_names: Vec<&str> = circuit.variables().map(|v| v.name.as_str()).collect();
    let mut by_id = name_map(circuit)?;
    let lets = definition_lets(circuit, &mut by_id)?;
    let theorem_name = format!(
        "{}_refuted",
        sanitize_generated_ident(&circuit.name, "gadget")
    );
    let constraint_labels = generated_constraint_labels(circuit)?;
    let _ = constraint_labels; // labels documented in the header; antecedents are positional

    let mut out = String::new();

    // -- imports (same set the prover scaffolds use)
    out.push_str("import ZkGadgets.Field\n");
    out.push_str("import ZkGadgets.Audit\n");
    out.push_str("import Mathlib.Data.ZMod.Basic\n");
    out.push_str("import Mathlib.Algebra.Field.ZMod\n");
    out.push_str("import Mathlib.Tactic.Ring\n");
    out.push_str("import Mathlib.Tactic.LinearCombination\n\n");

    // -- doc comment
    out.push_str(&format!("/-!\n# {} — refutation target\n\n", circuit.name));
    out.push_str(
        "Auto-generated by lean-emit (refutation mode). Do not edit the theorem statement.\n\n",
    );
    out.push_str(&format!(
        "A kernel-accepted proof of this theorem is a concrete counterexample at\n\
         `p = {prime}`: witness values satisfying every constraint while violating the\n\
         spec. That refutes the generic soundness statement — the circuit is\n\
         under-constrained (or the spec is wrong).\n\n"
    ));
    out.push_str("Constraints:\n");
    for c in &circuit.constraints {
        out.push_str(&format!(
            "  {} : {} = 0\n",
            c.label,
            emit_constraint_expr(c, &by_id)?
        ));
    }
    out.push_str(&format!("\nSpec under attack: {}\n", spec));
    out.push_str("-/\n\n");

    // -- theorem: the negated universally-quantified statement at the probe prime
    out.push_str(&format!("theorem {}\n", theorem_name));
    out.push_str(&format!(
        "    : ¬ (∀ ({} : ZMod {prime}),\n",
        var_names.join(" ")
    ));
    for h in &circuit.hypotheses {
        out.push_str(&format!(
            "        {} →\n",
            substitute_p(&h.lean_type, prime)
        ));
    }
    for (name, expr) in &lets {
        out.push_str(&format!(
            "        let {} := {}\n",
            name,
            substitute_p(expr, prime)
        ));
    }
    for c in &circuit.constraints {
        // constraint expressions can carry `(1 : ZMod p)`-style casts
        let expr = substitute_p(&emit_constraint_expr(c, &by_id)?, prime);
        out.push_str(&format!("        {} = 0 →\n", expr));
    }
    out.push_str(&format!(
        "        ({})) := by\n  sorry\n",
        substitute_p(spec, prime)
    ));

    // -- audit gate: a refutation must rest on the trusted kernel axioms too
    out.push_str(&audit_gate(&theorem_name));

    Ok(out)
}

/// Render an `#audit_axioms` gate line for a theorem. Placed after the proof so
/// `lake build` fails on an unproven or axiom-tainted scaffold rather than
/// merely warning.
fn audit_gate(theorem_name: &str) -> String {
    format!(
        "\n#audit_axioms {theorem_name}  -- proof must rest only on the trusted kernel axioms\n"
    )
}

/// Rearrange a constraint `sum_of_terms = 0` into a more useful equality.
///
/// Strategy: move negative terms to the RHS so we get `positives = negatives`.
fn rearrange_constraint(c: &Constraint, by_id: &HashMap<usize, &str>) -> Result<String, EmitError> {
    let mut lhs_parts = Vec::new();
    let mut rhs_parts = Vec::new();

    for term in &c.terms {
        let coeff = term.coeff.trim();
        let negative = coeff.starts_with('-');
        let abs_coeff = if negative { &coeff[1..] } else { coeff };

        let monomial = if term.vars.is_empty() {
            None
        } else {
            let mut names = Vec::new();
            for &id in &term.vars {
                let name = by_id
                    .get(&id)
                    .copied()
                    .ok_or_else(|| EmitError::UnknownWitnessId {
                        constraint: c.label.clone(),
                        id,
                    })?;
                names.push(name);
            }
            Some(names.join(" * "))
        };

        let expr = match (abs_coeff, &monomial) {
            ("1", Some(m)) => m.clone(),
            (c, Some(m)) => format!("{} * {}", c, m),
            ("1", None) => "(1 : ZMod p)".to_string(),
            (c, None) => format!("({} : ZMod p)", c),
        };

        if negative {
            rhs_parts.push(expr);
        } else {
            lhs_parts.push(expr);
        }
    }

    // If everything is on one side, fall back to `expr = 0`
    if lhs_parts.is_empty() || rhs_parts.is_empty() {
        let expr = emit_constraint_expr(c, by_id)?;
        return Ok(format!("{} = 0", expr));
    }

    Ok(format!(
        "{} = {}",
        lhs_parts.join(" + "),
        rhs_parts.join(" + ")
    ))
}

/// Emit a Lean 4 proof scaffold from a circuit definition.
///
/// The output contains imports, public/private variable parameters, constraint
/// hypotheses, and a `sorry` proof. Definitions are emitted as `let` bindings
/// ahead of the constraint antecedents. The theorem statement is
/// machine-generated; the proof is left for a human or LLM to fill in.
pub fn emit_lean(circuit: &CircuitIR) -> Result<String, EmitError> {
    let mut by_id = name_map(circuit)?;
    let lets = definition_lets(circuit, &mut by_id)?;
    let theorem_name = format!(
        "{}_sound",
        sanitize_generated_ident(&circuit.name, "gadget")
    );
    let constraint_labels = generated_constraint_labels(circuit)?;

    let mut out = String::new();

    // -- imports
    out.push_str("import ZkGadgets.Field\n");
    out.push_str("import ZkGadgets.Audit\n");
    out.push_str("import Mathlib.Data.ZMod.Basic\n");
    out.push_str("import Mathlib.Algebra.Field.ZMod\n");
    // The tactics the system prompt teaches (`linear_combination`, `ring`) must
    // be importable, or every model proof fails with "unknown tactic".
    out.push_str("import Mathlib.Tactic.Ring\n");
    out.push_str("import Mathlib.Tactic.LinearCombination\n\n");

    // -- doc comment
    out.push_str(&format!("/-!\n# {}\n\n", circuit.name));
    out.push_str("Auto-generated by lean-emit. Do not edit the theorem statement.\n\n");
    if !lets.is_empty() {
        out.push_str("Definitions:\n");
        for (name, expr) in &lets {
            out.push_str(&format!("  {} := {}\n", name, expr));
        }
        out.push('\n');
    }
    out.push_str("Constraints:\n");
    for c in &circuit.constraints {
        out.push_str(&format!(
            "  {} : {} = 0\n",
            c.label,
            emit_constraint_expr(c, &by_id)?
        ));
    }
    if let Some(spec) = &circuit.soundness_spec {
        out.push_str(&format!("\nSoundness: {}\n", spec));
    }
    out.push_str("-/\n\n");

    // -- field variable
    out.push_str("variable (p : ℕ) [Fact (Nat.Prime p)]\n\n");

    // -- theorem
    out.push_str(&format!("theorem {}\n", theorem_name));

    // variable parameters: public and private as distinct binder groups
    out.push_str(&variable_binders(circuit));

    // extra hypotheses (e.g. field-size bounds)
    for h in &circuit.hypotheses {
        out.push_str(&format!("    ({} : {})\n", h.name, h.lean_type));
    }

    if lets.is_empty() {
        // constraint hypotheses as named binders
        for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
            let expr = emit_constraint_expr(c, &by_id)?;
            out.push_str(&format!("    (h_{} : {} = 0)\n", label, expr));
        }

        // conclusion
        let conclusion = match &circuit.soundness_spec {
            Some(spec) => format!("    : {}", spec),
            None => "    : True".to_string(),
        };
        out.push_str(&conclusion);
    } else {
        // Definitions must be in scope for the constraints, so the `let`
        // chain opens the conclusion and the constraints follow as NAMED
        // antecedent binders `(h_<label> : …) →`. The names matter: goal
        // displays and `intro` default to them, which is what lets D2
        // diagnostics map a stalled hypothesis back to a source constraint
        // on definition-bearing (i.e. every ragu) circuit.
        out.push_str("    : ");
        for (i, (name, expr)) in lets.iter().enumerate() {
            if i > 0 {
                out.push_str("      ");
            }
            out.push_str(&format!("let {} := {}\n", name, expr));
        }
        for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
            let expr = emit_constraint_expr(c, &by_id)?;
            out.push_str(&format!("      (h_{} : {} = 0) →\n", label, expr));
        }
        let spec = circuit.soundness_spec.as_deref().unwrap_or("True");
        out.push_str(&format!("      {}", spec));
    }
    out.push_str(" := by\n  sorry\n");

    // -- audit gate: proof must rest only on the trusted kernel axioms
    out.push_str(&audit_gate(&theorem_name));

    Ok(out)
}

/// The generated constraint hypothesis names (`h_<sanitized label>`), aligned
/// index-for-index with `circuit.constraints`.
///
/// This is the same mapping the scaffold emitters use, exposed so diagnostics
/// can translate a Lean hypothesis name back to the source constraint (and its
/// `origin` span) instead of showing an engineer `h_c47`.
pub fn constraint_hypothesis_names(circuit: &CircuitIR) -> Result<Vec<String>, EmitError> {
    Ok(generated_constraint_labels(circuit)?
        .into_iter()
        .map(|label| format!("h_{label}"))
        .collect())
}

/// The soundness theorem's `(name, ∀-type)` exactly as `emit_lean` declares
/// it, rendered as a standalone Lean type expression.
///
/// This is what lets a caller *bind* a committed proof artifact to the
/// current IR: `example : <type> := @<name>` is a kernel-checked assertion
/// that the artifact's declaration proves precisely the statement this IR
/// regenerates — not merely "some theorem that builds green".
pub fn soundness_statement(circuit: &CircuitIR) -> Result<(String, String), EmitError> {
    let mut by_id = name_map(circuit)?;
    let lets = definition_lets(circuit, &mut by_id)?;
    let constraint_labels = generated_constraint_labels(circuit)?;
    let name = format!(
        "{}_sound",
        sanitize_generated_ident(&circuit.name, "gadget")
    );

    let mut ty = String::from("∀ (p : ℕ) [Fact (Nat.Prime p)]\n");
    ty.push_str(&variable_binders(circuit));
    for h in &circuit.hypotheses {
        ty.push_str(&format!("    ({} : {})\n", h.name, h.lean_type));
    }

    if lets.is_empty() {
        for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
            let expr = emit_constraint_expr(c, &by_id)?;
            ty.push_str(&format!("    (h_{} : {} = 0)\n", label, expr));
        }
        let spec = circuit.soundness_spec.as_deref().unwrap_or("True");
        ty.push_str(&format!("    , {}", spec));
    } else {
        ty.push_str("    , ");
        for (i, (dname, expr)) in lets.iter().enumerate() {
            if i > 0 {
                ty.push_str("      ");
            }
            ty.push_str(&format!("let {} := {}\n", dname, expr));
        }
        for (c, label) in circuit.constraints.iter().zip(constraint_labels.iter()) {
            let expr = emit_constraint_expr(c, &by_id)?;
            ty.push_str(&format!("      (h_{} : {} = 0) →\n", label, expr));
        }
        let spec = circuit.soundness_spec.as_deref().unwrap_or("True");
        ty.push_str(&format!("      {}", spec));
    }

    Ok((name, ty))
}

/// The refutation theorem's `(name, type)` at `prime`, exactly as
/// `emit_refutation` declares it. Same binding purpose as
/// [`soundness_statement`], for UNSOUND artifacts.
pub fn refutation_statement(
    circuit: &CircuitIR,
    prime: u64,
) -> Result<(String, String), EmitError> {
    let spec = circuit
        .soundness_spec
        .as_ref()
        .ok_or(EmitError::MissingSpec)?;
    let var_names: Vec<&str> = circuit.variables().map(|v| v.name.as_str()).collect();
    let mut by_id = name_map(circuit)?;
    let lets = definition_lets(circuit, &mut by_id)?;
    let name = format!(
        "{}_refuted",
        sanitize_generated_ident(&circuit.name, "gadget")
    );

    let mut ty = format!("¬ (∀ ({} : ZMod {prime}),\n", var_names.join(" "));
    for h in &circuit.hypotheses {
        ty.push_str(&format!(
            "        {} →\n",
            substitute_p(&h.lean_type, prime)
        ));
    }
    for (dname, expr) in &lets {
        ty.push_str(&format!(
            "        let {} := {}\n",
            dname,
            substitute_p(expr, prime)
        ));
    }
    for c in &circuit.constraints {
        let expr = substitute_p(&emit_constraint_expr(c, &by_id)?, prime);
        ty.push_str(&format!("        {} = 0 →\n", expr));
    }
    ty.push_str(&format!("        ({}))", substitute_p(spec, prime)));

    Ok((name, ty))
}

/// Render a constraint as a Lean expression (without `= 0`).
fn emit_constraint_expr(c: &Constraint, by_id: &HashMap<usize, &str>) -> Result<String, EmitError> {
    emit_terms(&c.terms, by_id, &c.label)
}

/// Render a sum of terms as a Lean expression.
fn emit_terms(
    terms: &[Term],
    by_id: &HashMap<usize, &str>,
    context: &str,
) -> Result<String, EmitError> {
    if terms.is_empty() {
        return Ok("0".to_string());
    }

    let mut parts = Vec::new();
    for (i, term) in terms.iter().enumerate() {
        parts.push(emit_term(term, by_id, context, i == 0)?);
    }
    Ok(parts.join(" "))
}

/// Render a single term with sign handling.
///
/// `is_first` controls whether a leading `+` is suppressed.
fn emit_term(
    term: &Term,
    by_id: &HashMap<usize, &str>,
    context: &str,
    is_first: bool,
) -> Result<String, EmitError> {
    let coeff = term.coeff.trim();
    let negative = coeff.starts_with('-');
    let abs_coeff = if negative { &coeff[1..] } else { coeff };

    // monomial: product of variable names
    let monomial: Option<String> = if term.vars.is_empty() {
        None
    } else {
        let mut var_names = Vec::with_capacity(term.vars.len());
        for &id in &term.vars {
            let name = by_id
                .get(&id)
                .copied()
                .ok_or_else(|| EmitError::UnknownWitnessId {
                    constraint: context.to_string(),
                    id,
                })?;
            var_names.push(name);
        }
        Some(var_names.join(" * "))
    };

    // absolute expression (no sign)
    let expr = match (abs_coeff, &monomial) {
        ("1", Some(m)) => m.clone(),
        (c, Some(m)) => format!("{} * {}", c, m),
        ("1", None) => "(1 : ZMod p)".to_string(),
        (c, None) => format!("({} : ZMod p)", c),
    };

    // attach sign
    if is_first {
        if negative {
            Ok(format!("-({})", expr))
        } else {
            Ok(expr)
        }
    } else if negative {
        Ok(format!("- {}", expr))
    } else {
        Ok(format!("+ {}", expr))
    }
}

fn name_map(circuit: &CircuitIR) -> Result<HashMap<usize, &str>, EmitError> {
    let mut by_id = HashMap::new();
    let mut names = HashSet::new();

    for variable in circuit.variables() {
        validate_user_ident("witness", &variable.name)?;
        if by_id.insert(variable.id, variable.name.as_str()).is_some() {
            return Err(EmitError::DuplicateWitnessId(variable.id));
        }
        if !names.insert(variable.name.as_str()) {
            return Err(EmitError::InvalidIdentifier {
                kind: "duplicate witness",
                name: variable.name.clone(),
            });
        }
    }

    for def in &circuit.definitions {
        if !names.insert(def.name.as_str()) {
            return Err(EmitError::InvalidIdentifier {
                kind: "duplicate definition",
                name: def.name.clone(),
            });
        }
    }

    for h in &circuit.hypotheses {
        validate_user_ident("hypothesis", &h.name)?;
    }

    Ok(by_id)
}

fn generated_constraint_labels(circuit: &CircuitIR) -> Result<Vec<String>, EmitError> {
    let mut seen = HashSet::with_capacity(circuit.constraints.len());
    let mut labels = Vec::with_capacity(circuit.constraints.len());

    for constraint in &circuit.constraints {
        let label = sanitize_generated_ident(&constraint.label, "constraint");
        if !seen.insert(label.clone()) {
            return Err(EmitError::DuplicateConstraintLabel(label));
        }
        labels.push(label);
    }

    Ok(labels)
}

fn validate_user_ident(kind: &'static str, name: &str) -> Result<(), EmitError> {
    if is_valid_lean_ident(name) {
        Ok(())
    } else {
        Err(EmitError::InvalidIdentifier {
            kind,
            name: name.to_string(),
        })
    }
}

fn sanitize_generated_ident(input: &str, fallback: &str) -> String {
    let mut out = String::new();
    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }

    while out.contains("__") {
        out = out.replace("__", "_");
    }

    let out = out.trim_matches('_');
    let mut out = if out.is_empty() {
        fallback.to_string()
    } else {
        out.to_string()
    };

    if out.as_bytes().first().is_some_and(u8::is_ascii_digit) || is_lean_keyword(&out) {
        out.insert_str(0, fallback);
        out.insert(fallback.len(), '_');
    }

    out
}

fn is_valid_lean_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };

    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }

    if is_lean_keyword(name) {
        return false;
    }

    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
}

fn is_lean_keyword(name: &str) -> bool {
    matches!(
        name,
        "abbrev"
            | "axiom"
            | "by"
            | "class"
            | "def"
            | "deriving"
            | "do"
            | "else"
            | "end"
            | "example"
            | "extends"
            | "for"
            | "forall"
            | "fun"
            | "have"
            | "if"
            | "import"
            | "in"
            | "inductive"
            | "infix"
            | "instance"
            | "let"
            | "macro"
            | "match"
            | "mutual"
            | "namespace"
            | "open"
            | "opaque"
            | "partial"
            | "private"
            | "protected"
            | "section"
            | "set_option"
            | "structure"
            | "syntax"
            | "theorem"
            | "unsafe"
            | "variable"
            | "where"
            | "with"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_ir::{Definition, Variable};

    fn examples_dir() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("examples")
    }

    fn load(gadget: &str) -> CircuitIR {
        circuit_ir::load_toml_file(&examples_dir().join(gadget).join("gadget.toml")).unwrap()
    }

    fn var(id: usize, name: &str) -> Variable {
        Variable {
            id,
            name: name.to_string(),
        }
    }

    fn term(coeff: &str, vars: &[usize]) -> Term {
        Term {
            coeff: coeff.to_string(),
            vars: vars.to_vec(),
        }
    }

    fn constraint(label: &str, terms: Vec<Term>) -> Constraint {
        Constraint {
            label: label.to_string(),
            terms,
            origin: None,
        }
    }

    #[test]
    fn emit_range_check() {
        let circuit = load("range-check");
        let out = emit_lean(&circuit).unwrap();

        // has theorem with correct name
        assert!(out.contains("theorem range_check_8bit_sound"));
        // has all witnesses
        assert!(out.contains("(x b0 b1 b2 b3 b4 b5 b6 b7 : ZMod p)"));
        // bit constraint renders correctly: b0 * b0 - b0 = 0
        assert!(out.contains("h_bit_0 : b0 * b0 - b0 = 0"));
        // decomposition has weighted terms
        assert!(out.contains("h_decomposition :"));
        assert!(out.contains("128 * b7"));
        assert!(out.contains("- x = 0"));
        // ends with sorry
        assert!(out.contains("sorry"));
        // non-vacuous soundness spec in conclusion, with its load-bearing bound
        assert!(out.contains("ZMod.val x < 256"));
        assert!(out.contains("(hp : p > 256)"));
        // audit gate on the theorem, with its import
        assert!(out.contains("import ZkGadgets.Audit"));
        assert!(out.trim_end().ends_with(
            "#audit_axioms range_check_8bit_sound  -- proof must rest only on the trusted kernel axioms"
        ));
    }

    #[test]
    fn refutation_prime_honors_bounds() {
        let circuit = load("range-check");
        // hp : p > 256 forces the probe past the bound, to the next prime.
        assert_eq!(refutation_prime(&circuit, 5), 257);
        let no_hyp = load("poseidon-sbox");
        assert_eq!(refutation_prime(&no_hyp, 5), 5);
        assert_eq!(refutation_prime(&no_hyp, 6), 7);
    }

    #[test]
    fn substitute_p_is_identifier_aware() {
        assert_eq!(substitute_p("p > 256", 257), "257 > 256");
        assert_eq!(substitute_p("(1 : ZMod p)", 5), "(1 : ZMod 5)");
        // `p` inside identifiers must survive.
        assert_eq!(substitute_p("exp + p_val + x", 5), "exp + p_val + x");
        assert_eq!(substitute_p("ZMod.val x < 256", 257), "ZMod.val x < 256");
    }

    #[test]
    fn emit_refutation_negates_statement_at_concrete_prime() {
        let circuit = load("range-check");
        let out = emit_refutation(&circuit, 257).unwrap();

        assert!(out.contains("theorem range_check_8bit_refuted"));
        // negated ∀ at the concrete prime; no generic field variable, no Fact binder
        assert!(out.contains("¬ (∀ (x b0 b1 b2 b3 b4 b5 b6 b7 : ZMod 257),"));
        assert!(!out.contains("variable (p"));
        // the p-bound hypothesis and spec are concretized
        assert!(out.contains("257 > 256 →"));
        assert!(out.contains("(ZMod.val x < 256)) := by"));
        // constraints appear as antecedents
        assert!(out.contains("b0 * b0 - b0 = 0 →"));
        // scaffold is red until refuted, and gated
        assert!(out.contains("sorry"));
        assert!(out.trim_end().ends_with(
            "#audit_axioms range_check_8bit_refuted  -- proof must rest only on the trusted kernel axioms"
        ));
    }

    #[test]
    fn emit_refutation_requires_a_spec() {
        let circuit = CircuitIR {
            name: "no-spec".into(),
            modulus: "7".into(),
            private: vec![var(0, "x")],
            ..Default::default()
        };
        assert_eq!(emit_refutation(&circuit, 5), Err(EmitError::MissingSpec));
    }

    #[test]
    fn emit_conditional_select() {
        let circuit = load("conditional-select");
        let out = emit_lean(&circuit).unwrap();

        assert!(out.contains("theorem conditional_select_sound"));
        assert!(out.contains("(b x y z : ZMod p)"));
        // boolean constraint: b * b - b = 0
        assert!(out.contains("h_boolean : b * b - b = 0"));
        // select constraint: b * x + y - b * y - z = 0
        assert!(out.contains("h_select : b * x + y - b * y - z = 0"));
        assert!(out.contains("sorry"));
    }

    #[test]
    fn emit_poseidon_sbox() {
        let circuit = load("poseidon-sbox");
        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("theorem poseidon_sbox_sound"));
        assert!(out.contains("(x q r y : ZMod p)"));
        assert!(out.contains("h_square_1 : q - x * x = 0"));
        assert!(out.contains("h_square_2 : r - q * q = 0"));
        assert!(out.contains("h_output : y - r * x = 0"));
        assert!(out.contains("y = x ^ 5"));
    }

    #[test]
    fn emit_nonzero_check() {
        let circuit = load("nonzero-check");
        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("theorem nonzero_check_sound"));
        assert!(out.contains("h_inverse : x * x_inv - (1 : ZMod p) = 0"));
        assert!(out.contains("x ≠ 0"));
    }

    #[test]
    fn emit_edwards_addition() {
        let circuit = load("edwards-addition");
        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("theorem edwards_addition_sound"));
        assert!(out.contains("(x1 y1 x2 y2 x3 y3 : ZMod p)"));
        // hypotheses before constraints
        assert!(out.contains("h_on_curve_1"));
        assert!(out.contains("h_on_curve_2"));
        assert!(out.contains("h_nondeg_x"));
        assert!(out.contains("h_nondeg_y"));
        assert!(out.contains("h_add_x"));
        assert!(out.contains("h_add_y"));
        assert!(out.contains("168700"));
    }

    #[test]
    fn emit_range_check_with_hypothesis() {
        let circuit = load("range-check");
        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("(hp : p > 256)"));
        // hypothesis appears before constraints
        let hp_pos = out.find("hp : p > 256").unwrap();
        let hbit_pos = out.find("h_bit_0").unwrap();
        assert!(hp_pos < hbit_pos);
    }

    #[test]
    fn emits_terms_by_variable_id_not_position() {
        let circuit = CircuitIR {
            name: "out-of-order".to_string(),
            modulus: "17".to_string(),
            private: vec![var(10, "x"), var(3, "y")],
            constraints: vec![constraint("product", vec![term("1", &[3, 10])])],
            ..Default::default()
        };

        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("h_product : y * x = 0"));
    }

    #[test]
    fn rejects_unknown_variable_id() {
        let circuit = CircuitIR {
            name: "bad-ref".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x")],
            constraints: vec![constraint("missing", vec![term("1", &[1])])],
            ..Default::default()
        };

        let err = emit_lean(&circuit).unwrap_err();
        assert!(matches!(err, EmitError::UnknownWitnessId { id: 1, .. }));
    }

    #[test]
    fn rejects_invalid_user_identifier() {
        let circuit = CircuitIR {
            name: "bad-ident".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x-bad")],
            ..Default::default()
        };

        let err = emit_lean(&circuit).unwrap_err();
        assert!(matches!(
            err,
            EmitError::InvalidIdentifier {
                kind: "witness",
                ..
            }
        ));
    }

    #[test]
    fn public_and_private_are_distinct_binder_groups() {
        let circuit = CircuitIR {
            name: "split".to_string(),
            modulus: "17".to_string(),
            public: vec![var(0, "out")],
            private: vec![var(1, "w")],
            constraints: vec![constraint("bind", vec![term("1", &[0]), term("-1", &[1])])],
            ..Default::default()
        };

        let out = emit_lean(&circuit).unwrap();
        // two separate binder lines, public first
        assert!(out.contains("    (out : ZMod p)\n    (w : ZMod p)\n"));
        assert!(out.contains("h_bind : out - w = 0"));
    }

    #[test]
    fn definitions_emit_as_let_bindings_before_constraints() {
        let circuit = CircuitIR {
            name: "with-def".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x"), var(1, "y"), var(2, "z")],
            definitions: vec![Definition {
                id: 3,
                name: "s".to_string(),
                terms: vec![term("1", &[0]), term("2", &[1])],
            }],
            // the constraint references the definition by id, like a variable
            constraints: vec![constraint(
                "uses_s",
                vec![term("1", &[3, 3]), term("-1", &[2])],
            )],
            soundness_spec: Some("z = (x + 2 * y) ^ 2".to_string()),
            ..Default::default()
        };

        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("let s := x + 2 * y\n"));
        // constraint mentions the definition by name, not its expansion, and
        // keeps its NAMED h_<label> binder so goal displays / intro / D2
        // citations still see the generated hypothesis name
        assert!(out.contains("(h_uses_s : s * s - z = 0) →"));
        // let binding comes before the constraint antecedent that uses it
        assert!(out.find("let s :=").unwrap() < out.find("(h_uses_s :").unwrap());
        assert!(out.contains("z = (x + 2 * y) ^ 2 := by"));
        // and the hypothesis-name helper agrees
        assert_eq!(
            constraint_hypothesis_names(&circuit).unwrap(),
            vec!["h_uses_s"]
        );
    }

    #[test]
    fn soundness_statement_mirrors_emit_lean() {
        // The regenerated ∀-type must carry exactly the pieces the scaffold
        // theorem declares — same binders, same constraint expressions, same
        // spec — or artifact binding would be vacuous.
        let circuit = load("range-check");
        let (name, ty) = soundness_statement(&circuit).unwrap();
        assert_eq!(name, "range_check_8bit_sound");
        assert!(ty.starts_with("∀ (p : ℕ) [Fact (Nat.Prime p)]"));
        assert!(ty.contains("(x b0 b1 b2 b3 b4 b5 b6 b7 : ZMod p)"));
        assert!(ty.contains("(hp : p > 256)"));
        assert!(ty.contains("(h_bit_0 : b0 * b0 - b0 = 0)"));
        assert!(ty.trim_end().ends_with(", ZMod.val x < 256"));

        // definition-bearing circuits keep the let-chain + named arrows
        let with_def = CircuitIR {
            name: "with-def".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x"), var(1, "z")],
            definitions: vec![Definition {
                id: 2,
                name: "s".to_string(),
                terms: vec![term("2", &[0])],
            }],
            constraints: vec![constraint(
                "uses_s",
                vec![term("1", &[2]), term("-1", &[1])],
            )],
            soundness_spec: Some("z = 2 * x".to_string()),
            ..Default::default()
        };
        let (_, ty) = soundness_statement(&with_def).unwrap();
        assert!(ty.contains("let s := 2 * x\n"));
        assert!(ty.contains("(h_uses_s : s - z = 0) →"));
    }

    #[test]
    fn refutation_statement_mirrors_emit_refutation() {
        let circuit = load("range-check");
        let (name, ty) = refutation_statement(&circuit, 257).unwrap();
        assert_eq!(name, "range_check_8bit_refuted");
        assert!(ty.starts_with("¬ (∀ (x b0 b1 b2 b3 b4 b5 b6 b7 : ZMod 257),"));
        assert!(ty.contains("257 > 256 →"));
        assert!(ty.contains("b0 * b0 - b0 = 0 →"));
        assert!(ty.trim_end().ends_with("(ZMod.val x < 256))"));
    }

    fn tokens(s: &str) -> Vec<&str> {
        s.split_whitespace().collect()
    }

    /// The statement `soundness_statement` regenerates must be token-identical
    /// to the theorem statement `emit_lean` emits (modulo the `theorem` /
    /// `∀`-type framing). The two are parallel renderings of the same pieces;
    /// if one is ever edited without the other, the binding oracle starts
    /// giving false results in both directions — the probe would bind proofs
    /// to a statement the scaffold no longer emits, or refuse proofs of the
    /// statement it does.
    fn assert_soundness_statement_matches(circuit: &CircuitIR) {
        let (name, ty) = soundness_statement(circuit).unwrap();
        let scaffold = emit_lean(circuit).unwrap();

        let header = format!("theorem {name}\n");
        let start = scaffold
            .find(&header)
            .unwrap_or_else(|| panic!("scaffold lacks `{header}`"))
            + header.len();
        let end = scaffold[start..]
            .find(" := by")
            .expect("scaffold theorem has a proof marker");
        let slice = &scaffold[start..start + end];

        // The scaffold writes binders then `    : <conclusion>`; the ∀-type
        // writes the same binders then `    , <conclusion>` under a
        // `∀ (p : ℕ) [Fact (Nat.Prime p)]` head that the scaffold's
        // `variable` line supplies instead.
        let expected = format!(
            "∀ (p : ℕ) [Fact (Nat.Prime p)]\n{}",
            slice.replacen("\n    : ", "\n    , ", 1)
        );
        assert_eq!(
            tokens(&ty),
            tokens(&expected),
            "soundness_statement drifted from emit_lean for {}",
            circuit.name
        );
    }

    /// Same guard for the refutation pair: the regenerated type must be
    /// token-identical to what `emit_refutation` declares.
    fn assert_refutation_statement_matches(circuit: &CircuitIR, prime: u64) {
        let (name, ty) = refutation_statement(circuit, prime).unwrap();
        let scaffold = emit_refutation(circuit, prime).unwrap();

        let header = format!("theorem {name}\n    : ");
        let start = scaffold
            .find(&header)
            .unwrap_or_else(|| panic!("refutation scaffold lacks `{header}`"))
            + header.len();
        let end = scaffold[start..]
            .find(" := by")
            .expect("refutation theorem has a proof marker");
        let slice = &scaffold[start..start + end];

        assert_eq!(
            tokens(&ty),
            tokens(slice),
            "refutation_statement drifted from emit_refutation for {}",
            circuit.name
        );
    }

    #[test]
    fn statements_match_emitted_theorems_for_every_gadget() {
        for gadget in [
            "range-check",
            "conditional-select",
            "poseidon-sbox",
            "nonzero-check",
            "edwards-addition",
        ] {
            let circuit = load(gadget);
            assert_soundness_statement_matches(&circuit);
            let prime = refutation_prime(&circuit, 5);
            assert_refutation_statement_matches(&circuit, prime);
        }

        // definition-bearing shape too — the let-chain + named-arrow branch
        // is a separate code path in both renderers
        let with_def = CircuitIR {
            name: "def-drift-guard".to_string(),
            modulus: "17".to_string(),
            public: vec![var(0, "out")],
            private: vec![var(1, "x"), var(2, "y")],
            definitions: vec![Definition {
                id: 3,
                name: "s".to_string(),
                terms: vec![term("1", &[1]), term("2", &[2]), term("1", &[])],
            }],
            constraints: vec![
                constraint("uses_s", vec![term("1", &[3, 3]), term("-1", &[0])]),
                constraint("pin", vec![term("1", &[1])]),
            ],
            hypotheses: vec![circuit_ir::Hypothesis {
                name: "hp".into(),
                lean_type: "p > 2".into(),
            }],
            soundness_spec: Some("out = (x + 2 * y + 1) ^ 2".to_string()),
            ..Default::default()
        };
        assert_soundness_statement_matches(&with_def);
        assert_refutation_statement_matches(&with_def, 5);
    }

    #[test]
    fn refutation_carries_definitions_at_the_probe_prime() {
        let circuit = CircuitIR {
            name: "with-def".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x"), var(1, "y")],
            definitions: vec![Definition {
                id: 2,
                name: "s".to_string(),
                terms: vec![term("1", &[0]), term("1", &[1]), term("1", &[])],
            }],
            constraints: vec![constraint("zero_sum", vec![term("1", &[2])])],
            soundness_spec: Some("x + y + 1 = 0".to_string()),
            ..Default::default()
        };

        let out = emit_refutation(&circuit, 5).unwrap();
        // the constant term's cast is concretized inside the let binding
        assert!(out.contains("let s := x + y + (1 : ZMod 5)"));
        assert!(out.contains("s = 0 →"));
    }

    #[test]
    fn rejects_non_linear_definition() {
        let circuit = CircuitIR {
            name: "bad-def".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x")],
            definitions: vec![Definition {
                id: 1,
                name: "sq".to_string(),
                terms: vec![term("1", &[0, 0])],
            }],
            ..Default::default()
        };

        let err = emit_lean(&circuit).unwrap_err();
        assert!(matches!(err, EmitError::NonLinearDefinition { .. }));
    }

    #[test]
    fn definitions_may_reference_earlier_definitions_only() {
        let base = |defs: Vec<Definition>| CircuitIR {
            name: "chain".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x")],
            definitions: defs,
            constraints: vec![constraint("c", vec![term("1", &[0])])],
            ..Default::default()
        };

        // forward chain works
        let ok = base(vec![
            Definition {
                id: 1,
                name: "a".to_string(),
                terms: vec![term("2", &[0])],
            },
            Definition {
                id: 2,
                name: "b".to_string(),
                terms: vec![term("1", &[1])],
            },
        ]);
        let out = emit_lean(&ok).unwrap();
        assert!(out.contains("let a := 2 * x\n"));
        assert!(out.contains("let b := a\n"));

        // referencing a later definition fails
        let bad = base(vec![
            Definition {
                id: 1,
                name: "a".to_string(),
                terms: vec![term("1", &[2])],
            },
            Definition {
                id: 2,
                name: "b".to_string(),
                terms: vec![term("1", &[0])],
            },
        ]);
        let err = emit_lean(&bad).unwrap_err();
        assert!(matches!(err, EmitError::UnknownWitnessId { id: 2, .. }));
    }

    #[test]
    fn decompose_edwards_addition() {
        let circuit = load("edwards-addition");
        let out = emit_lean_decomposed(&circuit).unwrap();
        // Should have helper lemmas
        assert!(out.contains("lemma edwards_addition_extract_add_x"));
        assert!(out.contains("lemma edwards_addition_extract_add_y"));
        // Helper lemmas should have rearranged equalities
        assert!(out.contains("= x1 * y2 + y1 * x2")); // add_x positive terms
        assert!(out.contains("168696 * y3 * x1 * x2 * y1 * y2 + y1 * y2")); // add_y RHS
                                                                            // Main theorem should reference helpers
        assert!(out.contains("h_add_x_eq := edwards_addition_extract_add_x"));
        assert!(out.contains("h_add_y_eq := edwards_addition_extract_add_y"));
        // Still has the main theorem
        assert!(out.contains("theorem edwards_addition_sound"));
    }

    #[test]
    fn decompose_poseidon_sbox() {
        let circuit = load("poseidon-sbox");
        let out = emit_lean_decomposed(&circuit).unwrap();
        assert!(out.contains("lemma poseidon_sbox_extract_square_1"));
        assert!(out.contains("lemma poseidon_sbox_extract_square_2"));
        assert!(out.contains("lemma poseidon_sbox_extract_output"));
        // Rearranged: q = x * x, r = q * q, y = r * x
        assert!(out.contains("q = x * x"));
        assert!(out.contains("r = q * q"));
        assert!(out.contains("y = r * x"));
        // One audit gate, on the main theorem (helpers are covered transitively).
        assert_eq!(out.matches("#audit_axioms").count(), 1);
        assert!(out.contains("#audit_axioms poseidon_sbox_sound"));
    }

    #[test]
    fn decompose_skips_simple_gadgets() {
        // nonzero-check has only 1 constraint, should fall back to emit_lean
        let circuit = load("nonzero-check");
        let out = emit_lean_decomposed(&circuit).unwrap();
        // Should NOT have extract lemmas
        assert!(!out.contains("extract_"));
        // Should have the normal theorem
        assert!(out.contains("theorem nonzero_check_sound"));
    }

    /// A definition-bearing circuit with a chained definition (`t` references
    /// `s` by id) and three constraints with distinct definition reach:
    /// `uses_t` reaches {s, t} transitively, `uses_s` reaches {s}, and
    /// `plain` reaches nothing.
    fn chained_defs_circuit() -> CircuitIR {
        CircuitIR {
            name: "defs".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x"), var(1, "y"), var(2, "z")],
            definitions: vec![
                Definition {
                    id: 3,
                    name: "s".to_string(),
                    terms: vec![term("1", &[0]), term("1", &[1])],
                },
                Definition {
                    id: 4,
                    name: "t".to_string(),
                    terms: vec![term("2", &[3])],
                },
            ],
            constraints: vec![
                constraint("uses_t", vec![term("1", &[4]), term("-1", &[2])]),
                constraint("uses_s", vec![term("1", &[3]), term("-1", &[1])]),
                constraint("plain", vec![term("1", &[0])]),
            ],
            soundness_spec: Some("z = 2 * (x + y)".to_string()),
            ..Default::default()
        }
    }

    /// F1 closed: decomposed mode no longer falls back on definitions. Each
    /// helper lemma restates exactly the definitions its constraint reaches
    /// *transitively*, as a `let` prefix in dependency order.
    #[test]
    fn decompose_restates_reached_definitions_per_helper() {
        let out = emit_lean_decomposed(&chained_defs_circuit()).unwrap();

        // `uses_t` mentions only `t`, but `t`'s terms reference `s`, so the
        // chain is followed: both lets, dependency order (`s` before `t`).
        assert!(out.contains(
            "lemma defs_extract_uses_t\n    \
             (x y z : ZMod p)\n    \
             : let s := x + y\n      \
             let t := 2 * s\n      \
             (h : t - z = 0) →\n      \
             t = z := by\n  sorry\n"
        ));

        // `uses_s` reaches only `s`: exactly one let, no `t`.
        assert!(out.contains(
            "lemma defs_extract_uses_s\n    \
             (x y z : ZMod p)\n    \
             : let s := x + y\n      \
             (h : s - y = 0) →\n      \
             s = y := by\n  sorry\n"
        ));

        // The main theorem keeps its Phase-A shape: the FULL let chain opens
        // the conclusion, constraints follow as named antecedent binders, and
        // the proof skeleton intros them before applying the helpers.
        assert!(out.contains(
            "theorem defs_sound\n    \
             (x y z : ZMod p)\n    \
             : let s := x + y\n      \
             let t := 2 * s\n      \
             (h_uses_t : t - z = 0) →\n      \
             (h_uses_s : s - y = 0) →\n      \
             (h_plain : x = 0) →\n      \
             z = 2 * (x + y) := by\n  \
             intro s t h_uses_t h_uses_s h_plain\n"
        ));
        assert!(out.contains("  have h_uses_t_eq := defs_extract_uses_t p x y z h_uses_t\n"));
    }

    /// A helper whose constraint touches no definitions keeps today's
    /// `let`-free statement shape, even in a definition-bearing circuit.
    #[test]
    fn decompose_definition_free_constraint_gets_no_let_prefix() {
        let out = emit_lean_decomposed(&chained_defs_circuit()).unwrap();
        assert!(out.contains(
            "lemma defs_extract_plain\n    \
             (x y z : ZMod p)\n    \
             (h : x = 0) :\n    \
             x = 0 := by\n  sorry\n"
        ));
    }

    // Byte-identity of definition-free decomposed output is pinned by
    // frontend-toml's compile-time snapshot tests (include_str! across all
    // five gadgets) — no duplicate runtime-path assertion here.

    /// SEMANTIC validation: the definition-bearing decomposed scaffold must be
    /// well-formed Lean — every helper statement and the main theorem
    /// elaborate, with `sorry` *warnings* but no *errors*.
    ///
    /// The `#audit_axioms` gate is stripped first: it is designed to fail the
    /// build on an unproven scaffold (sorryAx), which is exactly the state a
    /// scaffold ships in; this test checks statement well-formedness only.
    ///
    /// Run manually (needs built ZkGadgets + Mathlib oleans in `lean/`):
    /// `cargo test -p lean-emit -- --ignored --nocapture`
    #[test]
    #[ignore = "elaborates the scaffold with the Lean toolchain via `lake env lean` (slow)"]
    fn decomposed_definition_scaffold_elaborates() {
        let out = emit_lean_decomposed(&chained_defs_circuit()).unwrap();
        let stripped: String = out
            .lines()
            .filter(|l| !l.starts_with("#audit_axioms"))
            .collect::<Vec<_>>()
            .join("\n");

        let lake_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("lean");
        let file =
            std::env::temp_dir().join(format!("scribe-f1-decomposed-{}.lean", std::process::id()));
        std::fs::write(&file, &stripped).unwrap();

        let output = std::process::Command::new("lake")
            .args(["env", "lean"])
            .arg(&file)
            .current_dir(&lake_dir)
            .output()
            .expect("lake env lean should spawn (is the Lean toolchain installed?)");
        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let _ = std::fs::remove_file(&file);

        // visible under --nocapture: the expected shape is one
        // `declaration uses 'sorry'` warning per helper plus the main theorem
        println!("lake env lean output:\n{combined}");
        assert!(
            output.status.success(),
            "lake env lean rejected the scaffold:\n{combined}"
        );
        assert!(
            !combined.contains("error"),
            "scaffold elaborated with errors:\n{combined}"
        );
        assert!(
            combined.contains("sorry"),
            "expected the `declaration uses 'sorry'` warning:\n{combined}"
        );
    }

    #[test]
    fn hypothesis_names_align_with_constraints_and_sanitize() {
        let circuit = CircuitIR {
            name: "n".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x")],
            constraints: vec![
                constraint("bit_0", vec![term("1", &[0])]),
                constraint("select-value!", vec![term("1", &[0])]),
            ],
            ..Default::default()
        };
        let names = constraint_hypothesis_names(&circuit).unwrap();
        assert_eq!(names, vec!["h_bit_0", "h_select_value"]);
        // and they match what the scaffold actually emits
        let out = emit_lean(&circuit).unwrap();
        for n in &names {
            assert!(
                out.contains(&format!("({n} :")),
                "{n} missing from scaffold"
            );
        }
    }

    #[test]
    fn sanitizes_generated_identifiers() {
        let circuit = CircuitIR {
            name: "8-bit gadget!".to_string(),
            modulus: "17".to_string(),
            private: vec![var(0, "x")],
            constraints: vec![constraint("select-value!", vec![term("1", &[0])])],
            ..Default::default()
        };

        let out = emit_lean(&circuit).unwrap();
        assert!(out.contains("theorem gadget_8_bit_gadget_sound"));
        assert!(out.contains("h_select_value : x = 0"));
    }
}
