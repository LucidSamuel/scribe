//! Static, dependency-free presentation of typed Butterfly evidence.
use butterfly::{Account, Action, CaseReport, EvaluationReport, Mutation};
use scribe_core::Outcome;
use std::{
    fmt::Write,
    path::{Component, Path},
};

fn escape(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

// Link only to existing regular evidence inside this output directory. Canonical
// containment rejects symlinks escaping it; encoding prevents URI interpretation.
fn evidence_href(root: &Path, path: &Path) -> Option<String> {
    let root = root.canonicalize().ok()?;
    let target = path.canonicalize().ok()?;
    if !target.is_file() {
        return None;
    }
    let relative = target.strip_prefix(root).ok()?;
    let mut encoded = Vec::new();
    for component in relative.components() {
        let Component::Normal(name) = component else {
            return None;
        };
        let mut part = String::new();
        for byte in name.to_str()?.bytes() {
            if byte.is_ascii_alphanumeric() || b"-_.".contains(&byte) {
                part.push(byte as char);
            } else {
                write!(part, "%{byte:02X}").unwrap();
            }
        }
        encoded.push(part);
    }
    (!encoded.is_empty()).then(|| format!("./{}", encoded.join("/")))
}

fn status(case: &CaseReport) -> (&'static str, &'static str) {
    // Both the recorded verification mode and core verdict must agree.
    match (case.verification_status, case.verdict.outcome()) {
        ("checked_refutation", Outcome::Reject(_)) => ("refuted", "Checked counterexample"),
        ("checked_safe", Outcome::Accept(_)) => ("safe", "Checked conservation theorem"),
        ("unavailable", _) => ("unknown", "Verification unavailable"),
        ("rejected", _) => ("unknown", "Candidate rejected"),
        _ if case.search.candidate.is_some() => ("unknown", "Unverified candidate"),
        _ => ("unknown", "Unknown within search bounds"),
    }
}

fn action_label(action: &Action) -> String {
    let (kind, account, amount) = match action {
        Action::Issue { account, amount } => ("Issue to", account, amount),
        Action::Trade { account, amount } => ("Trade from", account, amount),
    };
    let name = match account {
        Account::Alice => "Alice",
        Account::Bob => "Bob",
    };
    format!("{kind} {name}: {amount}")
}

fn render_case(out: &mut String, case: &CaseReport, output_root: &Path) {
    let (class, label) = status(case);
    write!(
        out,
        "<section class=\"case\"><header><h2>{}</h2><span class=\"badge {}\">{}</span></header>",
        escape(case.variant.as_str()),
        class,
        label
    )
    .unwrap();
    write!(out, "<div class=\"rules\"><div><h3>Original rule</h3><p>{}</p></div><div><h3>Rule variant</h3><p>{}</p></div></div>",
        escape(case.original_rule), escape(case.mutant_rule)).unwrap();
    write!(
        out,
        "<p class=\"metrics\">Search: {} · {} states · {} edges · {} ms · verifier {} ms</p>",
        escape(&case.search.termination),
        case.search.stats.nodes,
        case.search.stats.edges,
        case.search.stats.elapsed_ms,
        case.verifier_elapsed_ms
    )
    .unwrap();
    if class == "safe" {
        out.push_str("<p>Accepted by an independently checked general conservation theorem, not by the absence of a search result.</p>");
    }
    if let Some(candidate) = &case.search.candidate {
        let candidate_path = output_root
            .join("candidates")
            .join(format!("{}.json", case.variant.as_str()));
        if let Some(href) = evidence_href(output_root, &candidate_path) {
            write!(
                out,
                "<p><a href=\"{}\">Candidate JSON — recheck with scribe butterfly verify</a></p>",
                escape(&href)
            )
            .unwrap();
        }
        write!(out, "<h3>{} trace · {} actions</h3><p>Initial total: 8. All accounts, including reserve and fees, are counted.</p>",
            if class == "refuted" { "Checked" } else { "Candidate" }, candidate.actions.len()).unwrap();
        out.push_str("<div class=\"table-wrap\"><table><caption>State after each action. Highlight marks the first baseline divergence.</caption><thead><tr><th>Step</th><th>Action</th><th>Reserve</th><th>Alice</th><th>Bob</th><th>Treasury</th><th>Total</th></tr></thead><tbody>");
        for (index, state) in candidate.states.iter().enumerate() {
            let action = index
                .checked_sub(1)
                .and_then(|i| candidate.actions.get(i))
                .map(action_label)
                .unwrap_or_else(|| "Initial state".into());
            let divergence = index > 0 && index - 1 == candidate.baseline_divergence;
            let total = u64::from(state.reserve)
                + u64::from(state.alice)
                + u64::from(state.bob)
                + u64::from(state.treasury);
            write!(out, "<tr{}><td>{}</td><td>{}{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}{}</td></tr>",
                if divergence { " class=\"divergence\"" } else { "" }, index, escape(&action),
                if divergence { " — first divergence" } else { "" }, state.reserve, state.alice, state.bob, state.treasury, total,
                if total != 8 { " (violates conservation)" } else { "" }).unwrap();
        }
        out.push_str("</tbody></table></div>");
        let i = candidate.baseline_divergence;
        if let (Some(state), Some(action)) = (candidate.states.get(i), candidate.actions.get(i)) {
            let baseline = butterfly::step(Mutation::Baseline, *state, *action);
            let outcome = baseline
                .map(|next| {
                    format!(
                        "permits a different next state: reserve {}, Alice {}, Bob {}, treasury {}",
                        next.reserve, next.alice, next.bob, next.treasury
                    )
                })
                .unwrap_or_else(|| "rejects the action".into());
            write!(
                out,
                "<p><strong>Baseline at action {}:</strong> {}.</p>",
                i + 1,
                escape(&outcome)
            )
            .unwrap();
        }
        if class != "refuted" {
            out.push_str("<p class=\"caution\">This trace is a search proposal. It is not an accepted counterexample.</p>");
        }
    } else if class != "safe" {
        out.push_str("<p>No checked witness is available. This is not a proof of safety.</p>");
    }
    let (summary, details): (&str, &[String]) = match case.verdict.outcome() {
        Outcome::Accept(e) => (&e.summary, &e.details),
        Outcome::Reject(e) => (&e.summary, &e.details),
        Outcome::Undetermined(e) => (&e.summary, &[]),
    };
    write!(
        out,
        "<details><summary>Verification evidence</summary><p>{}</p><ul>",
        escape(summary)
    )
    .unwrap();
    for detail in details {
        // Recognized fixed metadata labels only; never interpret arbitrary text as a URL.
        let path = detail
            .strip_prefix("certificate: ")
            .or_else(|| detail.strip_prefix("source SHA-256 manifest: "));
        if let Some(href) = path.and_then(|p| evidence_href(output_root, Path::new(p))) {
            write!(
                out,
                "<li><a href=\"{}\">{}</a></li>",
                escape(&href),
                escape(detail)
            )
            .unwrap();
        } else {
            write!(out, "<li>{}</li>", escape(detail)).unwrap();
        }
    }
    out.push_str("</ul></details></section>");
}

/// Render a report without scripts, remote resources, or reading evidence contents.
/// `output_root` bounds optional local evidence links; it does not validate proofs.
pub fn render(report: &EvaluationReport, output_root: &Path) -> String {
    let mut out = String::from(
        r#"<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'"><title>Butterfly — checked rule-change experiment</title><style>
:root{color-scheme:light;--ink:#182537;--muted:#526176;--border:#dbe2eb}*{box-sizing:border-box}body{margin:0;background:#f4f6f9;color:var(--ink);font:16px/1.55 system-ui,sans-serif}main{max-width:1100px;margin:auto;padding:32px 20px 64px}h1{font-size:2.4rem;line-height:1.15}h2{font-size:1.25rem;margin:0}h3{font-size:1rem;margin:0 0 8px}p{margin:10px 0}.intro{max-width:850px}.eyebrow{font-size:.8rem;letter-spacing:.12em;text-transform:uppercase}.case{margin:24px 0;background:white;border:1px solid var(--border);border-radius:12px;padding:24px}header{display:flex;justify-content:space-between;gap:16px;align-items:center}.badge{font-size:.8rem;font-weight:650;padding:5px 10px;border-radius:6px}.refuted{background:#ffe2dc;color:#852a1a}.safe{background:#dff3e8;color:#17593b}.unknown{background:#fff0ca;color:#75520b}.rules{display:grid;grid-template-columns:1fr 1fr;gap:18px;margin-top:20px}.rules>div{background:#f4f6f9;padding:16px;border-radius:8px}.metrics{font-size:.85rem;color:var(--muted)}.table-wrap{overflow-x:auto}table{width:100%;border-collapse:collapse;font-size:.85rem;margin-top:12px}caption{text-align:left;color:var(--muted);padding-bottom:8px}th,td{text-align:left;padding:10px;border-bottom:1px solid var(--border)}th{background:#edf1f6}.divergence{background:#fff0ca}.caution{font-weight:650}details{margin-top:16px;font-size:.85rem}summary{cursor:pointer}li{overflow-wrap:anywhere}a{color:#174c92}.summary{padding:16px;background:#e9eef6;border-radius:8px}@media(max-width:650px){.rules{grid-template-columns:1fr}header{align-items:flex-start;flex-direction:column}.case{padding:16px}h1{font-size:1.9rem}}@media print{body{background:white}.case{break-inside:avoid}details{display:block}}
</style></head><body><main><p class="eyebrow">Scribe / Butterfly</p><h1>A changed rule.<br>A checked counterexample.</h1><p class="intro">A finite resource-trading experiment. Search proposes traces; Lean checks the exact rule variant, every transition, conservation violation, and baseline divergence. Safety labels require a separate general theorem.</p>"#,
    );
    // Summary counts come from consistent case verdicts, not merely labels.
    let checked = report
        .cases
        .iter()
        .filter(|c| status(c).0 == "refuted")
        .count();
    let safe = report
        .cases
        .iter()
        .filter(|c| status(c).0 == "safe")
        .count();
    write!(out, "<p class=\"summary\"><strong>{checked} checked counterexamples · {safe} checked conservation theorems</strong><br>{} safe-control false accusations. Corpus: {}.</p>", report.safe_false_accusations, escape(report.corpus_version)).unwrap();
    write!(out, "<p class=\"metrics\">Per-variant search bounds: depth {}, states {}, edges {}, time {} seconds. No API calls. Trace length and bounded search are observations, not certified minimality claims.</p>", report.budget.max_depth, report.budget.max_nodes, report.budget.max_edges, report.budget.max_duration.as_secs_f64()).unwrap();
    for case in &report.cases {
        render_case(&mut out, case, output_root);
    }
    out.push_str("<footer><h2>Scope and limits</h2><ul>");
    for limitation in &report.limitations {
        write!(out, "<li>{}</li>", escape(limitation)).unwrap();
    }
    out.push_str("</ul><p>Unknown within a budget never means safe. This report presents local evidence; it is not itself an independently verified receipt.</p></footer></main></body></html>");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use butterfly::{CandidateWitness, CheckResult, SearchBudget, WitnessChecker};
    struct Offline;
    impl WitnessChecker for Offline {
        fn check(&self, _: &CandidateWitness) -> CheckResult {
            CheckResult::Unavailable("<script>alert('x')</script> & \"unavailable\"".into())
        }
    }
    #[test]
    fn escapes_dynamic_text_and_keeps_candidates_unverified() {
        let report = butterfly::evaluate(&Offline, SearchBudget::default());
        let html = render(&report, Path::new("/nonexistent"));
        assert!(!html.contains("<script>"));
        assert!(html.contains("&lt;script&gt;"));
        assert!(html.contains("Verification unavailable"));
        assert!(!html.contains("class=\"badge refuted\""));
        assert!(html.contains("first divergence"));
        assert!(html.contains("rejects the action"));
        assert!(html.contains("not an accepted counterexample"));
        assert!(html.contains("0 checked counterexamples"));
    }
    #[test]
    fn safe_status_requires_matching_core_acceptance() {
        let mut report = butterfly::evaluate(&Offline, SearchBudget::default());
        report.cases[0].verification_status = "checked_safe";
        assert!(!render(&report, Path::new("/nonexistent")).contains("class=\"badge safe\""));
        let discrimination = report.cases[0].verdict.discrimination().clone();
        report.cases[0].verdict = scribe_core::Verdict::new(
            Outcome::Accept(scribe_core::Evidence {
                summary: "Checked general theorem".into(),
                details: vec![],
            }),
            discrimination,
        );
        let html = render(&report, Path::new("/nonexistent"));
        assert!(html.contains("class=\"badge safe\""));
        assert!(html.contains("not by the absence of a search result"));
        assert!(html.contains("1 checked conservation theorems"));
    }

    #[test]
    fn evidence_links_are_contained_and_uri_encoded() {
        let root = std::env::temp_dir().join(format!("butterfly-html-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join("a #\".lean");
        std::fs::write(&path, "fixture").unwrap();
        assert_eq!(
            evidence_href(&root, &path),
            Some("./a%20%23%22.lean".into())
        );
        assert_eq!(evidence_href(&root, Path::new("/etc/hosts")), None);
        assert_eq!(evidence_href(&root, &root.join("../absent")), None);
        std::fs::remove_file(path).unwrap();
        std::fs::remove_dir(root).unwrap();
    }
    #[test]
    fn escaping_covers_attribute_delimiters() {
        assert_eq!(escape("<&>\"'"), "&lt;&amp;&gt;&quot;&#39;");
    }
}
