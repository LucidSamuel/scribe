//! Human-facing surface for the bounded, checked Butterfly experiment.
use clap::{Args, Subcommand};
use std::{fs, io::Read, path::PathBuf, time::Duration};

#[derive(Args)]
pub struct ButterflyArgs {
    #[command(subcommand)]
    command: ButterflyCommand,
}

#[derive(Subcommand)]
enum ButterflyCommand {
    /// Search the bundled trading model and display a candidate trace with its verdict.
    Demo(RunArgs),
    /// Evaluate all bundled harmful, harmless, and unreachable variants.
    Evaluate(RunArgs),
    /// Recheck a typed candidate JSON file; accepts no arbitrary Lean proof text.
    Verify {
        #[arg(long)]
        candidate: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long, default_value = "lean")]
        lake_dir: PathBuf,
        #[arg(long, default_value_t = 120)]
        check_seconds: u64,
    },
}

#[derive(Args)]
struct RunArgs {
    /// New directory for the report and Lean verification evidence.
    #[arg(long)]
    output: PathBuf,
    /// Trusted local Lake project containing the bundled Butterfly model.
    #[arg(long, default_value = "lean")]
    lake_dir: PathBuf,
    #[arg(long, default_value_t = 6)]
    max_depth: usize,
    #[arg(long, default_value_t = 20000)]
    max_nodes: usize,
    #[arg(long, default_value_t = 500000)]
    max_edges: usize,
    /// Wall-clock limit per variant's search.
    #[arg(long, default_value_t = 10)]
    seconds: u64,
    /// Wall-clock limit per Lean verification.
    #[arg(long, default_value_t = 120)]
    check_seconds: u64,
}

fn summary(report: &serde_json::Value, detail: bool) -> String {
    let mut text = String::from(
        "Butterfly — bounded resource-trading experiment\n\n\
        Search observations and verification verdicts are separate.\n\
        No witness within a budget is UNKNOWN, never a safety proof.\n\n",
    );
    if let Some(cases) = report["cases"].as_array() {
        for case in cases {
            let outcome = case["verdict"]["outcome"]
                .as_object()
                .and_then(|object| object.keys().next())
                .map(String::as_str)
                .unwrap_or("Undetermined");
            text.push_str(&format!(
                "{}\n  verification: {}\n  conservation verdict: {}\n  search: {}\n  cost: {}\n",
                case["variant"].as_str().unwrap_or("unknown variant"),
                case["verification_status"],
                outcome,
                case["search"]["termination"],
                case["search"]["stats"]
            ));
            if detail && !case["search"]["candidate"].is_null() {
                let variant: Option<butterfly::Mutation> =
                    serde_json::from_value(case["variant"].clone()).ok();
                text.push_str("  original: amount < balance; debit amount + 1; recipient + amount; treasury + 1\n");
                if let Some(variant) = variant {
                    text.push_str(&format!("  mutation: {}\n", variant.description()));
                }
                text.push_str("  candidate trace (consult verdict before treating as checked):\n");
                let candidate = &case["search"]["candidate"];
                text.push_str("  step | action | reserve | alice | bob | treasury | total\n");
                if let Some(states) = candidate["states"].as_array() {
                    for (index, state) in states.iter().enumerate() {
                        let action = if index == 0 {
                            "initial".to_string()
                        } else {
                            candidate["actions"][index - 1].to_string()
                        };
                        let total: u64 = ["reserve", "alice", "bob", "treasury"]
                            .iter()
                            .filter_map(|k| state[k].as_u64())
                            .sum();
                        text.push_str(&format!(
                            "  {index} | {action} | {} | {} | {} | {} | {total}\n",
                            state["reserve"], state["alice"], state["bob"], state["treasury"]
                        ));
                    }
                }
                text.push_str(&format!(
                    "  baseline first differs at action {} (zero-based).\n",
                    candidate["baseline_divergence"]
                ));
                if let Ok(candidate) =
                    serde_json::from_value::<butterfly::CandidateWitness>(candidate.clone())
                {
                    let i = candidate.baseline_divergence;
                    if let (Some(state), Some(action)) =
                        (candidate.states.get(i), candidate.actions.get(i))
                    {
                        match butterfly::step(butterfly::Mutation::Baseline, *state, *action) {
                            None => text.push_str("  baseline outcome at divergence: REJECTED (trade cannot proceed).\n"),
                            Some(next) => text.push_str(&format!("  baseline outcome at divergence: {}\n", serde_json::to_string(&next).unwrap())),
                        }
                    }
                }
            }
            text.push('\n');
        }
    }
    text.push_str(&format!(
        "Checked witnesses: {}\nSafe-control false accusations: {}\n",
        report["checked_witnesses"], report["safe_false_accusations"]
    ));
    text
}

fn execute(args: RunArgs, detail: bool) -> Result<(), String> {
    if args.seconds == 0 || args.check_seconds == 0 || args.max_nodes == 0 || args.max_edges == 0 {
        return Err("time, node and edge budgets must be positive".into());
    }
    // Never let stale receipts from an earlier experiment accompany a new report.
    fs::create_dir(&args.output)
        .map_err(|e| format!("create new output directory {}: {e}", args.output.display()))?;
    let checker = butterfly::LeanChecker::new(
        args.lake_dir,
        args.output.clone(),
        Duration::from_secs(args.check_seconds),
    );
    let budget = butterfly::SearchBudget {
        max_depth: args.max_depth,
        max_nodes: args.max_nodes,
        max_edges: args.max_edges,
        max_duration: Duration::from_secs(args.seconds),
    };
    let report = butterfly::evaluate(&checker, budget);
    let candidates = args.output.join("candidates");
    fs::create_dir(&candidates).map_err(|e| e.to_string())?;
    for case in &report.cases {
        if let Some(candidate) = &case.search.candidate {
            fs::write(
                candidates.join(format!("{}.json", case.variant.as_str())),
                serde_json::to_vec_pretty(candidate).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?;
        }
    }
    fs::write(
        args.output.join("report.html"),
        crate::butterfly_report::render(&report, &args.output),
    )
    .map_err(|e| e.to_string())?;
    let value = serde_json::to_value(&report).map_err(|e| e.to_string())?;
    let rendered = summary(&value, detail);
    fs::write(
        args.output.join("report.json"),
        serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    fs::write(args.output.join("summary.txt"), &rendered).map_err(|e| e.to_string())?;
    print!("{rendered}");
    println!(
        "Evidence: {}\nOpen report: {}",
        args.output.display(),
        args.output.join("report.html").display()
    );
    if value["cases"].as_array().is_some_and(|cases| {
        cases
            .iter()
            .any(|case| case["verification_status"] == "unavailable")
    }) {
        return Err("one or more verification checks were unavailable; see saved report".into());
    }
    Ok(())
}

pub fn run(args: ButterflyArgs) -> i32 {
    let result = match args.command {
        ButterflyCommand::Demo(args) => execute(args, true),
        ButterflyCommand::Evaluate(args) => execute(args, false),
        ButterflyCommand::Verify {
            candidate,
            output,
            lake_dir,
            check_seconds,
        } => verify(candidate, output, lake_dir, check_seconds),
    };
    match result {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Butterfly: {error}");
            3
        }
    }
}

fn verify(
    candidate: PathBuf,
    output: PathBuf,
    lake_dir: PathBuf,
    seconds: u64,
) -> Result<(), String> {
    use butterfly::WitnessChecker;
    if seconds == 0 {
        return Err("verification time budget must be positive".into());
    }
    let mut bytes = Vec::new();
    fs::File::open(candidate)
        .map_err(|e| e.to_string())?
        .take(1024 * 1024 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > 1024 * 1024 {
        return Err("candidate exceeds 1 MiB limit".into());
    }
    let candidate: butterfly::CandidateWitness =
        serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    fs::create_dir(&output).map_err(|e| format!("create new output directory: {e}"))?;
    let checker =
        butterfly::LeanChecker::new(lake_dir, output.clone(), Duration::from_secs(seconds));
    let (status, details) = match checker.check(&candidate) {
        butterfly::CheckResult::Verified(evidence) => (
            "checked",
            serde_json::to_value(evidence).map_err(|e| e.to_string())?,
        ),
        butterfly::CheckResult::Invalid(error) => ("rejected", serde_json::json!({"error": error})),
        butterfly::CheckResult::Unavailable(error) => {
            ("unavailable", serde_json::json!({"error": error}))
        }
    };
    let report = serde_json::json!({"schema_version": 1, "verification_status": status, "candidate": candidate, "details": details});
    fs::write(
        output.join("report.json"),
        serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    println!("Verification: {status}\nEvidence: {}", output.display());
    if status != "checked" {
        return Err(format!("candidate verification {status}"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unchecked_candidates_are_not_rendered_as_checked() {
        let report = serde_json::json!({"cases": [{"variant": "duplicate_credit", "verdict": "unknown", "search": {"termination": "witness_found", "stats": {}, "candidate": {"actions": []}}}], "checked_witnesses": 0, "safe_false_accusations": 0});
        let text = summary(&report, true);
        assert!(text.contains("consult verdict"));
        assert!(text.contains("Checked witnesses: 0"));
        assert!(text.contains("never a safety proof"));
    }
}
