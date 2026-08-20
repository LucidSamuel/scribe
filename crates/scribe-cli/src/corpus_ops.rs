//! D5 — corpus tooling: `scribe corpus validate` and `scribe corpus add`.
//!
//! The corpus is load-bearing (locked decision 5): it is the evidence behind
//! every verdict the oracle issues, it is versioned, and it grows
//! monotonically — a confirmed real-world bug becomes a permanent entry via
//! `corpus add`. `corpus validate` runs `scribe_core::validate()` over it and
//! renders the `DiscriminationReport` with **escapes as alarms**, not table
//! rows: an escaped negative means the oracle accepted something known to be
//! wrong, and every verdict it has ever issued is suspect.

use std::path::{Path, PathBuf};
use std::process;

use oracle_lean::{CircuitCorpus, CommittedValidation, LeanOracle};
use proof_pilot::backend::make_backend;
use scribe_core::{Corpus, DiscriminationReport};

use crate::corpus_cmd::{AddArgs, CorpusAction, CorpusArgs, ValidateArgs};

/// Exit codes, following the judge convention: 0 = the oracle discriminates
/// cleanly, 1 = no escapes but discrimination is incomplete (uncaught
/// negatives via budget exhaustion, or unaccepted positives), 2 = at least
/// one ESCAPE (soundness alarm), 3 = infrastructure error.
const EXIT_CLEAN: i32 = 0;
const EXIT_INCOMPLETE: i32 = 1;
const EXIT_ESCAPE: i32 = 2;
const EXIT_INFRA: i32 = 3;

pub fn run_corpus(args: CorpusArgs) {
    match args.action {
        CorpusAction::Validate(v) => run_validate(v),
        CorpusAction::Add(a) => run_add(a),
    }
}

// ─── corpus validate ─────────────────────────────────────────────────────────

fn run_validate(args: ValidateArgs) {
    let dir = PathBuf::from(&args.corpus);
    let corpus = CircuitCorpus::load(&dir).unwrap_or_else(|e| {
        eprintln!("error: {e}");
        process::exit(EXIT_INFRA);
    });

    let negatives = corpus.negatives().len();
    let positives = corpus.positives().len();
    eprintln!(
        "[scribe corpus] {} — {} instance(s): {} negative, {} positive",
        corpus.version(),
        negatives + positives,
        negatives,
        positives
    );
    for (entry, _) in corpus.entries() {
        eprintln!("    {:<10} {:<34} {}", entry.kind, entry.id, entry.file);
    }

    let out = args
        .out
        .clone()
        .unwrap_or_else(|| dir.join("discrimination-report.json").display().to_string());

    if args.dry_run {
        // The free tier: show the corpus and the committed evidence, spend
        // nothing. A committed report is only evidence for the corpus it
        // actually measured — the fingerprint binds the two, and a report
        // that does not match the corpus on disk is stale, not clean.
        match CommittedValidation::load(Path::new(&out)) {
            Ok(committed) => {
                if let Err(why) = committed_matches_corpus(&committed, &corpus) {
                    eprintln!("[scribe corpus] committed validation is STALE: {why}");
                    eprintln!(
                        "[scribe corpus] the oracle is UNMEASURED against this corpus — run \
                         without --dry-run to re-measure it"
                    );
                    process::exit(EXIT_INCOMPLETE);
                }
                eprintln!(
                    "[scribe corpus] committed validation ({}, {}):",
                    committed.generated, committed.oracle
                );
                eprint!("{}", render_report(&committed.report));
                process::exit(report_exit_code(&committed.report));
            }
            Err(e) => {
                eprintln!("[scribe corpus] no committed validation ({e})");
                eprintln!(
                    "[scribe corpus] the oracle is UNMEASURED against this corpus — run \
                     without --dry-run to measure it"
                );
                process::exit(EXIT_INCOMPLETE);
            }
        }
    }

    let backend = make_backend(
        &args.backend,
        args.model.clone(),
        args.api_key.clone(),
        args.base_url.clone(),
    )
    .unwrap_or_else(|e| {
        eprintln!("error: {e}");
        process::exit(EXIT_INFRA);
    });

    let lake_dir = crate::orchestrate::resolve_lake_dir(args.lake_dir.as_deref());
    let prompts_dir = std::env::var("SCRIBE_PROMPTS_DIR").unwrap_or_else(|_| "prompts".to_string());
    let oracle = LeanOracle::new(&lake_dir, backend)
        .with_prompts_dir(Path::new(&prompts_dir))
        .with_budgets(args.prove_iters, args.refute_iters);
    let oracle_desc = format!(
        "LeanOracle over {} (prove-then-refute)",
        oracle.backend_name()
    );
    eprintln!(
        "[scribe corpus] validating with {oracle_desc}, prove {} / refute {} iteration(s) — \
         this runs the LLM loop once per instance",
        args.prove_iters, args.refute_iters
    );

    let report = scribe_core::validate(&oracle, &corpus);
    eprint!("{}", render_report(&report));

    let committed = CommittedValidation {
        generated: format!(
            "unix:{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0)
        ),
        oracle: oracle_desc,
        prove_iters: args.prove_iters,
        refute_iters: args.refute_iters,
        corpus_fingerprint: Some(corpus.content_fingerprint()),
        report: report.clone(),
    };
    match committed.save(Path::new(&out)) {
        Ok(()) => eprintln!("[scribe corpus] report committed to {out} — it is the evidence"),
        Err(e) => {
            eprintln!("error: could not write {out}: {e}");
            process::exit(EXIT_INFRA);
        }
    }
    process::exit(report_exit_code(&report));
}

/// Does a committed validation describe the corpus as it exists on disk?
/// The binding is the corpus content fingerprint; a report without one (or
/// with a stale one) is evidence about some *other* corpus, and trusting it
/// would let an unmeasured instance ride under old clean numbers.
fn committed_matches_corpus(
    committed: &CommittedValidation,
    corpus: &CircuitCorpus,
) -> Result<(), String> {
    let current = corpus.content_fingerprint();
    match committed.corpus_fingerprint.as_deref() {
        Some(fp) if fp == current => Ok(()),
        Some(fp) => Err(format!(
            "its corpus fingerprint {fp} does not match the corpus on disk ({current}) — \
             some instance was added, removed, re-kinded, or semantically edited since the run"
        )),
        None => Err(format!(
            "it predates corpus fingerprinting (expected {current}) — there is no way to \
             tell which corpus it measured"
        )),
    }
}

/// Render a report with escapes as ALARMS. An escape is the loudest signal
/// the system can produce; it leads, it is not a table row.
fn render_report(report: &DiscriminationReport) -> String {
    let mut out = String::new();
    for id in &report.escaped {
        out.push_str(&format!(
            "\n  ⚠ SOUNDNESS ALARM — ESCAPE: the oracle ACCEPTED known-bad instance {id}.\n\
             \x20   Every verdict this oracle has issued is suspect until this is explained.\n"
        ));
    }
    if !report.escaped.is_empty() {
        out.push('\n');
    }
    out.push_str(&format!(
        "  negatives caught:   {}/{}\n  positives accepted: {}/{}\n  corpus:             {}\n",
        report.negatives_caught,
        report.negatives_total,
        report.positives_accepted,
        report.positives_total,
        report.corpus_version,
    ));
    let uncaught = report.negatives_total - report.negatives_caught - report.escaped.len();
    if uncaught > 0 {
        out.push_str(&format!(
            "  ({uncaught} negative(s) neither caught nor escaped — refuter budget exhausted; \
             not an escape, but not discrimination either)\n"
        ));
    }
    out
}

fn report_exit_code(report: &DiscriminationReport) -> i32 {
    if !report.escaped.is_empty() {
        EXIT_ESCAPE
    } else if report.negatives_caught < report.negatives_total
        || report.positives_accepted < report.positives_total
    {
        EXIT_INCOMPLETE
    } else {
        EXIT_CLEAN
    }
}

// ─── corpus add ──────────────────────────────────────────────────────────────

fn run_add(args: AddArgs) {
    let dir = PathBuf::from(&args.corpus);
    match add_instance(&dir, &args) {
        Ok(dest) => {
            eprintln!(
                "[scribe corpus] added {:?} ({}) as {} — the corpus grows monotonically; \
                 this entry is permanent evidence",
                args.id,
                args.kind,
                dest.display()
            );
            eprintln!(
                "[scribe corpus] the committed discrimination report predates this instance — \
                 re-run `scribe corpus validate` to re-measure the oracle against it"
            );
        }
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(EXIT_INFRA);
        }
    }
}

/// Validate and append a new instance: the IR must load and carry a spec, the
/// id must be new, the file lands inside the corpus dir, and the manifest
/// gains an `[[instances]]` block. The corpus is reloaded afterwards as a
/// self-check; on failure the manifest is restored byte-for-byte.
fn add_instance(dir: &Path, args: &AddArgs) -> Result<PathBuf, String> {
    if args.kind != "negative" && args.kind != "positive" {
        return Err(format!(
            "kind must be \"negative\" or \"positive\", got {:?}",
            args.kind
        ));
    }
    for (what, s) in [("id", &args.id), ("note", &args.note)] {
        if s.contains('"') || s.contains('\\') || s.contains('\n') {
            return Err(format!(
                "{what} must not contain quotes, backslashes, or newlines"
            ));
        }
    }

    let corpus = CircuitCorpus::load(dir).map_err(|e| e.to_string())?;
    if corpus.entries().iter().any(|(e, _)| e.id == args.id) {
        return Err(format!(
            "id {:?} already exists in the corpus — corpus entries are permanent; pick a new id",
            args.id
        ));
    }

    // The same loading rules CircuitCorpus::load applies, including the
    // spec requirement: a negative without a spec can never be caught, a
    // positive without one proves nothing.
    let src = PathBuf::from(&args.file);
    let ir = if src.extension().and_then(|e| e.to_str()) == Some("json") {
        let raw = std::fs::read_to_string(&src)
            .map_err(|e| format!("cannot read {}: {e}", src.display()))?;
        circuit_ir::CircuitIR::from_json(&raw).map_err(|e| e.to_string())?
    } else {
        circuit_ir::load_toml_file(&src).map_err(|e| e.to_string())?
    };
    if ir.soundness_spec.is_none() {
        return Err(format!(
            "{} has no soundness_spec — there is no claim for the oracle to adjudicate; \
             a spec-less {} cannot ever be {}",
            src.display(),
            args.kind,
            if args.kind == "negative" {
                "caught"
            } else {
                "accepted"
            }
        ));
    }

    // Build the full manifest block BEFORE touching the corpus dir, so every
    // metadata validation (including origin) happens while there is still
    // nothing to roll back.
    let basename = src
        .file_name()
        .ok_or_else(|| format!("{} has no file name", src.display()))?;
    let mut block = format!(
        "\n[[instances]]\nid = \"{}\"\nkind = \"{}\"\nfile = \"{}\"\n",
        args.id,
        args.kind,
        basename.to_string_lossy()
    );
    if let Some(origin) = &args.origin {
        if origin.contains('"') || origin.contains('\\') || origin.contains('\n') {
            return Err("origin must not contain quotes, backslashes, or newlines".into());
        }
        block.push_str(&format!("origin = \"{origin}\"\n"));
    }
    block.push_str(&format!("note = \"{}\"\n", args.note));

    let manifest_path = dir.join("corpus.toml");
    let original = std::fs::read_to_string(&manifest_path)
        .map_err(|e| format!("cannot read {}: {e}", manifest_path.display()))?;

    let dest = dir.join(basename);
    let src_bytes =
        std::fs::read(&src).map_err(|e| format!("cannot read {}: {e}", src.display()))?;
    let mut created_dest = false;
    if dest.exists() {
        let dest_bytes =
            std::fs::read(&dest).map_err(|e| format!("cannot read {}: {e}", dest.display()))?;
        if dest_bytes != src_bytes {
            return Err(format!(
                "{} already exists with different content — corpus files are immutable \
                 evidence; use a new file name",
                dest.display()
            ));
        }
    } else {
        std::fs::write(&dest, &src_bytes)
            .map_err(|e| format!("cannot write {}: {e}", dest.display()))?;
        created_dest = true;
    }
    // Undo everything this call created, leaving the corpus dir as found.
    // Pre-existing files are never removed: they are someone else's evidence.
    let roll_back = |manifest_written: bool| {
        if manifest_written {
            let _ = std::fs::write(&manifest_path, &original);
        }
        if created_dest {
            let _ = std::fs::remove_file(&dest);
        }
    };

    if let Err(e) = std::fs::write(&manifest_path, format!("{original}{block}")) {
        roll_back(false);
        return Err(format!("cannot write {}: {e}", manifest_path.display()));
    }

    // Self-check: the grown corpus must load cleanly, or we roll back.
    if let Err(e) = CircuitCorpus::load(dir) {
        roll_back(true);
        return Err(format!(
            "the corpus no longer loads after adding {:?} (rolled back): {e}",
            args.id
        ));
    }
    Ok(dest)
}

#[cfg(test)]
mod tests {
    use super::*;
    use scribe_core::InstanceId;

    fn tmp_corpus() -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "scribe-corpus-test-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("corpus.toml"),
            "version = \"test-corpus-v1\"\n\n[[instances]]\nid = \"pos-seed\"\nkind = \"positive\"\nfile = \"seed.toml\"\nnote = \"seed\"\n",
        )
        .unwrap();
        std::fs::write(dir.join("seed.toml"), GADGET).unwrap();
        dir
    }

    const GADGET: &str = "name = \"seed\"\nmodulus = \"17\"\nsoundness_spec = \"x = 0\"\n\n\
                          [[witnesses]]\nid = 0\nname = \"x\"\n\n\
                          [[constraints]]\nlabel = \"c\"\nterms = [{ coeff = \"1\", vars = [0] }]\n";

    fn add_args(dir: &Path, id: &str, file: &Path, kind: &str) -> AddArgs {
        AddArgs {
            corpus: dir.display().to_string(),
            file: file.display().to_string(),
            id: id.to_string(),
            kind: kind.to_string(),
            note: "a confirmed bug".to_string(),
            origin: Some("test".to_string()),
        }
    }

    #[test]
    fn add_appends_and_corpus_reloads() {
        let dir = tmp_corpus();
        let src = dir.join("newbug.toml");
        std::fs::write(&src, GADGET.replace("\"seed\"", "\"newbug\"")).unwrap();

        add_instance(&dir, &add_args(&dir, "neg-new-bug", &src, "negative")).unwrap();

        let corpus = CircuitCorpus::load(&dir).unwrap();
        assert_eq!(corpus.entries().len(), 2);
        assert_eq!(corpus.negatives().len(), 1);
        assert_eq!(corpus.negatives()[0].id, InstanceId::from("neg-new-bug"));
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn add_rejects_duplicate_ids_and_spec_less_irs() {
        let dir = tmp_corpus();
        let src = dir.join("newbug.toml");
        std::fs::write(&src, GADGET).unwrap();

        let err = add_instance(&dir, &add_args(&dir, "pos-seed", &src, "positive")).unwrap_err();
        assert!(err.contains("already exists"), "{err}");

        let specless = dir.join("specless.toml");
        std::fs::write(
            &specless,
            GADGET.replace("soundness_spec = \"x = 0\"\n", ""),
        )
        .unwrap();
        let err =
            add_instance(&dir, &add_args(&dir, "neg-specless", &specless, "negative")).unwrap_err();
        assert!(err.contains("no soundness_spec"), "{err}");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn add_never_overwrites_existing_evidence() {
        let dir = tmp_corpus();
        let elsewhere =
            std::env::temp_dir().join(format!("seed-clash-{}.toml", std::process::id()));
        std::fs::write(&elsewhere, GADGET.replace("x = 0", "x = 1")).unwrap();
        // same basename as the seed instance's file, different content
        let renamed = elsewhere.parent().unwrap().join("seed.toml");
        std::fs::copy(&elsewhere, &renamed).unwrap();

        let err =
            add_instance(&dir, &add_args(&dir, "neg-clash", &renamed, "negative")).unwrap_err();
        assert!(err.contains("different content"), "{err}");
        std::fs::remove_dir_all(&dir).ok();
        std::fs::remove_file(&elsewhere).ok();
        std::fs::remove_file(&renamed).ok();
    }

    #[test]
    fn add_validates_all_metadata_before_creating_any_file() {
        let dir = tmp_corpus();
        let src = dir.join("newbug.toml");
        std::fs::write(&src, GADGET.replace("\"seed\"", "\"newbug\"")).unwrap();
        let manifest_before = std::fs::read_to_string(dir.join("corpus.toml")).unwrap();

        let mut args = add_args(&dir, "neg-bad-origin", &src, "negative");
        args.origin = Some("has a \" quote".to_string());
        // The source file has the same basename inside the corpus dir already
        // (we wrote it there), so use a distinct destination check: point at a
        // file outside the corpus dir.
        let outside = std::env::temp_dir().join(format!("outside-{}.toml", std::process::id()));
        std::fs::write(&outside, GADGET.replace("\"seed\"", "\"newbug\"")).unwrap();
        args.file = outside.display().to_string();

        let err = add_instance(&dir, &args).unwrap_err();
        assert!(err.contains("origin"), "{err}");
        // Nothing was created and the manifest is untouched: metadata failed
        // validation before any write.
        assert!(!dir.join(outside.file_name().unwrap()).exists());
        assert_eq!(
            std::fs::read_to_string(dir.join("corpus.toml")).unwrap(),
            manifest_before
        );
        std::fs::remove_dir_all(&dir).ok();
        std::fs::remove_file(&outside).ok();
    }

    #[test]
    fn stale_or_missing_fingerprint_is_not_trusted() {
        let dir = tmp_corpus();
        let corpus = CircuitCorpus::load(&dir).unwrap();
        let committed = |fp: Option<String>| CommittedValidation {
            generated: "unix:0".into(),
            oracle: "test".into(),
            prove_iters: 1,
            refute_iters: 1,
            corpus_fingerprint: fp,
            report: DiscriminationReport {
                corpus_version: "test-corpus-v1".into(),
                negatives_caught: 0,
                negatives_total: 0,
                escaped: vec![],
                positives_accepted: 1,
                positives_total: 1,
            },
        };

        // Pre-fingerprint reports and mismatched fingerprints are both stale.
        let err = committed_matches_corpus(&committed(None), &corpus).unwrap_err();
        assert!(err.contains("predates corpus fingerprinting"), "{err}");
        let err =
            committed_matches_corpus(&committed(Some("deadbeef".into())), &corpus).unwrap_err();
        assert!(err.contains("does not match"), "{err}");

        // The matching fingerprint is the only trusted state.
        committed_matches_corpus(&committed(Some(corpus.content_fingerprint())), &corpus).unwrap();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn escapes_render_as_alarms_and_drive_exit_2() {
        let report = DiscriminationReport {
            corpus_version: "v1".into(),
            negatives_caught: 4,
            negatives_total: 5,
            escaped: vec![InstanceId::from("neg-bad")],
            positives_accepted: 3,
            positives_total: 3,
        };
        let rendered = render_report(&report);
        assert!(rendered.contains("SOUNDNESS ALARM — ESCAPE"), "{rendered}");
        assert!(rendered.contains("neg-bad"));
        // the alarm leads; the counts follow
        assert!(rendered.find("ALARM").unwrap() < rendered.find("negatives caught").unwrap());
        assert_eq!(report_exit_code(&report), 2);
    }

    #[test]
    fn exit_codes_follow_the_judge_convention() {
        let clean = DiscriminationReport {
            corpus_version: "v1".into(),
            negatives_caught: 5,
            negatives_total: 5,
            escaped: vec![],
            positives_accepted: 3,
            positives_total: 3,
        };
        assert_eq!(report_exit_code(&clean), 0);

        let incomplete = DiscriminationReport {
            negatives_caught: 4,
            ..clean.clone()
        };
        assert_eq!(report_exit_code(&incomplete), 1);
        let rendered = render_report(&incomplete);
        assert!(rendered.contains("neither caught nor escaped"));
    }
}
