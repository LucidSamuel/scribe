use clap::{Args, Subcommand};
use scribe_claim::{ClaimPackage, Trust};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Args)]
pub struct ClaimArgs {
    #[command(subcommand)]
    command: ClaimCommand,
}

#[derive(Subcommand)]
enum ClaimCommand {
    /// Write a sealed JSON envelope to stdout. This is not a proof verdict.
    Seal {
        #[arg(long)]
        package: PathBuf,
        #[arg(long)]
        root: PathBuf,
    },
    /// Bind statements to Lean theorems and check their actual axioms.
    /// Runs trusted local Lean code; does not verify heuristics or costs.
    Verify {
        #[arg(long)]
        package: PathBuf,
        #[arg(long)]
        root: PathBuf,
        #[arg(long, default_value = "lean")]
        lake_dir: PathBuf,
    },
}

fn read_package(path: &Path) -> Result<ClaimPackage, String> {
    serde_json::from_slice(&fs::read(path).map_err(|e| e.to_string())?).map_err(|e| e.to_string())
}

// Restrict module paths used in generated import commands.
fn module_name(root: &Path, source: &Path) -> Result<String, String> {
    let source = source.canonicalize().map_err(|e| e.to_string())?;
    let relative = source
        .strip_prefix(root)
        .map_err(|_| "proof must be inside Lake project")?;
    if relative.extension().is_none_or(|ext| ext != "lean") {
        return Err("proof must be a Lean source file".into());
    }
    let stem = relative.with_extension("");
    let parts: Vec<_> = stem.iter().map(|s| s.to_string_lossy()).collect();
    if parts.iter().any(|s| {
        s.is_empty()
            || !s.as_bytes()[0].is_ascii_alphabetic()
            || !s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
    }) {
        return Err("proof module path must use ASCII Lean identifiers".into());
    }
    Ok(parts.join("."))
}

fn lean_string(value: &str) -> String {
    // JSON and Lean share these escapes; reject other controls at the boundary.
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn run_lake(lake: &Path, args: &[&str]) -> Result<String, String> {
    let result = Command::new("lake")
        .args(args)
        .current_dir(lake)
        .output()
        .map_err(|e| format!("cannot run lake: {e}"))?;
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    if !result.status.success() {
        return Err(format!("Lean verification failed:\n{log}"));
    }
    Ok(log)
}

fn verify(package: ClaimPackage, root: &Path, lake: &Path) -> Result<serde_json::Value, String> {
    let sealed = package.clone().seal(root)?;
    let lake = lake.canonicalize().map_err(|e| e.to_string())?;
    let toolchain = fs::read_to_string(lake.join("lean-toolchain")).map_err(|e| e.to_string())?;
    if package.toolchain != toolchain.trim() {
        return Err("package toolchain must equal the project's lean-toolchain".into());
    }
    let lake_str = lake.to_str().ok_or("non-UTF8 Lake path")?;
    let environment = crate::cache::environment_fingerprint(lake_str).map_err(|e| e.to_string())?;
    let mut probe = String::from("import ZkGadgets.ClaimAudit\n");
    let mut modules = std::collections::BTreeSet::new();
    for p in &package.propositions {
        if matches!(p.trust, Trust::NativeDecide) {
            return Err(
                "native_decide claims are not supported by the kernel-only verifier".into(),
            );
        }
        for value in std::iter::once(&p.declaration)
            .chain(std::iter::once(&p.statement))
            .chain(p.axioms.iter())
        {
            if value
                .chars()
                .any(|c| c.is_control() && !matches!(c, '\n' | '\r' | '\t'))
            {
                return Err("claim strings contain unsupported control characters".into());
            }
        }
        if p.axioms
            .iter()
            .any(|a| !["propext", "Classical.choice", "Quot.sound"].contains(&a.as_str()))
        {
            return Err("declared axioms must belong to the kernel trust allowlist".into());
        }
        modules.insert(module_name(
            &lake,
            &root.join(&package.artifacts[&p.artifact_id].path),
        )?);
    }
    let mut transcript = run_lake(&lake, &["build", "ZkGadgets.ClaimAudit"])?;
    for module in modules {
        transcript.push_str(&run_lake(&lake, &["build", &module])?);
        probe.push_str(&format!("import {module}\n"));
    }
    for p in &package.propositions {
        probe.push_str(&format!(
            "#audit_claim {} {} {}\n",
            lean_string(&p.declaration),
            lean_string(&p.statement),
            lean_string(&p.axioms.join(","))
        ));
    }
    // A fresh directory prevents concurrent invocations from sharing probes.
    let scratch = lake.join("ZkGadgets/Bench");
    fs::create_dir_all(&scratch).map_err(|e| e.to_string())?;
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    let dir = scratch.join(format!("Claim{}_{nonce}", std::process::id()));
    fs::create_dir(&dir).map_err(|e| e.to_string())?;
    let file = dir.join("Probe.lean");
    let result = (|| {
        fs::write(&file, &probe).map_err(|e| e.to_string())?;
        run_lake(
            &lake,
            &["env", "lean", file.to_str().ok_or("non-UTF8 probe path")?],
        )
    })();
    let _ = fs::remove_dir_all(&dir);
    transcript.push_str(&result?);
    // Refuse receipts when inputs drifted during the check.
    package.clone().seal(root)?;
    if environment != crate::cache::environment_fingerprint(lake_str).map_err(|e| e.to_string())? {
        return Err("Lean environment changed during verification".into());
    }
    Ok(serde_json::json!({
        "sealed_package": sealed,
        "verification": {
            "kind": "lean_statement_and_axiom_check_v1",
            "environment_sha256": environment,
            "toolchain": toolchain.trim(),
            "probe": probe,
            "transcript": transcript,
            "declarations": package.propositions.iter().map(|p| &p.declaration).collect::<Vec<_>>(),
            "scope": "Theorem statement binding and allowed axioms only; heuristics and costs are not verified."
        }
    }))
}

pub fn run(args: ClaimArgs) {
    let result = (|| -> Result<serde_json::Value, String> {
        match args.command {
            ClaimCommand::Seal { package, root } => {
                serde_json::to_value(read_package(&package)?.seal(&root)?)
                    .map_err(|e| e.to_string())
            }
            ClaimCommand::Verify {
                package,
                root,
                lake_dir,
            } => verify(read_package(&package)?, &root, &lake_dir),
        }
    })();
    match result {
        Ok(value) => println!(
            "{}",
            serde_json::to_string_pretty(&value).expect("JSON value")
        ),
        Err(error) => {
            eprintln!("claim package rejected: {error}");
            std::process::exit(3);
        }
    }
}
