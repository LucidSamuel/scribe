//! Extraction helpers for `scribe verify`.
//!
//! Two modes (locked decision #1 from roadmap-v2.md):
//!
//! - **Fast path** (`--halva-output`): read an already-extracted Halva .lean file
//!   from disk.
//! - **Extractor project** (`--circuit`): shell out to `cargo run --release` inside
//!   the specified Halva EXTRACTOR PROJECT directory and capture stdout as the Lean
//!   output.  The directory must contain a Cargo project that runs the Halva
//!   extractor and prints the resulting Lean to stdout.

use std::fs;
use std::path::Path;
use std::process::{self, Command};

/// Read Halva extraction output from a pre-extracted .lean file on disk.
pub fn from_halva_file(path: &str) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("error: cannot read --halva-output {path}: {e}");
        process::exit(1);
    })
}

/// Invoke `cargo run --release` inside `project_dir` and return the captured
/// stdout as the Halva Lean output.
///
/// The Halva extractor program must print its Lean output to stdout.
pub fn from_circuit_project(project_dir: &str) -> String {
    let dir = Path::new(project_dir);
    if !dir.is_dir() {
        eprintln!(
            "error: --circuit path `{project_dir}` is not a directory. \
             It must be a Halva EXTRACTOR PROJECT (a Cargo project that prints \
             extracted Lean to stdout)."
        );
        process::exit(1);
    }

    eprintln!("[scribe] running Halva extractor in {project_dir}...");
    eprintln!(
        "[scribe] note: --circuit points at a Halva EXTRACTOR PROJECT, not a raw \
         halo2 circuit. The project must contain `cargo run --release` logic that \
         emits Lean output to stdout."
    );

    let output = Command::new("cargo")
        .args(["run", "--release"])
        .current_dir(dir)
        .output()
        .unwrap_or_else(|e| {
            eprintln!("error: failed to run `cargo run --release` in {project_dir}: {e}");
            process::exit(1);
        });

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprintln!(
            "error: `cargo run --release` in {project_dir} exited with {}\nstderr:\n{stderr}",
            output.status
        );
        process::exit(1);
    }

    let lean_output = String::from_utf8_lossy(&output.stdout).into_owned();
    if lean_output.trim().is_empty() {
        eprintln!(
            "error: `cargo run --release` in {project_dir} produced no output. \
             The extractor must print the extracted Lean content to stdout."
        );
        process::exit(1);
    }

    eprintln!("[scribe] extraction complete ({} bytes)", lean_output.len());
    lean_output
}
