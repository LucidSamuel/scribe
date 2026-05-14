use std::path::Path;
use std::process::Command;

/// Result of running `lake build`.
pub struct BuildResult {
    pub success: bool,
    pub stdout: String,
    pub stderr: String,
    /// Combined stdout + stderr for tactic scanning.
    pub combined: String,
}

/// Run `lake build` in the given directory and capture output.
pub fn run_lake_build(working_dir: &Path) -> Result<BuildResult, std::io::Error> {
    let output = Command::new("lake")
        .arg("build")
        .current_dir(working_dir)
        .output()?;

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let combined = format!("{}\n{}", stdout, stderr);

    Ok(BuildResult {
        success: output.status.success(),
        stdout,
        stderr,
        combined,
    })
}

const FORBIDDEN: &[&str] = &["sorry", "axiom", "native_decide"];

/// Check if build output contains forbidden tactics for a specific file.
///
/// Only matches warning lines that reference the given filename.
/// If `target_file` is `None`, checks the entire output (legacy behavior).
pub fn has_forbidden_tactics(build_output: &str, target_file: Option<&str>) -> bool {
    match target_file {
        Some(filename) => {
            // Extract just the filename portion for matching
            let basename = Path::new(filename)
                .file_name()
                .and_then(|f| f.to_str())
                .unwrap_or(filename);

            build_output.lines().any(|line| {
                line.contains(basename)
                    && FORBIDDEN.iter().any(|kw| line.contains(kw))
            })
        }
        None => FORBIDDEN.iter().any(|kw| build_output.contains(kw)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_sorry_unfiltered() {
        assert!(has_forbidden_tactics("warning: declaration uses 'sorry'", None));
        assert!(has_forbidden_tactics("axiom foo : True", None));
    }

    #[test]
    fn detects_sorry_for_target_file() {
        let output = "warning: Foo.lean:10:8: declaration uses `sorry`\n\
                       warning: Bar.lean:5:0: declaration uses `sorry`";
        assert!(has_forbidden_tactics(output, Some("Foo.lean")));
        assert!(has_forbidden_tactics(output, Some("Bar.lean")));
        assert!(!has_forbidden_tactics(output, Some("Baz.lean")));
    }

    #[test]
    fn clean_output_passes() {
        assert!(!has_forbidden_tactics("Build completed successfully", None));
        assert!(!has_forbidden_tactics("", None));
    }
}
