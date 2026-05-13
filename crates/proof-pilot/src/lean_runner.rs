use std::path::Path;
use std::process::Command;

/// Result of running `lake build`.
pub struct BuildResult {
    pub success: bool,
    pub stdout: String,
    pub stderr: String,
}

/// Run `lake build` in the given directory and capture output.
pub fn run_lake_build(working_dir: &Path) -> Result<BuildResult, std::io::Error> {
    let output = Command::new("lake")
        .arg("build")
        .current_dir(working_dir)
        .output()?;

    Ok(BuildResult {
        success: output.status.success(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

const FORBIDDEN: &[&str] = &["sorry", "axiom", "native_decide"];

/// Check if build output contains sorry, axiom, or native_decide warnings.
pub fn has_forbidden_tactics(build_output: &str) -> bool {
    FORBIDDEN.iter().any(|kw| build_output.contains(kw))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_sorry() {
        assert!(has_forbidden_tactics("warning: declaration uses 'sorry'"));
        assert!(has_forbidden_tactics("axiom foo : True"));
        assert!(has_forbidden_tactics("native_decide"));
    }

    #[test]
    fn clean_output_passes() {
        assert!(!has_forbidden_tactics("Build completed successfully"));
        assert!(!has_forbidden_tactics(""));
    }
}
