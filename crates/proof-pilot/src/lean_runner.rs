use std::path::Path;

/// Result of running `lake build`.
pub struct BuildResult {
    pub success: bool,
    pub stdout: String,
    pub stderr: String,
}

/// Run `lake build` in the given directory and capture output.
pub fn run_lake_build(_working_dir: &Path) -> Result<BuildResult, std::io::Error> {
    todo!()
}

/// Check if build output contains sorry, axiom, or native_decide warnings.
pub fn has_forbidden_tactics(_build_output: &str) -> bool {
    todo!()
}
