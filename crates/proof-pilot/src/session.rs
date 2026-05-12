/// Configuration for a proof completion session.
pub struct SessionConfig {
    /// Path to the Lean file to prove.
    pub lean_file: String,
    /// Working directory containing the Lake project.
    pub lake_dir: String,
    /// Maximum number of iterations before giving up.
    pub max_iterations: u32,
    /// Path to the system prompt for Claude.
    pub system_prompt: String,
}

/// Run a proof completion session.
///
/// Loop: read file -> send to Claude CLI with lake build output ->
/// get patch -> apply -> rebuild -> repeat until green or budget exhausted.
pub fn run(_config: &SessionConfig) -> Result<(), Box<dyn std::error::Error>> {
    todo!()
}
