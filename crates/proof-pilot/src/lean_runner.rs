use std::fs;
use std::path::Path;
use std::process::Command;

/// Result of running a Lean verification command.
pub struct BuildResult {
    pub success: bool,
    pub stdout: String,
    pub stderr: String,
    /// Combined stdout + stderr for tactic scanning.
    pub combined: String,
}

/// Run `lake build` in the given directory and capture output.
pub fn run_lake_build(working_dir: &Path) -> Result<BuildResult, std::io::Error> {
    run_command(Command::new("lake").arg("build").current_dir(working_dir))
}

/// Build the Lake project, then compile the exact requested Lean file.
///
/// A successful default `lake build` does not imply that an arbitrary file was
/// compiled: the file may be outside the project or absent from its root module.
/// The second command closes that gap while retaining Lake's dependency setup.
pub fn run_lake_build_for_file(
    working_dir: &Path,
    lean_file: &Path,
) -> Result<BuildResult, std::io::Error> {
    let project = run_lake_build(working_dir)?;
    if !project.success {
        return Ok(project);
    }

    let target = match lean_file.strip_prefix(working_dir) {
        Ok(relative) => relative.to_path_buf(),
        Err(_) if lean_file.is_absolute() => lean_file.to_path_buf(),
        Err(_) => lean_file.canonicalize()?,
    };
    let mut file = run_command(
        Command::new("lake")
            .args(["env", "lean"])
            .arg(&target)
            .current_dir(working_dir),
    )?;
    let source_path = if target.is_absolute() {
        target
    } else {
        working_dir.join(target)
    };
    let source = fs::read_to_string(&source_path)?;
    if let Some(keyword) = forbidden_source_token(&source) {
        let diagnostic = format!(
            "{}: forbidden token `{keyword}` in source",
            source_path.display()
        );
        file.success = false;
        file.stderr.push_str(&format!("\n{diagnostic}\n"));
        file.combined.push_str(&format!("\n{diagnostic}\n"));
    }

    Ok(BuildResult {
        success: file.success,
        stdout: format!("{}\n{}", project.stdout, file.stdout),
        stderr: format!("{}\n{}", project.stderr, file.stderr),
        combined: format!("{}\n{}", project.combined, file.combined),
    })
}

fn run_command(command: &mut Command) -> Result<BuildResult, std::io::Error> {
    let output = command.output()?;

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

/// Return the first forbidden Lean token outside comments and string literals.
pub fn forbidden_source_token(source: &str) -> Option<&'static str> {
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut block_comment_depth = 0;
    let mut in_string = false;

    while i < bytes.len() {
        if in_string {
            match bytes[i] {
                b'\\' => i += 2,
                b'"' => {
                    in_string = false;
                    i += 1;
                }
                _ => i += 1,
            }
            continue;
        }

        if block_comment_depth > 0 {
            if bytes.get(i..i + 2) == Some(b"/-") {
                block_comment_depth += 1;
                i += 2;
            } else if bytes.get(i..i + 2) == Some(b"-/") {
                block_comment_depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }

        if bytes.get(i..i + 2) == Some(b"--") {
            i = source[i..]
                .find('\n')
                .map_or(bytes.len(), |offset| i + offset + 1);
        } else if bytes.get(i..i + 2) == Some(b"/-") {
            block_comment_depth = 1;
            i += 2;
        } else if bytes[i] == b'"' {
            in_string = true;
            i += 1;
        } else if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let start = i;
            i += 1;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || matches!(bytes[i], b'_' | b'\''))
            {
                i += 1;
            }
            let token = &source[start..i];
            if let Some(keyword) = FORBIDDEN.iter().find(|keyword| **keyword == token) {
                return Some(*keyword);
            }
        } else {
            i += 1;
        }
    }

    None
}

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

            build_output
                .lines()
                .any(|line| line.contains(basename) && FORBIDDEN.iter().any(|kw| line.contains(kw)))
        }
        None => FORBIDDEN.iter().any(|kw| build_output.contains(kw)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_sorry_unfiltered() {
        assert!(has_forbidden_tactics(
            "warning: declaration uses 'sorry'",
            None
        ));
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

    #[test]
    fn detects_forbidden_source_tokens() {
        assert_eq!(
            forbidden_source_token("axiom unsound : False"),
            Some("axiom")
        );
        assert_eq!(
            forbidden_source_token("theorem t : True := by\n  native_decide"),
            Some("native_decide")
        );
        assert_eq!(
            forbidden_source_token("theorem t : True := by\n  sorry"),
            Some("sorry")
        );
    }

    #[test]
    fn ignores_forbidden_words_in_comments_and_strings() {
        let source = r#"
-- sorry axiom native_decide
/- axiom /- sorry -/ native_decide -/
def message := "sorry axiom native_decide"
theorem t : True := by trivial
"#;
        assert_eq!(forbidden_source_token(source), None);
    }
}
