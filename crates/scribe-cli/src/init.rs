//! Template generator for Halva extractor projects.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process;

use crate::init_cmd::InitArgs;

pub fn run_init(args: InitArgs) {
    let config = InitConfig::from(args);
    match create_project(&config) {
        Ok(report) => {
            eprintln!(
                "[scribe] wrote extractor template: {}",
                report.output.display()
            );
            eprintln!(
                "[scribe] edit {}/src/main.rs to instantiate your circuit and call Halva",
                report.output.display()
            );
            println!("{}", report.output.display());
        }
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    }
}

#[derive(Debug, Clone)]
pub struct InitConfig {
    pub circuit: PathBuf,
    pub output: Option<PathBuf>,
    pub name: Option<String>,
    pub force: bool,
    pub halva_git: Option<String>,
    pub halva_rev: Option<String>,
}

impl From<InitArgs> for InitConfig {
    fn from(args: InitArgs) -> Self {
        Self {
            circuit: PathBuf::from(args.circuit),
            output: args.output.map(PathBuf::from),
            name: args.name,
            force: args.force,
            halva_git: args.halva_git,
            halva_rev: args.halva_rev,
        }
    }
}

#[derive(Debug, Clone)]
pub struct InitReport {
    pub output: PathBuf,
}

#[derive(Debug)]
pub enum InitError {
    CircuitNotDirectory(PathBuf),
    OutputExists(PathBuf),
    Io { path: PathBuf, source: io::Error },
}

impl fmt::Display for InitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InitError::CircuitNotDirectory(path) => write!(
                f,
                "--circuit path `{}` is not a directory. Point it at the raw halo2 circuit crate or source directory you want to wrap.",
                path.display()
            ),
            InitError::OutputExists(path) => write!(
                f,
                "output directory `{}` already exists and is not empty; pass --force to overwrite template files",
                path.display()
            ),
            InitError::Io { path, source } => write!(f, "{}: {source}", path.display()),
        }
    }
}

pub fn create_project(config: &InitConfig) -> Result<InitReport, InitError> {
    if !config.circuit.is_dir() {
        return Err(InitError::CircuitNotDirectory(config.circuit.clone()));
    }

    let circuit_package = infer_package_name(&config.circuit).unwrap_or_else(|| {
        config
            .circuit
            .file_name()
            .and_then(|name| name.to_str())
            .map(slugify_package)
            .filter(|name| !name.is_empty())
            .unwrap_or_else(|| "my-circuit".to_string())
    });
    let package_base = config
        .name
        .as_deref()
        .map(slugify_package)
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| slugify_package(&circuit_package));
    let namespace = config
        .name
        .as_deref()
        .map(namespace_name)
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| namespace_name(&package_base));
    let output = config
        .output
        .clone()
        .unwrap_or_else(|| PathBuf::from(format!("{package_base}-halva-extractor")));

    if output.is_dir() && output_has_entries(&output)? && !config.force {
        return Err(InitError::OutputExists(output));
    }

    write_file(
        &output.join("Cargo.toml"),
        &render_cargo_toml(config, &package_base, &circuit_package),
    )?;
    write_file(&output.join("src/main.rs"), &render_main_rs(&namespace))?;
    write_file(
        &output.join("README.md"),
        &render_readme(&package_base, &namespace),
    )?;
    write_file(&output.join(".gitignore"), "/target\n/extracted.lean\n")?;

    Ok(InitReport { output })
}

fn output_has_entries(path: &Path) -> Result<bool, InitError> {
    let mut entries = fs::read_dir(path).map_err(|source| InitError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    Ok(entries.next().is_some())
}

fn write_file(path: &Path, content: &str) -> Result<(), InitError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| InitError::Io {
            path: parent.to_path_buf(),
            source,
        })?;
    }
    fs::write(path, content).map_err(|source| InitError::Io {
        path: path.to_path_buf(),
        source,
    })
}

fn render_cargo_toml(config: &InitConfig, package_base: &str, circuit_package: &str) -> String {
    let project_name = format!("{package_base}-halva-extractor");
    let circuit_path = cargo_path(&config.circuit);
    let halva_dep = render_halva_dependency(config);

    format!(
        r#"[package]
name = "{project_name}"
version = "0.1.0"
edition = "2021"
publish = false

# Keep this extractor runnable if it is generated inside a parent Cargo workspace.
[workspace]

[dependencies]
# TODO: keep this path pointed at the crate that defines your halo2 Circuit.
# This is generated as an absolute path; edit it if you move or commit this template.
{circuit_package} = {{ path = "{circuit_path}" }}

{halva_dep}

# TODO: add the exact halo2 dependency versions used by your circuit if Halva's
# API requires them in the extractor entrypoint.
"#
    )
}

fn render_main_rs(namespace: &str) -> String {
    format!(
        r#"//! Halva extractor entrypoint generated by `scribe init`.
//!
//! `scribe verify --circuit <this-dir>` runs `cargo run --release` here and
//! expects the extracted Lean file on stdout.

fn main() -> Result<(), Box<dyn std::error::Error>> {{
    // TODO: import the circuit type from your raw halo2 crate.
    // TODO: instantiate the circuit with representative parameters/witnesses.
    // TODO: call Halva's halo2-to-Lean extractor and set the Lean namespace to
    // `{namespace}` or another stable module name.
    //
    // The final line should be equivalent to:
    //
    //     print!("{{}}", extracted_lean);
    //
    // where `extracted_lean` contains a Lean namespace with a top-level
    // `def meets_constraints ...` declaration. `scribe verify` will append your
    // semantic Spec and soundness theorem to that namespace.

    eprintln!(
        "fill in src/main.rs: instantiate your halo2 circuit and print Halva Lean output to stdout"
    );
    std::process::exit(2);
}}
"#
    )
}

fn render_halva_dependency(config: &InitConfig) -> String {
    match (&config.halva_git, &config.halva_rev) {
        (Some(git), Some(rev)) => format!(
            "# Halva halo2-to-Lean extractor.\nhalo2-fv-extractor = {{ git = \"{git}\", rev = \"{rev}\" }}"
        ),
        (Some(git), None) => {
            format!("# Halva halo2-to-Lean extractor.\nhalo2-fv-extractor = {{ git = \"{git}\" }}")
        }
        (None, Some(rev)) => format!(
            "# TODO: set the Halva extractor dependency URL. Requested revision: {rev}.\n# halo2-fv-extractor = {{ git = \"https://github.com/<owner>/<repo>.git\", rev = \"{rev}\" }}"
        ),
        (None, None) => String::from(
            "# TODO: set the Halva halo2-to-Lean extractor dependency you use.\n# halo2-fv-extractor = { git = \"https://github.com/<owner>/<repo>.git\" }",
        ),
    }
}

fn render_readme(package_base: &str, namespace: &str) -> String {
    format!(
        r#"# {package_base} Halva extractor

Generated by `scribe init --circuit`.

This project is the bridge from a raw halo2 circuit crate to `scribe verify`.
Fill in `src/main.rs` so `cargo run --release` instantiates your circuit, runs
Halva's extractor, and prints the extracted Lean program to stdout.

Expected Lean shape:

```lean
namespace {namespace}

def meets_constraints ... : Prop := ...

end {namespace}
```

Then run:

```sh
cargo run --release > extracted.lean
scribe verify --circuit . --spec-file path/to/spec.lean --output path/to/Soundness.lean
```

`scribe verify --circuit .` runs this extractor project; it does not parse raw
halo2 Rust source directly.
"#
    )
}

fn cargo_path(circuit: &Path) -> String {
    fs::canonicalize(circuit)
        .unwrap_or_else(|_| circuit.to_path_buf())
        .to_string_lossy()
        .replace('\\', "/")
}

fn infer_package_name(circuit: &Path) -> Option<String> {
    let manifest = fs::read_to_string(circuit.join("Cargo.toml")).ok()?;
    let mut in_package = false;
    for line in manifest.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_package = trimmed == "[package]";
            continue;
        }
        if in_package {
            if let Some(name) = package_name_from_line(trimmed) {
                return Some(name);
            }
        }
    }
    None
}

fn package_name_from_line(line: &str) -> Option<String> {
    let rest = line.strip_prefix("name")?.trim_start();
    let value = rest.strip_prefix('=')?.trim_start();
    parse_toml_string_value(value)
}

fn parse_toml_string_value(value: &str) -> Option<String> {
    let quote = value.chars().next()?;
    if quote != '"' && quote != '\'' {
        return None;
    }
    let remainder = &value[quote.len_utf8()..];
    let end = remainder.find(quote)?;
    Some(remainder[..end].to_string())
}

fn slugify_package(input: &str) -> String {
    let mut out = String::new();
    let mut last_dash = false;
    for ch in input.chars().flat_map(char::to_lowercase) {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
            last_dash = false;
        } else if !last_dash {
            out.push('-');
            last_dash = true;
        }
    }
    out.trim_matches('-').to_string()
}

fn namespace_name(input: &str) -> String {
    let mut out = String::new();
    for part in input
        .split(|ch: char| !ch.is_ascii_alphanumeric())
        .filter(|part| !part.is_empty())
    {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
    }
    if out.is_empty() {
        "Circuit".to_string()
    } else {
        out
    }
}

impl Default for InitConfig {
    fn default() -> Self {
        Self {
            circuit: PathBuf::from("."),
            output: None,
            name: None,
            force: false,
            halva_git: None,
            halva_rev: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("scribe_init_{name}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        dir
    }

    #[test]
    fn generated_project_uses_circuit_manifest_name() {
        let root = temp_dir("manifest_name");
        let circuit = root.join("raw");
        fs::create_dir_all(&circuit).expect("create circuit dir");
        fs::write(
            circuit.join("Cargo.toml"),
            r#"[package]
name = "poseidon-sbox"
version = "0.1.0"
"#,
        )
        .expect("write manifest");

        let output = root.join("extractor");
        let report = create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            ..InitConfig::default()
        })
        .expect("generate project");

        assert_eq!(report.output, output);
        let manifest = fs::read_to_string(output.join("Cargo.toml")).expect("read Cargo.toml");
        assert!(manifest.contains(r#"name = "poseidon-sbox-halva-extractor""#));
        assert!(manifest.contains("[workspace]"));
        assert!(manifest.contains(r#"poseidon-sbox = { path = ""#));
        assert!(manifest.contains("TODO: set the Halva halo2-to-Lean extractor dependency"));
        let main_rs = fs::read_to_string(output.join("src/main.rs")).expect("read main.rs");
        assert!(main_rs.contains("namespace to\n    // `PoseidonSbox`"));
    }

    #[test]
    fn generated_project_finds_package_name_after_other_keys() {
        let root = temp_dir("version_first");
        let circuit = root.join("raw");
        fs::create_dir_all(&circuit).expect("create circuit dir");
        fs::write(
            circuit.join("Cargo.toml"),
            r#"[package]
version = "0.1.0"

# comments and blank lines are allowed before the name
name_foo = "wrong"
name = "good-circuit"
"#,
        )
        .expect("write manifest");

        let output = root.join("extractor");
        create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            ..InitConfig::default()
        })
        .expect("generate project");

        let manifest = fs::read_to_string(output.join("Cargo.toml")).expect("read Cargo.toml");
        assert!(manifest.contains(r#"name = "good-circuit-halva-extractor""#));
        assert!(manifest.contains(r#"good-circuit = { path = ""#));
    }

    #[test]
    fn generated_project_preserves_underscore_package_dependency() {
        let root = temp_dir("underscore_package");
        let circuit = root.join("raw");
        fs::create_dir_all(&circuit).expect("create circuit dir");
        fs::write(
            circuit.join("Cargo.toml"),
            r#"[package]
name = "my_circuit"
version = "0.1.0"
"#,
        )
        .expect("write manifest");

        let output = root.join("extractor");
        create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            ..InitConfig::default()
        })
        .expect("generate project");

        let manifest = fs::read_to_string(output.join("Cargo.toml")).expect("read Cargo.toml");
        assert!(manifest.contains(r#"name = "my-circuit-halva-extractor""#));
        assert!(manifest.contains(r#"my_circuit = { path = ""#));
        assert!(!manifest.contains(r#"my-circuit = { path = ""#));
    }

    #[test]
    fn generated_project_uses_explicit_halva_dependency() {
        let root = temp_dir("halva_git");
        let circuit = root.join("circuit");
        let output = root.join("extractor");
        fs::create_dir_all(&circuit).expect("create circuit");

        create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            halva_git: Some("https://example.com/halva.git".to_string()),
            halva_rev: Some("abc123".to_string()),
            ..InitConfig::default()
        })
        .expect("generate project");

        let manifest = fs::read_to_string(output.join("Cargo.toml")).expect("read Cargo.toml");
        assert!(
            manifest.contains(
                r#"halo2-fv-extractor = { git = "https://example.com/halva.git", rev = "abc123" }"#
            ),
            "{manifest}"
        );
    }

    #[test]
    fn refuses_non_empty_output_without_force() {
        let root = temp_dir("non_empty");
        let circuit = root.join("circuit");
        let output = root.join("extractor");
        fs::create_dir_all(&circuit).expect("create circuit");
        fs::create_dir_all(&output).expect("create output");
        fs::write(output.join("README.md"), "existing").expect("write existing file");

        let err = create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            ..InitConfig::default()
        })
        .expect_err("should refuse non-empty output");

        assert!(matches!(err, InitError::OutputExists(path) if path == output));
    }

    #[test]
    fn force_overwrites_template_files() {
        let root = temp_dir("force");
        let circuit = root.join("circuit");
        let output = root.join("extractor");
        fs::create_dir_all(&circuit).expect("create circuit");
        fs::create_dir_all(&output).expect("create output");
        fs::write(output.join("README.md"), "existing").expect("write existing file");

        create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            force: true,
            ..InitConfig::default()
        })
        .expect("force generate");

        let readme = fs::read_to_string(output.join("README.md")).expect("read README");
        assert!(readme.contains("Generated by `scribe init --circuit`."));
    }

    #[test]
    fn explicit_name_preserves_namespace_casing() {
        let root = temp_dir("namespace_case");
        let circuit = root.join("circuit");
        let output = root.join("extractor");
        fs::create_dir_all(&circuit).expect("create circuit");

        create_project(&InitConfig {
            circuit,
            output: Some(output.clone()),
            name: Some("MyCircuit".to_string()),
            ..InitConfig::default()
        })
        .expect("generate");

        let main_rs = fs::read_to_string(output.join("src/main.rs")).expect("read main.rs");
        assert!(main_rs.contains("`MyCircuit` or another stable module name"));
        let manifest = fs::read_to_string(output.join("Cargo.toml")).expect("read Cargo.toml");
        assert!(manifest.contains(r#"name = "mycircuit-halva-extractor""#));
    }
}
