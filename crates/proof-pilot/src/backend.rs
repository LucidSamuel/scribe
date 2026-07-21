//! Pluggable LLM backends for the proof completion loop.
//!
//! The session loop is backend-agnostic — it only needs a `Backend` impl that
//! takes a prompt and returns a response string. Concrete implementations cover
//! the Claude CLI, the Anthropic Messages API, and any OpenAI-compatible
//! endpoint (OpenAI, Leanstral, vLLM, ollama, etc.).

use std::process::Command;

/// Trait for LLM backends that can complete proof attempts.
///
/// `Send + Sync` so best-of-n sampling can issue concurrent `complete` calls
/// from scoped threads; implementations take `&self` and hold no interior
/// mutability.
pub trait Backend: Send + Sync {
    /// Send a prompt to the model and return the response text.
    fn complete(&self, prompt: &str, system_prompt: Option<&str>) -> Result<String, BackendError>;

    /// Human-readable backend name for logging.
    fn name(&self) -> &str;
}

#[derive(Debug)]
pub enum BackendError {
    /// The backend process or HTTP request failed.
    RequestFailed(String),
    /// The response could not be parsed.
    ParseError(String),
}

impl std::fmt::Display for BackendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BackendError::RequestFailed(msg) => write!(f, "request failed: {msg}"),
            BackendError::ParseError(msg) => write!(f, "parse error: {msg}"),
        }
    }
}

impl std::error::Error for BackendError {}

// ─── Claude CLI ──────────────────────────────────────────────────────────────

/// Backend that shells out to the `claude` CLI in pipe mode.
pub struct ClaudeCli {
    model: String,
    display_name: String,
}

impl ClaudeCli {
    pub fn new(model: String) -> Self {
        let display_name = format!("claude-cli ({model})");
        Self {
            model,
            display_name,
        }
    }
}

impl Backend for ClaudeCli {
    fn complete(&self, prompt: &str, system_prompt: Option<&str>) -> Result<String, BackendError> {
        let mut cmd = Command::new("claude");
        cmd.env_remove("CLAUDECODE")
            .arg("-p")
            .arg(prompt)
            .arg("--model")
            .arg(&self.model);

        if let Some(sp) = system_prompt {
            cmd.arg("--system-prompt").arg(sp);
        }

        let output = cmd
            .output()
            .map_err(|e| BackendError::RequestFailed(format!("spawn claude: {e}")))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(BackendError::RequestFailed(format!(
                "claude exited {}: {stderr}",
                output.status
            )));
        }

        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    }

    fn name(&self) -> &str {
        &self.display_name
    }
}

// ─── Anthropic Messages API ─────────────────────────────────────────────────

/// Backend that calls the Anthropic Messages API directly via HTTP.
pub struct AnthropicApi {
    model: String,
    api_key: String,
    base_url: String,
    max_tokens: usize,
    display_name: String,
}

impl AnthropicApi {
    pub fn new(model: String, api_key: String) -> Self {
        let display_name = format!("anthropic ({model})");
        Self {
            model,
            api_key,
            base_url: "https://api.anthropic.com".to_string(),
            max_tokens: 16384,
            display_name,
        }
    }

    pub fn with_base_url(mut self, url: String) -> Self {
        self.display_name = format!("anthropic ({}, {url})", self.model);
        self.base_url = url;
        self
    }
}

impl Backend for AnthropicApi {
    fn complete(&self, prompt: &str, system_prompt: Option<&str>) -> Result<String, BackendError> {
        let mut body = serde_json::json!({
            "model": self.model,
            "max_tokens": self.max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        });

        if let Some(sp) = system_prompt {
            body["system"] = serde_json::json!(sp);
        }

        let url = format!("{}/v1/messages", self.base_url);
        let resp = match ureq::post(&url)
            .set("x-api-key", &self.api_key)
            .set("anthropic-version", "2023-06-01")
            .set("content-type", "application/json")
            .send_string(&body.to_string())
        {
            Ok(r) => r,
            Err(ureq::Error::Status(code, resp)) => {
                let body = resp.into_string().unwrap_or_default();
                return Err(BackendError::RequestFailed(format!(
                    "HTTP {code}: {}",
                    &body[..body.len().min(500)]
                )));
            }
            Err(e) => return Err(BackendError::RequestFailed(format!("anthropic: {e}"))),
        };

        let resp_text = resp
            .into_string()
            .map_err(|e| BackendError::ParseError(format!("read body: {e}")))?;

        let val: serde_json::Value = serde_json::from_str(&resp_text)
            .map_err(|e| BackendError::ParseError(format!("json: {e}")))?;

        val["content"][0]["text"]
            .as_str()
            .map(|s| s.to_string())
            .ok_or_else(|| {
                BackendError::ParseError(format!(
                    "no content[0].text in response: {}",
                    &resp_text[..resp_text.len().min(200)]
                ))
            })
    }

    fn name(&self) -> &str {
        &self.display_name
    }
}

// ─── OpenAI-compatible API ──────────────────────────────────────────────────

/// Backend for any OpenAI-compatible Chat Completions API.
///
/// Works with OpenAI, Leanstral (hosted or self-hosted), vLLM, ollama, etc.
/// - `api_key` is optional — local endpoints (vLLM, ollama) typically need none.
/// - `use_completion_tokens` sends `max_completion_tokens` (OpenAI GPT-5 family)
///   instead of `max_tokens` (generic OpenAI-compat servers).
pub struct OpenAiCompatible {
    model: String,
    api_key: Option<String>,
    base_url: String,
    max_tokens: usize,
    use_completion_tokens: bool,
    display_name: String,
}

impl OpenAiCompatible {
    pub fn new(model: String, api_key: Option<String>, base_url: String) -> Self {
        let display_name = format!("openai-compat ({model}, {base_url})");
        Self {
            model,
            api_key,
            base_url,
            max_tokens: 16384,
            use_completion_tokens: false,
            display_name,
        }
    }

    /// Use `max_completion_tokens` instead of `max_tokens` in requests.
    ///
    /// Required for OpenAI reasoning models (GPT-5 family) where
    /// `max_tokens` is deprecated and completion limits include reasoning tokens.
    pub fn with_completion_tokens(mut self) -> Self {
        self.use_completion_tokens = true;
        self
    }

    pub fn with_name(mut self, name: String) -> Self {
        self.display_name = name;
        self
    }
}

impl Backend for OpenAiCompatible {
    fn complete(&self, prompt: &str, system_prompt: Option<&str>) -> Result<String, BackendError> {
        let mut messages = Vec::new();
        if let Some(sp) = system_prompt {
            messages.push(serde_json::json!({"role": "system", "content": sp}));
        }
        messages.push(serde_json::json!({"role": "user", "content": prompt}));

        let mut body = serde_json::json!({
            "model": self.model,
            "messages": messages,
        });

        if self.use_completion_tokens {
            body["max_completion_tokens"] = serde_json::json!(self.max_tokens);
        } else {
            body["max_tokens"] = serde_json::json!(self.max_tokens);
        }

        let url = format!("{}/chat/completions", self.base_url);
        let mut req = ureq::post(&url).set("content-type", "application/json");

        if let Some(key) = &self.api_key {
            req = req.set("Authorization", &format!("Bearer {key}"));
        }

        let resp = match req.send_string(&body.to_string()) {
            Ok(r) => r,
            Err(ureq::Error::Status(code, resp)) => {
                let body = resp.into_string().unwrap_or_default();
                return Err(BackendError::RequestFailed(format!(
                    "HTTP {code}: {}",
                    &body[..body.len().min(500)]
                )));
            }
            Err(e) => return Err(BackendError::RequestFailed(format!("openai-compat: {e}"))),
        };

        let resp_text = resp
            .into_string()
            .map_err(|e| BackendError::ParseError(format!("read body: {e}")))?;

        let val: serde_json::Value = serde_json::from_str(&resp_text)
            .map_err(|e| BackendError::ParseError(format!("json: {e}")))?;

        val["choices"][0]["message"]["content"]
            .as_str()
            .map(|s| s.to_string())
            .ok_or_else(|| {
                BackendError::ParseError(format!(
                    "no choices[0].message.content in response: {}",
                    &resp_text[..resp_text.len().min(200)]
                ))
            })
    }

    fn name(&self) -> &str {
        &self.display_name
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Resolve an API key from an explicit value or an environment variable.
pub fn resolve_api_key(explicit: Option<&str>, env_var: &str) -> Option<String> {
    explicit
        .map(|s| s.to_string())
        .or_else(|| std::env::var(env_var).ok())
}

/// Require an API key, resolving from an explicit value or environment variable.
pub fn require_api_key(
    explicit: Option<&str>,
    env_var: &str,
    backend: &str,
) -> Result<String, String> {
    resolve_api_key(explicit, env_var)
        .ok_or_else(|| format!("{backend} backend requires --api-key or {env_var} env var"))
}

/// Default model for the `claude`/`anthropic` backends when `--model` is not
/// given. Kept in one place because retired models fail at request time (e.g.
/// claude-sonnet-4-20250514 was retired 2026-06-15 and broke every default run).
pub const DEFAULT_ANTHROPIC_MODEL: &str = "claude-sonnet-5";

/// Construct a `Box<dyn Backend>` from a name, optional model, API key, and base URL.
///
/// Recognized names: `claude` / `claude-cli`, `anthropic`, `openai`, `leanstral`,
/// `leanstral-local`, `openai-compat`.
///
/// Returns `Err` with a diagnostic message if the name is unknown or required
/// parameters (key, URL) are missing — the CALLER owns the exit code, because
/// different commands document different infrastructure-error codes (`scribe
/// judge` exits 3, `scribe refute` exits 1).
pub fn make_backend(
    name: &str,
    model: Option<String>,
    api_key: Option<String>,
    base_url: Option<String>,
) -> Result<Box<dyn Backend>, String> {
    match name {
        "claude" | "claude-cli" => {
            let m = model.unwrap_or_else(|| DEFAULT_ANTHROPIC_MODEL.into());
            Ok(Box::new(ClaudeCli::new(m)))
        }
        "anthropic" => {
            let m = model.unwrap_or_else(|| DEFAULT_ANTHROPIC_MODEL.into());
            let key = require_api_key(api_key.as_deref(), "ANTHROPIC_API_KEY", "anthropic")?;
            let mut b = AnthropicApi::new(m, key);
            if let Some(url) = base_url {
                b = b.with_base_url(url);
            }
            Ok(Box::new(b))
        }
        "openai" => {
            let m = model.unwrap_or_else(|| "gpt-4o".into());
            let key = require_api_key(api_key.as_deref(), "OPENAI_API_KEY", "openai")?;
            let url = base_url.unwrap_or_else(|| "https://api.openai.com/v1".into());
            Ok(Box::new(
                OpenAiCompatible::new(m, Some(key), url)
                    .with_completion_tokens()
                    .with_name("openai".into()),
            ))
        }
        "leanstral" => {
            let m = model.unwrap_or_else(|| "leanstral-v1".into());
            let key = require_api_key(api_key.as_deref(), "LEANSTRAL_API_KEY", "leanstral")?;
            let url = base_url.ok_or_else(|| {
                "leanstral backend requires --base-url (e.g. https://api.leanstral.ai/v1)"
                    .to_string()
            })?;
            Ok(Box::new(
                OpenAiCompatible::new(m, Some(key), url).with_name("leanstral".into()),
            ))
        }
        "leanstral-local" => {
            let m = model.unwrap_or_else(|| "leanstral-v1".into());
            let url = base_url.unwrap_or_else(|| "http://localhost:8000/v1".into());
            Ok(Box::new(
                OpenAiCompatible::new(m, api_key, url).with_name("leanstral-local".into()),
            ))
        }
        "openai-compat" => {
            let m = model.ok_or_else(|| "openai-compat backend requires --model".to_string())?;
            let url =
                base_url.ok_or_else(|| "openai-compat backend requires --base-url".to_string())?;
            Ok(Box::new(
                OpenAiCompatible::new(m, api_key, url).with_name("openai-compat".into()),
            ))
        }
        other => Err(format!(
            "unknown backend: {other}\navailable: claude, anthropic, openai, leanstral, \
             leanstral-local, openai-compat"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn claude_cli_name_includes_model() {
        let b = ClaudeCli::new("claude-sonnet-5".into());
        assert_eq!(b.name(), "claude-cli (claude-sonnet-5)");
    }

    #[test]
    fn anthropic_name_includes_model() {
        let b = AnthropicApi::new("claude-sonnet-5".into(), "sk-test".into());
        assert_eq!(b.name(), "anthropic (claude-sonnet-5)");
    }

    #[test]
    fn anthropic_custom_base_url_shown_in_name() {
        let b = AnthropicApi::new("claude-sonnet-5".into(), "sk-test".into())
            .with_base_url("https://custom.example.com".into());
        assert!(b.name().contains("custom.example.com"));
    }

    #[test]
    fn openai_compat_name_includes_model_and_url() {
        let b = OpenAiCompatible::new(
            "gpt-4o".into(),
            Some("sk-test".into()),
            "https://api.openai.com/v1".into(),
        );
        assert!(b.name().contains("gpt-4o"));
        assert!(b.name().contains("api.openai.com"));
    }

    #[test]
    fn openai_compat_localhost_no_auth() {
        let b = OpenAiCompatible::new(
            "leanstral-v1".into(),
            None,
            "http://localhost:8000/v1".into(),
        );
        assert!(b.name().contains("leanstral-v1"));
        assert!(b.name().contains("localhost:8000"));
        assert!(b.api_key.is_none());
    }

    #[test]
    fn openai_completion_tokens_flag() {
        let b = OpenAiCompatible::new(
            "gpt-5".into(),
            Some("sk-test".into()),
            "https://api.openai.com/v1".into(),
        )
        .with_completion_tokens();
        assert!(b.use_completion_tokens);
    }

    #[test]
    fn resolve_api_key_prefers_explicit() {
        std::env::set_var("_TEST_SCRIBE_KEY", "from-env");
        let key = resolve_api_key(Some("from-flag"), "_TEST_SCRIBE_KEY");
        assert_eq!(key.unwrap(), "from-flag");
        std::env::remove_var("_TEST_SCRIBE_KEY");
    }

    #[test]
    fn resolve_api_key_falls_back_to_env() {
        std::env::set_var("_TEST_SCRIBE_KEY2", "from-env");
        let key = resolve_api_key(None, "_TEST_SCRIBE_KEY2");
        assert_eq!(key.unwrap(), "from-env");
        std::env::remove_var("_TEST_SCRIBE_KEY2");
    }

    #[test]
    fn resolve_api_key_returns_none_when_missing() {
        let key = resolve_api_key(None, "_TEST_SCRIBE_NONEXISTENT_KEY");
        assert!(key.is_none());
    }
}
