fn main() {
    println!("proof-pilot: LLM-driven Lean proof completion loop");
    println!("drives `claude` CLI (Sonnet 4) to close sorry holes");
    println!();
    println!("TODO: implementation pending");
    println!("  - session: orchestrate iteration loop with budget");
    println!("  - lean_runner: shell out to `lake build`, capture output");
    println!("  - patcher: apply LLM-suggested edits to .lean files");
}
