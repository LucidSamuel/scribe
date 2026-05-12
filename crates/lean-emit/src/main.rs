use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: lean-emit <path/to/gadget.toml>");
        std::process::exit(1);
    }

    let path = PathBuf::from(&args[1]);
    let gadget = gadget_ir::load_gadget_file(&path).unwrap_or_else(|e| {
        eprintln!("error loading {}: {}", path.display(), e);
        std::process::exit(1);
    });

    let lean_source = lean_emit::emit_lean(&gadget);
    print!("{}", lean_source);
}
