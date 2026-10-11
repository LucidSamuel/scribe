use circuit_ir::load_toml_file;

fn examples_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("examples")
}

#[test]
fn load_range_check_gadget() {
    let gadget = load_toml_file(&examples_dir().join("range-check/gadget.toml"))
        .expect("failed to load gadget.toml");
    assert_eq!(gadget.name, "range-check-8bit");
    assert_eq!(gadget.private.len(), 9); // x + 8 bits, via the `witnesses` alias
    assert_eq!(gadget.constraints.len(), 9); // 8 bit constraints + 1 decomposition

    // check first bit constraint has 2 terms
    let bit0 = &gadget.constraints[0];
    assert_eq!(bit0.label, "bit_0");
    assert_eq!(bit0.terms.len(), 2);

    // check decomposition constraint has 9 terms
    let decomp = &gadget.constraints[8];
    assert_eq!(decomp.label, "decomposition");
    assert_eq!(decomp.terms.len(), 9);

    // check hypothesis
    assert_eq!(gadget.hypotheses.len(), 1);
    assert_eq!(gadget.hypotheses[0].name, "hp");
}

#[test]
fn load_poseidon_sbox() {
    let gadget = load_toml_file(&examples_dir().join("poseidon-sbox/gadget.toml")).unwrap();
    assert_eq!(gadget.name, "poseidon-sbox");
    assert_eq!(gadget.private.len(), 4);
    assert_eq!(gadget.constraints.len(), 3);
}

#[test]
fn load_nonzero_check() {
    let gadget = load_toml_file(&examples_dir().join("nonzero-check/gadget.toml")).unwrap();
    assert_eq!(gadget.name, "nonzero-check");
    assert_eq!(gadget.private.len(), 2);
    assert_eq!(gadget.constraints.len(), 1);
    assert_eq!(gadget.constraints[0].terms.len(), 2);
}

#[test]
fn load_edwards_addition() {
    let gadget = load_toml_file(&examples_dir().join("edwards-addition/gadget.toml")).unwrap();
    assert_eq!(gadget.name, "edwards-addition");
    assert_eq!(gadget.private.len(), 6);
    assert_eq!(gadget.constraints.len(), 2);
    assert_eq!(gadget.hypotheses.len(), 4);
}
