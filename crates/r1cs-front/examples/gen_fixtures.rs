//! Generates two .r1cs fixtures with r1cs-front's builder (no circom install
//! needed): a correct Num2Bits(2) and the classic circomlib IsZero bug.
//!
//! ```sh
//! cargo run -p r1cs-front --example gen_fixtures -- <out-dir>
//! scribe import-r1cs --r1cs <out-dir>/iszero_buggy.r1cs --sym <out-dir>/iszero_buggy.sym \
//!   --spec "(in_ = 0 ∧ out = 1) ∨ (in_ ≠ 0 ∧ out = 0)"
//! scribe judge --gadget <out-dir>/iszero_buggy.gadget.toml   # → UNSOUND
//! ```
//
// Fixture notes:
// - num2bits2.r1cs: correct 2-bit decomposition (circomlib Num2Bits(2) shape)
// - iszero_buggy.r1cs: circomlib IsZero with the `in*out = 0` constraint DROPPED
//   (the canonical audit bug — out is then unconstrained for in != 0)
use num_bigint::BigUint;
use r1cs_front::{build_r1cs_bytes, R1csConstraint};

fn main() {
    let p = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    let one = BigUint::from(1u32);
    let neg1 = &p - &one;
    let dir = std::env::args().nth(1).expect("out dir");

    // num2bits2: wires 0=1, 1=in, 2=out0, 3=out1
    let num2bits = vec![
        R1csConstraint {
            a: vec![(2, one.clone())],
            b: vec![(2, one.clone()), (0, neg1.clone())],
            c: vec![],
        },
        R1csConstraint {
            a: vec![(3, one.clone())],
            b: vec![(3, one.clone()), (0, neg1.clone())],
            c: vec![],
        },
        R1csConstraint {
            a: vec![(2, one.clone()), (3, BigUint::from(2u32))],
            b: vec![(0, one.clone())],
            c: vec![(1, one.clone())],
        },
    ];
    std::fs::write(
        format!("{dir}/num2bits2.r1cs"),
        build_r1cs_bytes(&p, 32, 4, &num2bits),
    )
    .unwrap();
    std::fs::write(
        format!("{dir}/num2bits2.sym"),
        "1,1,0,main.in\n2,2,0,main.out[0]\n3,3,0,main.out[1]\n",
    )
    .unwrap();

    // iszero (BUGGY): wires 0=1, 1=in, 2=out, 3=inv
    // kept:    (-in)*(inv) + 1 - out = 0   i.e. out = 1 - in*inv
    // DROPPED: in*out = 0
    let iszero_buggy = vec![R1csConstraint {
        a: vec![(1, neg1.clone())],
        b: vec![(3, one.clone())],
        c: vec![(2, one.clone()), (0, neg1.clone())],
    }];
    std::fs::write(
        format!("{dir}/iszero_buggy.r1cs"),
        build_r1cs_bytes(&p, 32, 4, &iszero_buggy),
    )
    .unwrap();
    std::fs::write(
        format!("{dir}/iszero_buggy.sym"),
        "1,1,0,main.in\n2,2,0,main.out\n3,3,0,main.inv\n",
    )
    .unwrap();
    println!("fixtures written to {dir}");
}
