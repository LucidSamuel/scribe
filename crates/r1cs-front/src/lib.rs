//! circom / R1CS front-end for scribe.
//!
//! Parses the iden3 `.r1cs` binary format (the interchange format emitted by
//! `circom --r1cs` and consumed by snarkjs) plus the companion `.sym` signal
//! map, and converts the rank-1 constraint system into scribe's `gadget-ir` —
//! from which the whole existing pipeline (Lean scaffolds, the proof loop, the
//! adversarial refuter, `scribe judge`) works unchanged.
//!
//! A rank-1 constraint `⟨A,w⟩ · ⟨B,w⟩ = ⟨C,w⟩` is expanded exactly into
//! gadget-ir's sum-of-products form: `Σᵢⱼ aᵢbⱼ·wᵢwⱼ − Σₖ cₖ·wₖ = 0`, with wire 0
//! (the constant-1 wire) dropping out of monomials. Coefficients are reduced
//! mod the header prime and canonicalized to signed form (`p − 1` renders as
//! `-1`), keeping the emitted Lean statement generic over the field where the
//! circuit's arithmetic allows it — see [`ConvertOptions::max_coeff_bits`].
//!
//! Format reference: <https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md>

use std::collections::BTreeMap;

use gadget_ir::{Constraint, Gadget, Term, WitnessVar};
use num_bigint::BigUint;
use num_traits::Zero;

// ─── Errors ─────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum R1csError {
    Io(std::io::Error),
    /// Not an r1cs file, or an unsupported version.
    BadMagic(String),
    /// Structurally invalid content (truncated section, wire id out of range, …).
    Malformed(String),
    /// Valid file, but outside what the v1 converter supports.
    Unsupported(String),
}

impl std::fmt::Display for R1csError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            R1csError::Io(e) => write!(f, "io: {e}"),
            R1csError::BadMagic(m) => write!(f, "not an r1cs file: {m}"),
            R1csError::Malformed(m) => write!(f, "malformed r1cs: {m}"),
            R1csError::Unsupported(m) => write!(f, "unsupported by the v1 converter: {m}"),
        }
    }
}

impl std::error::Error for R1csError {}

impl From<std::io::Error> for R1csError {
    fn from(e: std::io::Error) -> Self {
        R1csError::Io(e)
    }
}

// ─── Parsed representation ──────────────────────────────────────────────────

/// One sparse linear combination: `wire id → coefficient` (already reduced
/// mod the prime by the producer; we reduce again defensively).
pub type LinearCombination = Vec<(u32, BigUint)>;

/// A rank-1 constraint `⟨A,w⟩ · ⟨B,w⟩ = ⟨C,w⟩`.
#[derive(Debug, Clone)]
pub struct R1csConstraint {
    pub a: LinearCombination,
    pub b: LinearCombination,
    pub c: LinearCombination,
}

/// A parsed `.r1cs` file (header + constraints).
#[derive(Debug, Clone)]
pub struct R1csFile {
    /// The field prime from the header.
    pub prime: BigUint,
    /// Total wires, including wire 0 (the constant 1).
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub constraints: Vec<R1csConstraint>,
}

// ─── Binary parsing ─────────────────────────────────────────────────────────

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Reader { buf, pos: 0 }
    }

    fn take(&mut self, n: usize, what: &str) -> Result<&'a [u8], R1csError> {
        if self.pos + n > self.buf.len() {
            return Err(R1csError::Malformed(format!(
                "truncated while reading {what} ({n} bytes at offset {})",
                self.pos
            )));
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }

    fn u32(&mut self, what: &str) -> Result<u32, R1csError> {
        let b = self.take(4, what)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn u64(&mut self, what: &str) -> Result<u64, R1csError> {
        let b = self.take(8, what)?;
        Ok(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }
}

/// Parse the iden3 `.r1cs` binary format from a byte buffer.
pub fn parse_r1cs_bytes(bytes: &[u8]) -> Result<R1csFile, R1csError> {
    let mut r = Reader::new(bytes);

    let magic = r.take(4, "magic")?;
    if magic != b"r1cs" {
        return Err(R1csError::BadMagic(format!(
            "magic is {magic:?}, expected \"r1cs\""
        )));
    }
    let version = r.u32("version")?;
    if version != 1 {
        return Err(R1csError::BadMagic(format!(
            "version {version}, only version 1 is supported"
        )));
    }
    let n_sections = r.u32("section count")?;

    // Sections may appear in any order; index them, then parse header before
    // constraints (the constraint encoding needs the header's field size).
    let mut sections: BTreeMap<u32, &[u8]> = BTreeMap::new();
    for _ in 0..n_sections {
        let stype = r.u32("section type")?;
        let ssize = r.u64("section size")? as usize;
        let content = r.take(ssize, "section content")?;
        // Duplicate section types are malformed; keep the first, reject rest.
        if sections.insert(stype, content).is_some() {
            return Err(R1csError::Malformed(format!(
                "duplicate section type {stype}"
            )));
        }
    }
    if r.pos != r.buf.len() {
        return Err(R1csError::Malformed(format!(
            "trailing bytes after section table at offset {}",
            r.pos
        )));
    }

    let header = sections
        .get(&1)
        .ok_or_else(|| R1csError::Malformed("missing header section (type 1)".into()))?;
    let mut h = Reader::new(header);
    let n8 = h.u32("field size")? as usize;
    if n8 == 0 || n8 > 64 {
        return Err(R1csError::Malformed(format!(
            "field size {n8} bytes out of range"
        )));
    }
    let prime = BigUint::from_bytes_le(h.take(n8, "prime")?);
    if prime < BigUint::from(2u8) {
        return Err(R1csError::Malformed("prime < 2".into()));
    }
    let n_wires = h.u32("nWires")?;
    let n_pub_out = h.u32("nPubOut")?;
    let n_pub_in = h.u32("nPubIn")?;
    let n_prv_in = h.u32("nPrvIn")?;
    let _n_labels = h.u64("nLabels")?;
    let m_constraints = h.u32("mConstraints")?;
    if h.pos != h.buf.len() {
        return Err(R1csError::Malformed(format!(
            "trailing bytes in header section at offset {}",
            h.pos
        )));
    }

    let cs_section = sections
        .get(&2)
        .ok_or_else(|| R1csError::Malformed("missing constraints section (type 2)".into()))?;
    let mut c = Reader::new(cs_section);
    let mut constraints = Vec::with_capacity(m_constraints as usize);
    for ci in 0..m_constraints {
        let mut lcs: [LinearCombination; 3] = [Vec::new(), Vec::new(), Vec::new()];
        for lc in &mut lcs {
            let nnz = c.u32("lc term count")?;
            for _ in 0..nnz {
                let wire = c.u32("wire id")?;
                if wire >= n_wires {
                    return Err(R1csError::Malformed(format!(
                        "constraint {ci}: wire {wire} out of range (nWires = {n_wires})"
                    )));
                }
                let coeff = BigUint::from_bytes_le(c.take(n8, "coefficient")?) % &prime;
                if !coeff.is_zero() {
                    lc.push((wire, coeff));
                }
            }
        }
        let [a, b, c_lc] = lcs;
        constraints.push(R1csConstraint { a, b, c: c_lc });
    }
    if c.pos != c.buf.len() {
        return Err(R1csError::Malformed(format!(
            "trailing bytes in constraints section at offset {}",
            c.pos
        )));
    }

    Ok(R1csFile {
        prime,
        n_wires,
        n_pub_out,
        n_pub_in,
        n_prv_in,
        constraints,
    })
}

/// Parse a `.r1cs` file from disk.
pub fn parse_r1cs_file(path: &std::path::Path) -> Result<R1csFile, R1csError> {
    parse_r1cs_bytes(&std::fs::read(path)?)
}

// ─── .sym parsing ───────────────────────────────────────────────────────────

/// Parse a circom `.sym` file into `wire id → signal name`.
///
/// Each line is `#label,#wire,#component,name` (e.g. `2,2,1,main.in[0]`);
/// wires optimized out by the compiler carry `-1` and are skipped. When
/// several labels map to one wire (signal aliasing after optimization), the
/// first name wins.
pub fn parse_sym(content: &str) -> BTreeMap<u32, String> {
    let mut map = BTreeMap::new();
    for line in content.lines() {
        let mut parts = line.splitn(4, ',');
        let (Some(_label), Some(wire), Some(_component), Some(name)) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            continue;
        };
        let Ok(wire) = wire.trim().parse::<i64>() else {
            continue;
        };
        if wire < 0 {
            continue;
        }
        map.entry(wire as u32)
            .or_insert_with(|| name.trim().to_string());
    }
    map
}

// ─── Conversion to gadget-ir ────────────────────────────────────────────────

/// Options for [`to_gadget`].
pub struct ConvertOptions {
    /// Gadget name (becomes the Lean theorem name after sanitization).
    pub name: String,
    /// The soundness spec is the human trust root — R1CS carries constraints,
    /// never intent, so it must be supplied, not derived.
    pub soundness_spec: Option<String>,
    /// Reject any canonicalized coefficient wider than this many bits.
    ///
    /// Small signed coefficients (`-1`, powers of two, …) mean the same
    /// polynomial over every prime field, so the emitted theorem can stay
    /// generic over `p`. A huge canonical coefficient (e.g. an inverse of 2,
    /// `(p+1)/2`) is only meaningful at the header prime — supporting those
    /// needs prime-pinned emission, which v1 deliberately does not do.
    /// Default 64.
    pub max_coeff_bits: u64,
}

impl Default for ConvertOptions {
    fn default() -> Self {
        ConvertOptions {
            name: "r1cs-import".to_string(),
            soundness_spec: None,
            max_coeff_bits: 64,
        }
    }
}

/// Render a mod-p coefficient in signed canonical form: values above `p/2`
/// render as the negative of their complement (`p − 1` → `"-1"`).
fn canonical_coeff(c: &BigUint, prime: &BigUint) -> String {
    let half = prime >> 1;
    if c > &half {
        format!("-{}", prime - c)
    } else {
        c.to_string()
    }
}

/// Bit width of the magnitude of a signed canonical coefficient string.
fn canonical_bits(s: &str) -> u64 {
    let mag = s.strip_prefix('-').unwrap_or(s);
    mag.parse::<BigUint>().map(|b| b.bits()).unwrap_or(u64::MAX)
}

/// A stable, Lean-friendly witness name from a `.sym` signal name:
/// `main.in[0]` → `in_0`, `main.child.out` → `child_out`.
fn lean_name(sym: &str) -> String {
    let trimmed = sym.strip_prefix("main.").unwrap_or(sym);
    let mut out = String::new();
    for ch in trimmed.chars() {
        match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(ch),
            '.' | '[' => {
                if !out.ends_with('_') {
                    out.push('_');
                }
            }
            _ => {}
        }
    }
    let out = out.trim_matches('_').to_string();
    if out.is_empty() || out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        return format!("w_{out}");
    }
    // Lean 4 keywords make illegal binder names; `in` is a common circom
    // signal name, so this bites in practice.
    const LEAN_KEYWORDS: &[&str] = &[
        "in", "fun", "let", "do", "then", "else", "if", "match", "with", "by", "at", "from",
        "have", "show", "open", "end", "def", "theorem", "example", "variable", "where",
    ];
    if LEAN_KEYWORDS.contains(&out.as_str()) {
        format!("{out}_")
    } else {
        out
    }
}

/// Convert a parsed R1CS into a `gadget_ir::Gadget`.
///
/// Wire 0 is the constant-1 wire: it contributes to coefficients, never to
/// monomials. Every other wire that appears in some constraint, or appears in
/// the `.sym` map, becomes a witness variable. Preserving named unconstrained
/// wires is essential: specs often mention public outputs precisely to catch
/// dangling-output bugs.
/// Each rank-1 row expands to one gadget constraint
/// `Σᵢⱼ aᵢbⱼ·wᵢwⱼ − Σₖ cₖ·wₖ = 0`, with like monomials merged.
pub fn to_gadget(
    r1cs: &R1csFile,
    sym: &BTreeMap<u32, String>,
    opts: &ConvertOptions,
) -> Result<Gadget, R1csError> {
    // Collect constrained wires plus named `.sym` wires (excluding wire 0).
    let mut used: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for c in &r1cs.constraints {
        for (w, _) in c.a.iter().chain(c.b.iter()).chain(c.c.iter()) {
            if *w != 0 {
                used.insert(*w);
            }
        }
    }
    for wire in sym.keys().copied().filter(|w| *w != 0) {
        if wire >= r1cs.n_wires {
            return Err(R1csError::Malformed(format!(
                ".sym references wire {wire}, but nWires = {}",
                r1cs.n_wires
            )));
        }
        used.insert(wire);
    }

    // Wire id → dense witness id, plus names (deduped after sanitization).
    let mut witnesses = Vec::with_capacity(used.len());
    let mut wire_to_id: BTreeMap<u32, usize> = BTreeMap::new();
    let mut seen_names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (id, wire) in used.iter().enumerate() {
        let base_name = sym
            .get(wire)
            .map(|s| lean_name(s))
            .unwrap_or_else(|| format!("w{wire}"));
        let mut name = base_name.clone();
        let mut suffix = 0usize;
        while !seen_names.insert(name.clone()) {
            suffix += 1;
            name = if suffix == 1 {
                format!("{base_name}_w{wire}")
            } else {
                format!("{base_name}_w{wire}_{suffix}")
            };
        }
        witnesses.push(WitnessVar { id, name });
        wire_to_id.insert(*wire, id);
    }

    let prime = &r1cs.prime;
    let mut constraints = Vec::with_capacity(r1cs.constraints.len());
    for (ci, rc) in r1cs.constraints.iter().enumerate() {
        // Accumulate coefficients per monomial. Key: sorted witness-id list
        // (empty = constant term).
        let mut acc: BTreeMap<Vec<usize>, BigUint> = BTreeMap::new();
        let add = |key: Vec<usize>, val: BigUint, acc: &mut BTreeMap<Vec<usize>, BigUint>| {
            let entry = acc.entry(key).or_insert_with(BigUint::zero);
            *entry = (&*entry + val) % prime;
        };

        // + A·B
        for (wa, ca) in &rc.a {
            for (wb, cb) in &rc.b {
                let coeff = (ca * cb) % prime;
                let mut key: Vec<usize> = Vec::new();
                if *wa != 0 {
                    key.push(wire_to_id[wa]);
                }
                if *wb != 0 {
                    key.push(wire_to_id[wb]);
                }
                key.sort_unstable();
                add(key, coeff, &mut acc);
            }
        }
        // − C  (as + (p − c))
        for (wc, cc) in &rc.c {
            let neg = (prime - cc) % prime;
            let key = if *wc == 0 {
                Vec::new()
            } else {
                vec![wire_to_id[wc]]
            };
            add(key, neg, &mut acc);
        }

        let mut terms = Vec::new();
        for (vars, coeff) in acc {
            if coeff.is_zero() {
                continue;
            }
            let rendered = canonical_coeff(&coeff, prime);
            let bits = canonical_bits(&rendered);
            if bits > opts.max_coeff_bits {
                return Err(R1csError::Unsupported(format!(
                    "constraint {ci}: canonical coefficient {rendered} is {bits} bits wide \
                     (limit {}). This circuit's arithmetic is only meaningful at the header \
                     prime; prime-pinned emission is not supported yet.",
                    opts.max_coeff_bits
                )));
            }
            terms.push(Term {
                coeff: rendered,
                vars,
            });
        }
        // A row that cancels to nothing is `0 = 0` — legal R1CS, nothing to state.
        if terms.is_empty() {
            continue;
        }
        constraints.push(Constraint {
            label: format!("r1cs_{ci}"),
            terms,
        });
    }

    Ok(Gadget {
        name: opts.name.clone(),
        modulus: prime.to_string(),
        witnesses,
        constraints,
        hypotheses: Vec::new(),
        soundness_spec: opts.soundness_spec.clone(),
    })
}

// ─── Test-support builder (also used by fixtures) ───────────────────────────

/// Serialize an [`R1csFile`]-shaped description back into the binary format.
/// Used by tests to build fixtures without a circom install; kept in the
/// public API so downstream tests (e.g. scribe-cli's) can do the same.
pub fn build_r1cs_bytes(
    prime: &BigUint,
    n8: usize,
    n_wires: u32,
    constraints: &[R1csConstraint],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"r1cs");
    out.extend_from_slice(&1u32.to_le_bytes()); // version
    out.extend_from_slice(&2u32.to_le_bytes()); // two sections

    // Header section
    let mut header = Vec::new();
    header.extend_from_slice(&(n8 as u32).to_le_bytes());
    let mut prime_bytes = prime.to_bytes_le();
    prime_bytes.resize(n8, 0);
    header.extend_from_slice(&prime_bytes);
    header.extend_from_slice(&n_wires.to_le_bytes());
    header.extend_from_slice(&0u32.to_le_bytes()); // nPubOut
    header.extend_from_slice(&0u32.to_le_bytes()); // nPubIn
    header.extend_from_slice(&0u32.to_le_bytes()); // nPrvIn
    header.extend_from_slice(&(n_wires as u64).to_le_bytes()); // nLabels
    header.extend_from_slice(&(constraints.len() as u32).to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&(header.len() as u64).to_le_bytes());
    out.extend_from_slice(&header);

    // Constraints section
    let mut cs = Vec::new();
    for c in constraints {
        for lc in [&c.a, &c.b, &c.c] {
            cs.extend_from_slice(&(lc.len() as u32).to_le_bytes());
            for (wire, coeff) in lc {
                cs.extend_from_slice(&wire.to_le_bytes());
                let mut cb = coeff.to_bytes_le();
                cb.resize(n8, 0);
                cs.extend_from_slice(&cb);
            }
        }
    }
    out.extend_from_slice(&2u32.to_le_bytes());
    out.extend_from_slice(&(cs.len() as u64).to_le_bytes());
    out.extend_from_slice(&cs);

    out
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn p() -> BigUint {
        // Small prime keeps fixtures readable; the parser never assumes BN254.
        BigUint::from(101u32)
    }

    fn big(n: u32) -> BigUint {
        BigUint::from(n)
    }

    fn append_to_section(mut bytes: Vec<u8>, section_type: u32, extra: &[u8]) -> Vec<u8> {
        let mut pos = 12usize; // magic + version + section count
        loop {
            let stype = u32::from_le_bytes(bytes[pos..pos + 4].try_into().unwrap());
            let size_pos = pos + 4;
            let size = u64::from_le_bytes(bytes[size_pos..size_pos + 8].try_into().unwrap());
            let content_start = pos + 12;
            let content_end = content_start + size as usize;
            if stype == section_type {
                let new_size = size + extra.len() as u64;
                bytes[size_pos..size_pos + 8].copy_from_slice(&new_size.to_le_bytes());
                bytes.splice(content_end..content_end, extra.iter().copied());
                return bytes;
            }
            pos = content_end;
        }
    }

    /// wires: 0 = const 1, 1 = a, 2 = b, 3 = c;  constraint: a * b = c
    fn multiplier() -> Vec<R1csConstraint> {
        vec![R1csConstraint {
            a: vec![(1, big(1))],
            b: vec![(2, big(1))],
            c: vec![(3, big(1))],
        }]
    }

    #[test]
    fn roundtrip_multiplier() {
        let bytes = build_r1cs_bytes(&p(), 8, 4, &multiplier());
        let parsed = parse_r1cs_bytes(&bytes).expect("parse");
        assert_eq!(parsed.prime, p());
        assert_eq!(parsed.n_wires, 4);
        assert_eq!(parsed.constraints.len(), 1);
        assert_eq!(parsed.constraints[0].a, vec![(1, big(1))]);
    }

    #[test]
    fn rejects_bad_magic_version_truncation_and_range() {
        let good = build_r1cs_bytes(&p(), 8, 4, &multiplier());

        let mut bad = good.clone();
        bad[0] = b'x';
        assert!(matches!(
            parse_r1cs_bytes(&bad),
            Err(R1csError::BadMagic(_))
        ));

        let mut bad = good.clone();
        bad[4] = 9; // version
        assert!(matches!(
            parse_r1cs_bytes(&bad),
            Err(R1csError::BadMagic(_))
        ));

        assert!(matches!(
            parse_r1cs_bytes(&good[..good.len() - 3]),
            Err(R1csError::Malformed(_))
        ));

        let mut trailing_file = good.clone();
        trailing_file.push(0);
        assert!(matches!(
            parse_r1cs_bytes(&trailing_file),
            Err(R1csError::Malformed(_))
        ));

        assert!(matches!(
            parse_r1cs_bytes(&append_to_section(good.clone(), 1, &[0])),
            Err(R1csError::Malformed(_))
        ));

        assert!(matches!(
            parse_r1cs_bytes(&append_to_section(good.clone(), 2, &[0])),
            Err(R1csError::Malformed(_))
        ));

        // wire id ≥ nWires
        let out_of_range = vec![R1csConstraint {
            a: vec![(9, big(1))],
            b: vec![(2, big(1))],
            c: vec![(3, big(1))],
        }];
        let bytes = build_r1cs_bytes(&p(), 8, 4, &out_of_range);
        assert!(matches!(
            parse_r1cs_bytes(&bytes),
            Err(R1csError::Malformed(_))
        ));
    }

    #[test]
    fn multiplier_converts_to_expected_terms() {
        let bytes = build_r1cs_bytes(&p(), 8, 4, &multiplier());
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let sym: BTreeMap<u32, String> = [
            (1, "main.a".to_string()),
            (2, "main.b".to_string()),
            (3, "main.c".to_string()),
        ]
        .into();
        let gadget = to_gadget(
            &parsed,
            &sym,
            &ConvertOptions {
                name: "multiplier".into(),
                soundness_spec: Some("c = a * b".into()),
                ..Default::default()
            },
        )
        .expect("convert");

        let names: Vec<&str> = gadget.witnesses.iter().map(|w| w.name.as_str()).collect();
        assert_eq!(names, vec!["a", "b", "c"]);
        assert_eq!(gadget.modulus, "101");
        assert_eq!(gadget.constraints.len(), 1);
        // a*b - c = 0  →  {coeff 1, vars [0,1]}, {coeff -1, vars [2]}
        let terms = &gadget.constraints[0].terms;
        assert_eq!(terms.len(), 2);
        assert!(terms.iter().any(|t| t.coeff == "1" && t.vars == vec![0, 1]));
        assert!(terms.iter().any(|t| t.coeff == "-1" && t.vars == vec![2]));
    }

    /// Num2Bits(2): out0, out1 bits of in.
    /// wires: 0 = 1, 1 = in, 2 = out0, 3 = out1
    ///   out0 * (out0 - 1) = 0
    ///   out1 * (out1 - 1) = 0
    ///   out0 + 2*out1 = in         (as lc·1 = in)
    fn num2bits() -> Vec<R1csConstraint> {
        let one = big(1);
        let neg1 = p() - big(1);
        vec![
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
                a: vec![(2, one.clone()), (3, big(2))],
                b: vec![(0, one.clone())],
                c: vec![(1, one)],
            },
        ]
    }

    #[test]
    fn num2bits_expansion_and_signed_canonicalization() {
        let bytes = build_r1cs_bytes(&p(), 8, 4, &num2bits());
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let sym: BTreeMap<u32, String> = [
            (1, "main.in".to_string()),
            (2, "main.out[0]".to_string()),
            (3, "main.out[1]".to_string()),
        ]
        .into();
        let gadget = to_gadget(&parsed, &sym, &ConvertOptions::default()).unwrap();

        let names: Vec<&str> = gadget.witnesses.iter().map(|w| w.name.as_str()).collect();
        assert_eq!(names, vec!["in_", "out_0", "out_1"]); // `in` is a Lean keyword

        // Constraint 0: out0*out0 - out0 = 0 (p−1 canonicalizes to -1).
        let c0 = &gadget.constraints[0].terms;
        assert!(c0.iter().any(|t| t.coeff == "1" && t.vars == vec![1, 1]));
        assert!(c0.iter().any(|t| t.coeff == "-1" && t.vars == vec![1]));

        // Constraint 2: out0 + 2*out1 - in = 0.
        let c2 = &gadget.constraints[2].terms;
        assert!(c2.iter().any(|t| t.coeff == "1" && t.vars == vec![1]));
        assert!(c2.iter().any(|t| t.coeff == "2" && t.vars == vec![2]));
        assert!(c2.iter().any(|t| t.coeff == "-1" && t.vars == vec![0]));
    }

    #[test]
    fn wide_coefficient_is_rejected_with_guidance() {
        // A coefficient like an inverse only means something at THIS prime:
        // over ZMod 101, inv(2) = 51 — 51 and -50 are both "wide" relative to
        // a 5-bit limit, so the guard must fire.
        let cs = vec![R1csConstraint {
            a: vec![(1, big(51))],
            b: vec![(0, big(1))],
            c: vec![(2, big(1))],
        }];
        let bytes = build_r1cs_bytes(&p(), 8, 3, &cs);
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let opts = ConvertOptions {
            max_coeff_bits: 5,
            ..Default::default()
        };
        let err = to_gadget(&parsed, &BTreeMap::new(), &opts).unwrap_err();
        assert!(matches!(err, R1csError::Unsupported(_)));
        assert!(err.to_string().contains("prime-pinned"));
    }

    #[test]
    fn sym_parsing_names_aliases_and_optimized_wires() {
        let sym = parse_sym(
            "1,1,0,main.in\n\
             2,2,0,main.out[0]\n\
             3,-1,0,main.dropped\n\
             4,2,0,main.alias_of_out\n\
             garbage line\n",
        );
        assert_eq!(sym.get(&1).unwrap(), "main.in");
        assert_eq!(sym.get(&2).unwrap(), "main.out[0]"); // first name wins
        assert!(!sym.values().any(|v| v.contains("dropped")));
    }

    #[test]
    fn lean_name_sanitization() {
        assert_eq!(lean_name("main.in[0]"), "in_0");
        assert_eq!(lean_name("main.child.out"), "child_out");
        assert_eq!(lean_name("main.x"), "x");
        assert_eq!(lean_name("main.0weird"), "w_0weird");
        // Lean keywords must not survive as binder names.
        assert_eq!(lean_name("main.in"), "in_");
        assert_eq!(lean_name("main.fun"), "fun_");
    }

    #[test]
    fn zero_row_is_dropped_and_like_monomials_merge() {
        // (a + b) * 0 = 0 → empty row, dropped.
        // (a)·(a) + (a)·(a) via A = [a, a] duplicates → coefficients merge.
        let cs = vec![
            R1csConstraint {
                a: vec![(1, big(1)), (2, big(1))],
                b: vec![],
                c: vec![],
            },
            R1csConstraint {
                a: vec![(1, big(1)), (1, big(1))],
                b: vec![(1, big(1))],
                c: vec![],
            },
        ];
        let bytes = build_r1cs_bytes(&p(), 8, 3, &cs);
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let gadget = to_gadget(&parsed, &BTreeMap::new(), &ConvertOptions::default()).unwrap();
        assert_eq!(gadget.constraints.len(), 1);
        let terms = &gadget.constraints[0].terms;
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0].coeff, "2"); // merged 1+1
        assert_eq!(terms[0].vars, vec![0, 0]); // a * a
    }

    #[test]
    fn named_unconstrained_sym_wires_are_preserved_as_witnesses() {
        let bytes = build_r1cs_bytes(&p(), 8, 4, &multiplier());
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let sym: BTreeMap<u32, String> = [
            (1, "main.a".to_string()),
            (2, "main.b".to_string()),
            (3, "main.c".to_string()),
            (4, "main.dangling_out".to_string()),
        ]
        .into();
        let mut parsed = parsed;
        parsed.n_wires = 5;

        let gadget = to_gadget(&parsed, &sym, &ConvertOptions::default()).unwrap();
        let names: Vec<&str> = gadget.witnesses.iter().map(|w| w.name.as_str()).collect();

        assert_eq!(names, vec!["a", "b", "c", "dangling_out"]);
    }

    #[test]
    fn repaired_name_collisions_are_deduped_until_unique() {
        let bytes = build_r1cs_bytes(&p(), 8, 4, &multiplier());
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let sym: BTreeMap<u32, String> = [
            (1, "main.a".to_string()),
            (2, "main.a_w3".to_string()),
            (3, "main.a".to_string()),
        ]
        .into();

        let gadget = to_gadget(&parsed, &sym, &ConvertOptions::default()).unwrap();
        let names: Vec<&str> = gadget.witnesses.iter().map(|w| w.name.as_str()).collect();

        assert_eq!(names, vec!["a", "a_w3", "a_w3_2"]);
    }

    #[test]
    fn sym_wire_out_of_range_is_malformed() {
        let bytes = build_r1cs_bytes(&p(), 8, 4, &multiplier());
        let parsed = parse_r1cs_bytes(&bytes).unwrap();
        let sym: BTreeMap<u32, String> = [(4, "main.out_of_range".to_string())].into();

        let err = to_gadget(&parsed, &sym, &ConvertOptions::default()).unwrap_err();

        assert!(matches!(err, R1csError::Malformed(_)));
        assert!(err.to_string().contains(".sym references wire 4"));
    }
}
