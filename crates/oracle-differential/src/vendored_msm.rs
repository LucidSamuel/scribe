//! The reference MSM, vendored verbatim from ragu, plus the planted defects
//! that form the negative half of the `corpus/msm` corpus.
//!
//! # Provenance
//!
//! Vendored from `crates/ragu_arithmetic/src/util.rs` (`bucket_lookup` and
//! `msm`) at ragu revision `fc61822cf8c248d36b950c89817bf170d533a7f3`
//! (`origin/main` of <https://github.com/tachyon-zcash/ragu>, the Phase C
//! audit revision). Vendoring instead of depending: ragu pins rustc 1.97
//! while this workspace pins 1.90.0, so a path/git dependency cannot build
//! here (see Cargo.toml).
//!
//! Two deliberate deltas from upstream, both semantics-preserving:
//!
//! 1. Window sums run sequentially. Upstream maps windows through the
//!    `maybe-rayon` facade (`into_par_iter`), which is itself sequential
//!    unless ragu's `multicore` feature is enabled; parallelism never changes
//!    the result, only the schedule.
//! 2. The `CurveAffine` trait comes from crates.io `pasta_curves 0.5.1`
//!    rather than ragu's pinned fork of the same crate (the fork's MSRV also
//!    exceeds 1.90). `msm` is generic over `CurveAffine` and touches no
//!    fork-specific API.
//!
//! # Defects
//!
//! [`msm_with_defect`] is the same function with three marked divergence
//! points, selected by [`Defect`]. `Defect::None` is the reference. Each
//! defect is a single-line divergence, commented `PLANTED DEFECT` at the
//! site. This is the same planted-defect discipline ragu itself practices
//! (`PATCHER_SELFTEST` in `qa/fuzz`), extended to a surface it has not been
//! applied to: input-size coverage of the MSM window strategy.

use ff::PrimeField;
use group::Group;
use pasta_curves::arithmetic::CurveAffine;

/// Which planted defect to enable. `None` reproduces upstream `msm` exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Defect {
    /// No defect: the vendored reference.
    None,
    /// Wide-window undercount: in the final window-combination loop, perform
    /// `c - 1` doublings instead of `c` — but only when `bucket_lookup`
    /// selected a window width of 11 bits or more, i.e. only when
    /// `n >= 22027`. This is the mutant planted in a demonstrably unreached
    /// path: no ragu rank `<= R<14>` can produce an MSM that large
    /// (`R::num_coeffs() = 2^rank` caps the commit-side MSM, and the only
    /// other call site is a ~108-term decomposition MSM), and the largest
    /// MSM the fuzz fleet actually performs is n = 5507 (measured: the
    /// `ProductionRank` trivial-proof build in `fuzz_verify_reject`; see
    /// `docs/v2.1/equivalence-notes.md`).
    WideWindowSkipDouble,
    /// Bucket-collision drop: the `Bucket::Affine -> Bucket::Projective`
    /// transition forgets the point already in the bucket. Wrong whenever any
    /// bucket receives two or more points in some window — near-certain for
    /// random full-width scalars at any `n >= 2`.
    BucketCollisionDrop,
    /// Window-boundary shift drop: `get_at` skips the sub-byte right shift,
    /// so any window that does not start on a byte boundary reads the wrong
    /// bits. Wrong for essentially any input at any `n`.
    WindowShiftDrop,
}

/// Upstream `bucket_lookup` (verbatim): given a number of scalars, returns
/// the window size in bits selected for the multiexp.
///
/// The 15-entry threshold table partitions `n` into 16 bands (`c = 1..=16`);
/// the `c = 2` band is empty because the first two thresholds are both 4.
pub fn bucket_lookup(n: usize) -> usize {
    const LN_THRESHOLDS: [usize; 15] = [
        4, 4, 32, 55, 149, 404, 1097, 2981, 8104, 22027, 59875, 162755, 442414, 1202605, 3269018,
    ];

    let mut cur = 1;
    for &threshold in LN_THRESHOLDS.iter() {
        if n < threshold {
            return cur;
        }

        cur += 1;
    }
    cur
}

/// Upstream `msm` with the [`Defect`] divergence points. See module docs for
/// provenance and deltas.
pub fn msm_with_defect<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    defect: Defect,
) -> C::Curve {
    let c = bucket_lookup(coeffs.len());
    msm_core(coeffs, bases, c, defect)
}

/// The windowed algorithm with an explicit window width instead of the
/// `bucket_lookup` selection. Any `1 <= c <= 16` computes the same sum, so
/// running a deliberately different `c` than the reference selects is a
/// correct-by-construction metamorphic candidate (used as the corpus
/// positive).
pub fn msm_windowed_with_c<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    c: usize,
) -> C::Curve {
    assert!(
        (1..=16).contains(&c),
        "get_at reads 4 bytes; c must be <= 16"
    );
    msm_core(coeffs, bases, c, Defect::None)
}

pub(crate) fn msm_core<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    c: usize,
    defect: Defect,
) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();

    fn get_at<F: PrimeField>(segment: usize, c: usize, bytes: &F::Repr, defect: Defect) -> usize {
        let skip_bits = segment * c;
        let skip_bytes = skip_bits / 8;

        if skip_bytes >= bytes.as_ref().len() {
            return 0;
        }

        // 4 bytes suffices since bucket_lookup returns at most 16.
        let mut v = [0; 4];
        for (v, o) in v.iter_mut().zip(bytes.as_ref()[skip_bytes..].iter()) {
            *v = *o;
        }

        let mut tmp = u32::from_le_bytes(v);
        if defect != Defect::WindowShiftDrop {
            tmp >>= skip_bits - (skip_bytes * 8);
        } // PLANTED DEFECT (WindowShiftDrop): sub-byte shift skipped.
        tmp %= 1 << c;

        tmp as usize
    }

    let segments = (C::Scalar::NUM_BITS as usize).div_ceil(c);

    #[derive(Clone, Copy)]
    enum Bucket<C: CurveAffine> {
        None,
        Affine(C),
        Projective(C::Curve),
    }

    impl<C: CurveAffine> Bucket<C> {
        fn add_assign(&mut self, other: &C, defect: Defect) {
            *self = match *self {
                Bucket::None => Bucket::Affine(*other),
                Bucket::Affine(a) => {
                    if defect == Defect::BucketCollisionDrop {
                        // PLANTED DEFECT: forgets the point already present.
                        Bucket::Projective(other.to_curve())
                    } else {
                        Bucket::Projective(a + *other)
                    }
                }
                Bucket::Projective(mut a) => {
                    a += *other;
                    Bucket::Projective(a)
                }
            }
        }

        fn add(self, mut other: C::Curve) -> C::Curve {
            match self {
                Bucket::None => other,
                Bucket::Affine(a) => {
                    other += a;
                    other
                }
                Bucket::Projective(a) => other + a,
            }
        }
    }

    /// Compute the bucket sum for a single window segment.
    fn window_sum<C: CurveAffine>(
        current_segment: usize,
        c: usize,
        coeffs: &[<C::Scalar as PrimeField>::Repr],
        bases: &[C],
        defect: Defect,
    ) -> C::Curve {
        let mut buckets: Vec<Bucket<C>> = vec![Bucket::None; (1 << c) - 1];

        for (coeff, base) in coeffs.iter().zip(bases) {
            let coeff = get_at::<C::Scalar>(current_segment, c, coeff, defect);
            if coeff != 0 {
                buckets[coeff - 1].add_assign(base, defect);
            }
        }

        // Summation by parts
        // e.g. 3a + 2b + 1c = a +
        //                    (a) + b +
        //                    ((a) + b) + c
        let mut running_sum = C::Curve::identity();
        let mut sum = C::Curve::identity();
        for exp in buckets.into_iter().rev() {
            running_sum = exp.add(running_sum);
            sum += &running_sum;
        }
        sum
    }

    // Upstream parallelizes this map through the maybe-rayon facade; run it
    // sequentially (delta 1 in the module docs).
    let window_sums: Vec<C::Curve> = (0..segments)
        .map(|seg| window_sum(seg, c, &coeffs, bases, defect))
        .collect();

    // Combine window sums sequentially, from most significant to least.
    let doublings = if defect == Defect::WideWindowSkipDouble && c >= 11 {
        // PLANTED DEFECT: one doubling short, only in wide-window bands
        // (bucket_lookup selects c >= 11 only for n >= 22027).
        c - 1
    } else {
        c
    };
    let mut acc = C::Curve::identity();
    for sum in window_sums.into_iter().rev() {
        for _ in 0..doublings {
            acc = acc.double();
        }
        acc += &sum;
    }

    acc
}

/// The vendored reference: upstream `msm` with no defect.
pub fn msm_reference<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    msm_with_defect(coeffs, bases, Defect::None)
}

/// An independent check implementation: the textbook sum of scalar
/// multiplications, sharing no code or structure with the windowed bucket
/// method. The unit tests compare it against the vendored reference at small
/// sizes, cross-checking the vendored copy itself; the corpus positive uses
/// the cheaper metamorphic shifted-window candidate instead, because the
/// textbook method is quadratically slower at the fleet's largest size.
pub fn msm_naive<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    coeffs
        .iter()
        .zip(bases.iter())
        .fold(C::Curve::identity(), |acc, (s, p)| acc + p.to_curve() * s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Affine, MsmInputs};

    fn inputs(n: usize) -> MsmInputs {
        MsmInputs::generate(0xC0FFEE, vec![n])
    }

    fn slices(inputs: &MsmInputs, n: usize) -> (&[crate::Scalar], &[Affine]) {
        inputs.test_slice(n)
    }

    /// The 15-entry threshold table partitions n into these bands. Band
    /// c = 2 is unreachable (the first two thresholds are both 4); the
    /// c >= 11 bands require n >= 22027, which no ragu rank <= R<14> can
    /// produce — the fact the escaped corpus mutant relies on.
    #[test]
    fn bucket_lookup_band_edges() {
        for (n, c) in [
            (0, 1),
            (3, 1),
            (4, 3),
            (31, 3),
            (32, 4),
            (54, 4),
            (55, 5),
            (128, 5),
            (148, 5),
            (149, 6),
            (1096, 7),
            (1097, 8),
            (8103, 9),
            (8104, 10),
            (8192, 10),
            (22026, 10),
            (22027, 11),
            (3269018, 16),
        ] {
            assert_eq!(bucket_lookup(n), c, "bucket_lookup({n})");
        }
    }

    /// The vendored copy agrees with an algorithm that shares none of its
    /// structure, across every band the corpus input sizes can select at
    /// small n. This is the check that the vendoring itself is faithful.
    #[test]
    fn naive_agrees_with_reference_across_small_bands() {
        let inputs = inputs(160);
        for n in [1, 2, 3, 4, 31, 32, 55, 128, 149, 160] {
            let (coeffs, bases) = slices(&inputs, n);
            assert_eq!(
                msm_naive(coeffs, bases),
                msm_reference(coeffs, bases),
                "n = {n}"
            );
        }
    }

    /// Any window width computes the same sum — the property the corpus
    /// positive (shifted-window candidate) rests on.
    #[test]
    fn every_window_width_agrees() {
        let inputs = inputs(64);
        let (coeffs, bases) = slices(&inputs, 64);
        let expected = msm_naive(coeffs, bases);
        for c in 1..=16 {
            assert_eq!(msm_windowed_with_c(coeffs, bases, c), expected, "c = {c}");
        }
    }

    /// The escaped mutant is a real defect, not a no-op: with its gate
    /// condition (c >= 11) met, it computes a wrong answer. Forcing c = 11
    /// at small n keeps this cheap; `bucket_lookup_band_edges` pins the
    /// public-path link that n >= 22027 selects c = 11.
    #[test]
    fn wide_window_defect_is_real_once_gated_path_is_entered() {
        let inputs = inputs(100);
        let (coeffs, bases) = slices(&inputs, 100);
        let good = msm_core(coeffs, bases, 11, Defect::None);
        let bad = msm_core(coeffs, bases, 11, Defect::WideWindowSkipDouble);
        assert_ne!(good, bad);
        // ... and below its gate it is byte-identical to the reference,
        // which is why the fleet-shaped input distribution cannot see it.
        assert_eq!(
            msm_with_defect(coeffs, bases, Defect::WideWindowSkipDouble),
            msm_reference(coeffs, bases)
        );
    }

    #[test]
    fn caught_mutants_are_real_defects_at_fleet_sizes() {
        let inputs = inputs(48);
        let (coeffs, bases) = slices(&inputs, 48);
        let good = msm_reference(coeffs, bases);
        assert_ne!(
            msm_with_defect(coeffs, bases, Defect::BucketCollisionDrop),
            good
        );
        assert_ne!(
            msm_with_defect(coeffs, bases, Defect::WindowShiftDrop),
            good
        );
    }
}
