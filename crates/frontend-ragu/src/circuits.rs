//! Small ragu circuits used as extraction subjects.
//!
//! These are ordinary `ragu_circuits::Circuit` implementations — nothing in
//! them knows about scribe — written in the same shape as ragu's own test
//! fixtures (`ragu_testing::circuits`). [`BooleanBit`] is the Phase B proof
//! target: it wraps `ragu_primitives::boolean::Boolean::alloc`, the canonical
//! "one gate, two constraints" boolean gadget, and exposes the bit as the
//! circuit's public instance.

use ragu_arithmetic::ff::Field;
use ragu_circuits::{Circuit, WithAux};
use ragu_core::{
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
    Result,
};
use ragu_primitives::{allocator::Standard, Boolean, Element};

/// One boolean bit, public.
///
/// `Boolean::alloc` costs one gate and two constraints: the gate's `a·b = c`
/// with `c` enforced to zero (so `a·b = 0`), plus `a + b = 1` — together
/// forcing `a ∈ {0, 1}`. The bit is the circuit's output, so it is bound into
/// the instance polynomial `k(Y)` and the verifier sees it.
pub struct BooleanBit;

impl<F: Field> Circuit<F> for BooleanBit {
    type Instance<'source> = bool;
    type Witness<'source> = bool;
    type Output = Kind![F; Boolean<'_, _>];
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, bool>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        Boolean::alloc(dr, allocator, instance)
    }

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, bool>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, ()>>> {
        let allocator = &mut Standard::new();
        let bit = Boolean::alloc(dr, allocator, witness)?;
        Ok(WithAux::new(bit, D::unit()))
    }
}

/// Proves knowledge of `x`, `y` with public output `(x + y)²`.
///
/// Deliberately exercises `Driver::add`: the sum `x + y` is a **virtual**
/// wire (a `Definition` in the IR, no constraint), which is then squared
/// through a real gate. Extracted ragu circuits carry definitions whenever a
/// gadget uses free linear combinations — which is most of them.
pub struct SumThenSquare;

impl<F: Field> Circuit<F> for SumThenSquare {
    type Instance<'source> = F;
    type Witness<'source> = (F, F);
    type Output = Kind![F; Element<'_, _>];
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, F>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        Element::alloc(dr, allocator, instance)
    }

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, (F, F)>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, ()>>> {
        let allocator = &mut Standard::new();
        let x = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.0))?;
        let y = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.1))?;
        let sum = x.add(dr, &y); // virtual wire — Definition, no constraint
        let square = sum.square(dr)?;
        Ok(WithAux::new(square, D::unit()))
    }
}

/// Squares a witness element `times` times; the result is public. Same shape
/// as ragu's own `SquareCircuit` fixture — used to check gate/constraint
/// scaling against `ragu_circuits::metrics` at several sizes.
pub struct SquareChain {
    pub times: usize,
}

impl<F: Field> Circuit<F> for SquareChain {
    type Instance<'source> = F;
    type Witness<'source> = F;
    type Output = Kind![F; Element<'_, _>];
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, F>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        Element::alloc(dr, allocator, instance)
    }

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, F>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, ()>>> {
        let allocator = &mut Standard::new();
        let mut acc = Element::alloc(dr, allocator, witness)?;
        for _ in 0..self.times {
            acc = acc.square(dr)?;
        }
        Ok(WithAux::new(acc, D::unit()))
    }
}
