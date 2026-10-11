//! A fixed, witness-independent polynomial slice using Ragu's real `Element::fold`.
//! Coefficients are supplied in descending order: `[a₂, a₁, a₀]`.
use ragu_arithmetic::ff::Field;
use ragu_circuits::{Circuit, WithAux};
use ragu_core::{
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
    Result,
};
use ragu_primitives::{allocator::Standard, Element};

pub struct HornerThree;

impl<F: Field> Circuit<F> for HornerThree {
    type Instance<'source> = F;
    type Witness<'source> = [F; 4];
    type Output = Kind![F; Element<'_, _>];
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, F>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Element::alloc(dr, &mut Standard::new(), instance)
    }

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, [F; 4]>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, ()>>> {
        let allocator = &mut Standard::new();
        let a2 = Element::alloc(dr, allocator, witness.as_ref().map(|w| w[0]))?;
        let a1 = Element::alloc(dr, allocator, witness.as_ref().map(|w| w[1]))?;
        let a0 = Element::alloc(dr, allocator, witness.as_ref().map(|w| w[2]))?;
        let x = Element::alloc(dr, allocator, witness.as_ref().map(|w| w[3]))?;
        let result = Element::fold(dr, [&a2, &a1, &a0], &x)?;
        Ok(WithAux::new(result, D::unit()))
    }
}
