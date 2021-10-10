/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import algebra.star.basic
import data.equiv.module

/-!
# The star operation, bundled as a star-linear equiv

We define `star_linear_equiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

## TODO

- We only define it for commutative `R` for now; the noncommutative case would require
  using `star_ring_equiv` between `R` and `Rᵒᵖ`, which is undesirable in the commutative case.
-/

/-- If `A` is a left- and right- module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
def star_linear_equiv {R : Type*} {A : Type*}
  [comm_ring R] [star_ring R] [semiring A] [star_ring A] [module R A] [star_module R A]  :
    A ≃ₛₗ[((star_ring_aut : ring_aut R) : R →+* R)] A :=
{ to_fun := star,
  map_smul' := star_smul,
  .. star_add_equiv }
