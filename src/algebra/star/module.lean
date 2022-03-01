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

- Define `star_linear_equiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `is_op R S` and have an instance `is_op R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵒᵖ` or `is_op R S` would require adding
  the appropriate `ring_hom_inv_pair` instances to be able to define the semilinear
  equivalence.
-/

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
def star_linear_equiv {R : Type*} {A : Type*}
  [comm_ring R] [star_ring R] [semiring A] [star_ring A] [module R A] [star_module R A]  :
    A ≃ₛₗ[((star_ring_aut : ring_aut R) : R →+* R)] A :=
{ to_fun := star,
  map_smul' := star_smul,
  .. star_add_equiv }
