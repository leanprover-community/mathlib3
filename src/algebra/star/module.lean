/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/

import algebra.star.basic
import data.equiv.module

/-- If `A` is a left- and right- module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
def star_linear_equiv {R : Type*} {A : Type*}
  [comm_ring R] [star_ring R] [semiring A] [star_ring A] [module R A] [star_module R A]  :
    A ≃ₛₗ[((star_ring_aut : ring_aut R) : R →+* R)] A :=
{ to_fun := star,
  map_smul' := star_smul,
  .. star_add_equiv }
