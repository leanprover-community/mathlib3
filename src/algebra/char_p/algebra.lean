/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
import algebra.char_p.basic
import ring_theory.localization.fraction_ring
import algebra.free_algebra


/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `fraction_ring R`.


## Main results

- `char_p_of_injective_algebra_map` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `free_algebra R X` has the same characteristic as `R`.
- The `fraction_ring R` of an integral domain `R` has the same characteristic as `R`.

-/


/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
lemma char_p_of_injective_algebra_map {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (h : function.injective (algebra_map R A)) (p : ℕ) [char_p R p] : char_p A p :=
{ cast_eq_zero_iff := λx,
  begin
    rw ←char_p.cast_eq_zero_iff R p x,
    change algebra_map ℕ A x = 0 ↔ algebra_map ℕ R x = 0,
    rw is_scalar_tower.algebra_map_apply ℕ R A x,
    refine iff.trans _ h.eq_iff,
    rw ring_hom.map_zero,
  end }

lemma char_p_of_injective_algebra_map' (R A : Type*) [field R] [semiring A] [algebra R A]
  [nontrivial A] (p : ℕ) [char_p R p] : char_p A p :=
char_p_of_injective_algebra_map (algebra_map R A).injective p

/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
lemma char_zero_of_injective_algebra_map {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (h : function.injective (algebra_map R A)) [char_zero R] : char_zero A :=
{ cast_injective := λ x y hxy,
  begin
    change algebra_map ℕ A x = algebra_map ℕ A y at hxy,
    rw is_scalar_tower.algebra_map_apply ℕ R A x at hxy,
    rw is_scalar_tower.algebra_map_apply ℕ R A y at hxy,
    exact char_zero.cast_injective (h hxy),
  end }
-- `char_p.char_p_to_char_zero A _ (char_p_of_injective_algebra_map h 0)` does not work
-- here as it would require `ring A`.

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/
section Q_algebra

variables (R : Type*) [nontrivial R]

/-- A nontrivial `ℚ`-algebra has `char_p` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebra_rat`. It's probably easier to go the other way: prove `char_zero R` and
automatically receive an `algebra ℚ R` instance.
-/
lemma algebra_rat.char_p_zero [semiring R] [algebra ℚ R] : char_p R 0 :=
char_p_of_injective_algebra_map (algebra_map ℚ R).injective 0

/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebra_rat`. It's probably easier to go the other way: prove `char_zero R` and
automatically receive an `algebra ℚ R` instance.
-/
lemma algebra_rat.char_zero [ring R] [algebra ℚ R] : char_zero R :=
@char_p.char_p_to_char_zero R _ (algebra_rat.char_p_zero R)

end Q_algebra

/-!
An algebra over a field has the same characteristic as the field.
-/
section

variables (K L : Type*) [field K] [comm_semiring L] [nontrivial L] [algebra K L]

lemma algebra.char_p_iff (p : ℕ) : char_p K p ↔ char_p L p :=
(algebra_map K L).char_p_iff_char_p p

lemma algebra.ring_char_eq : ring_char K = ring_char L :=
by { rw [ring_char.eq_iff, algebra.char_p_iff K L], apply ring_char.char_p }

end

namespace free_algebra

variables {R X : Type*} [comm_semiring R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `free_algebra R X`. -/
instance char_p [char_p R p] : char_p (free_algebra R X) p :=
char_p_of_injective_algebra_map free_algebra.algebra_map_left_inverse.injective p

/-- If `R` has characteristic `0`, then so does `free_algebra R X`. -/
instance char_zero [char_zero R] : char_zero (free_algebra R X) :=
char_zero_of_injective_algebra_map free_algebra.algebra_map_left_inverse.injective

end free_algebra

namespace is_fraction_ring

variables (R : Type*) {K : Type*} [comm_ring R]
  [field K] [algebra R K] [is_fraction_ring R K]
variables (p : ℕ)

/-- If `R` has characteristic `p`, then so does Frac(R). -/
lemma char_p_of_is_fraction_ring [char_p R p] : char_p K p :=
char_p_of_injective_algebra_map (is_fraction_ring.injective R K) p

/-- If `R` has characteristic `0`, then so does Frac(R). -/
lemma char_zero_of_is_fraction_ring [char_zero R] : char_zero K :=
@char_p.char_p_to_char_zero K _ (char_p_of_is_fraction_ring R 0)

variables [is_domain R]

/-- If `R` has characteristic `p`, then so does `fraction_ring R`. -/
instance char_p [char_p R p] : char_p (fraction_ring R) p :=
char_p_of_is_fraction_ring R p

/-- If `R` has characteristic `0`, then so does `fraction_ring R`. -/
instance char_zero [char_zero R] : char_zero (fraction_ring R) :=
char_zero_of_is_fraction_ring R

end is_fraction_ring
