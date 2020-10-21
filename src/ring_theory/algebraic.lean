/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.finite_dimensional
import ring_theory.integral_closure
import data.polynomial.integral_normalization

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

universe variables u v

open_locale classical
open polynomial

section
variables (R : Type u) {A : Type v} [comm_ring R] [comm_ring A] [algebra R A]

/-- An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial. -/
def is_algebraic (x : A) : Prop :=
∃ p : polynomial R, p ≠ 0 ∧ aeval x p = 0

variables {R}

/-- A subalgebra is algebraic if all its elements are algebraic. -/
def subalgebra.is_algebraic (S : subalgebra R A) : Prop := ∀ x ∈ S, is_algebraic R x

variables (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
def algebra.is_algebraic : Prop := ∀ x : A, is_algebraic R x

variables {R A}

/-- A subalgebra is algebraic if and only if it is algebraic an algebra. -/
lemma subalgebra.is_algebraic_iff (S : subalgebra R A) :
  S.is_algebraic ↔ @algebra.is_algebraic R S _ _ (S.algebra) :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  rw [subtype.forall'],
  apply forall_congr, rintro ⟨x, hx⟩,
  apply exists_congr, intro p,
  apply and_congr iff.rfl,
  have h : function.injective (S.val) := subtype.val_injective,
  conv_rhs { rw [← h.eq_iff, alg_hom.map_zero], },
  rw [← aeval_alg_hom_apply, S.val_apply]
end

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
lemma algebra.is_algebraic_iff : algebra.is_algebraic R A ↔ (⊤ : subalgebra R A).is_algebraic :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  simp only [algebra.mem_top, forall_prop_of_true, iff_self],
end

end

section zero_ne_one
variables (R : Type u) {A : Type v} [comm_ring R] [nontrivial R] [comm_ring A] [algebra R A]

/-- An integral element of an algebra is algebraic.-/
lemma is_integral.is_algebraic {x : A} (h : is_integral R x) : is_algebraic R x :=
by { rcases h with ⟨p, hp, hpx⟩, exact ⟨p, hp.ne_zero, hpx⟩ }

end zero_ne_one

section field
variables (K : Type u) {A : Type v} [field K] [comm_ring A] [algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
lemma is_algebraic_iff_is_integral {x : A} :
  is_algebraic K x ↔ is_integral K x :=
begin
  refine ⟨_, is_integral.is_algebraic K⟩,
  rintro ⟨p, hp, hpx⟩,
  refine ⟨_, monic_mul_leading_coeff_inv hp, _⟩,
  rw [← aeval_def, alg_hom.map_mul, hpx, zero_mul],
end

end field

namespace algebra
variables {K : Type*} {L : Type*} {A : Type*}
variables [field K] [field L] [comm_ring A]
variables [algebra K L] [algebra L A] [algebra K A] [is_scalar_tower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K A :=
begin
  simp only [is_algebraic, is_algebraic_iff_is_integral] at L_alg A_alg ⊢,
  exact is_integral_trans L_alg A_alg,
end

/-- A field extension is algebraic if it is finite. -/
lemma is_algebraic_of_finite [finite : finite_dimensional K L] : is_algebraic K L :=
λ x, (is_algebraic_iff_is_integral _).mpr (is_integral_of_submodule_noetherian ⊤
  (is_noetherian_of_submodule_of_noetherian _ _ _ finite) x algebra.mem_top)

end algebra

variables {R S : Type*} [integral_domain R] [comm_ring S]

lemma exists_integral_multiple [algebra R S] {z : S} (hz : is_algebraic R z)
  (inj : ∀ x, algebra_map R S x = 0 → x = 0) :
  ∃ (x : integral_closure R S) (y ≠ (0 : integral_closure R S)),
    z * y = x :=
begin
  rcases hz with ⟨p, p_ne_zero, px⟩,
  set n := p.nat_degree with n_def,
  set a := p.leading_coeff with a_def,
  have a_ne_zero : a ≠ 0 := mt polynomial.leading_coeff_eq_zero.mp p_ne_zero,
  have y_integral : is_integral R (algebra_map R S a) := is_integral_algebra_map,
  have x_integral : is_integral R (z * algebra_map R S a) :=
    ⟨ p.integral_normalization,
      monic_integral_normalization p_ne_zero,
      integral_normalization_aeval_eq_zero p_ne_zero px inj ⟩,
  refine ⟨⟨_, x_integral⟩, ⟨_, y_integral⟩, _, rfl⟩,
  exact λ h, a_ne_zero (inj _ (subtype.ext_iff_val.mp h))
end
