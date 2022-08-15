/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import ring_theory.polynomial.vieta
import field_theory.splitting_field

/-!
# Cubics and discriminants

This file defines discriminants of cubic polynomials over a splitting field.

## Main definitions

* `disc`: the discriminant of a cubic polynomial.

## Main statements

* `disc_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
  the cubic has no duplicate roots.

## References

* https://en.wikipedia.org/wiki/Cubic_equation
* https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/

noncomputable theory

open polynomial
open_locale polynomial big_operators

variables {R S F K : Type*}

section to_poly

section basic
variables [semiring R] {N : ℕ}

/-- Convert a vector to a polynomial. This construction allows one to work with the module of
polynomials of a guaranteed maximal degree, known in mathlib as `degree_lt R`, while retaining easy
access to the coefficients (which for an element `P : ↥(degree_lt R N)` would be accessed with the
more cumbersome invocation `(P : R[X]).coeff`). -/
def to_poly : (fin N → R) →ₗ[R] R[X] :=
(degree_lt R N).subtype.comp (↑(degree_lt_equiv R N).symm : (fin N → R) →ₗ[R] degree_lt R N)

lemma to_poly_apply (P : fin N → R) : to_poly P =  ∑ i : fin N, monomial i (P i) := rfl

@[simp] lemma polynomial.degree_lt_equiv_symm_apply (P : fin N → R) :
  ((degree_lt_equiv R N).symm P : R[X]) = to_poly P :=
rfl

lemma to_poly_mem_degree_lt (P : fin N → R) : to_poly P ∈ degree_lt R N :=
((degree_lt_equiv R N).symm P).prop

variables (R N)

@[simp] lemma to_poly_injective : function.injective (to_poly : (fin N → R) → R[X]) :=
(submodule.injective_subtype (degree_lt R N)).comp (degree_lt_equiv R N).symm.injective

@[simp] lemma to_poly_zero : to_poly (0 : fin N → R) = 0 := (@to_poly R _ _).map_zero

variables {R N}

@[simp] lemma to_poly_eq_iff (P Q : fin N → R) : to_poly P = to_poly Q ↔ P = Q :=
(to_poly_injective R N).eq_iff

@[simp] lemma to_poly_eq_zero_iff (P : fin N → R) : to_poly P = 0 ↔ P = 0 :=
by rw [← to_poly_zero, to_poly_eq_iff]

lemma map_to_poly [semiring S] {P : fin N → R} {φ : R →+* S} :
  to_poly (φ ∘ P) = polynomial.map φ (to_poly P) :=
by simp [to_poly_apply, polynomial.map_sum]

/-! ### Coefficients -/

section coeff
variables {P : fin N → R}

lemma coeff_to_poly_ge_four (P : fin N → R) (n : ℕ) (hn : N ≤ n) : (to_poly P).coeff n = 0 :=
(submodule.mem_infi _).mp ((submodule.mem_infi _).mp (to_poly_mem_degree_lt P) n : _ ∈ _) hn

@[simp] lemma coeff_to_poly_le_three (P : fin N → R) (n : fin N) : (to_poly P).coeff n = P n :=
by simp [to_poly_apply, coeff_monomial, set_coe.ext_iff, finset.sum_ite_eq']

end coeff

/-! ### Degrees -/

section degree

lemma degree_to_poly_lt (P : fin N → R) : (to_poly P).degree < N :=
by simpa [mem_degree_lt] using to_poly_mem_degree_lt P

variables (P : fin N.succ → R)

lemma degree_to_poly_le : (to_poly P).degree ≤ N :=
(degree_le_iff_coeff_zero _ _).mpr (λ m hm, coeff_to_poly_ge_four P m (by simpa using hm))

lemma nat_degree_to_poly_le : (to_poly P).nat_degree ≤ N :=
begin
  by_cases hP : to_poly P = 0,
  { simp [hP] },
  simpa [degree_eq_nat_degree hP] using degree_to_poly_le P,
end

variables {P}

lemma degree_to_poly (ha : P N ≠ 0) : (to_poly P).degree = N :=
le_antisymm (degree_to_poly_le P) $
calc (N : with_bot ℕ) = _ : congr_arg some (fin.coe_coe_of_lt (nat.lt.base N)).symm
... ≤ (to_poly P).degree : le_degree_of_ne_zero (by rwa ← coeff_to_poly_le_three P at ha)

lemma nat_degree_to_poly (ha : P N ≠ 0) : (to_poly P).nat_degree = N :=
le_antisymm (nat_degree_to_poly_le P) $
calc N = _ : (fin.coe_coe_of_lt (nat.lt.base N)).symm
... ≤ _ : le_nat_degree_of_ne_zero (by rwa ← coeff_to_poly_le_three P at ha)

lemma leading_coeff (ha : P N ≠ 0) : (to_poly P).leading_coeff = P N :=
by rw [leading_coeff, nat_degree_to_poly ha, ← coeff_to_poly_le_three P,
  fin.coe_coe_of_lt (nat.lt.base N)]

end degree

end basic

section roots

open multiset

/-! ### Roots over an extension -/

section extension
variables [comm_ring R] [comm_ring S] {N: ℕ} {P : fin N → R} {φ : R →+* S}

theorem mem_roots_to_poly_iff [is_domain R] (h0 : to_poly P ≠ 0) (x : R) :
  x ∈ (to_poly P).roots ↔ ∑ i, P i * x ^ (i:ℕ) = 0 :=
begin
  rw [mem_roots h0, is_root, to_poly_apply, eval_finset_sum],
  simp only [eval_monomial],
end

theorem card_roots_to_poly_le {P : fin N.succ → R} [is_domain R] [decidable_eq R] :
  (to_poly P).roots.to_finset.card ≤ N :=
(to_finset_card_le (to_poly P).roots).trans $
(card_roots' (to_poly P)).trans $ nat_degree_to_poly_le P

end extension

/-! ### Roots over a splitting field -/

section split
variables [field F] [field K] {N : ℕ} {P : fin N.succ → F} {φ : F →+* K} {x y z : K}

theorem to_poly_splits_iff_card_roots (ha : P N ≠ 0) :
  splits φ (to_poly P) ↔ (to_poly (φ ∘ P)).roots.card = N :=
begin
  replace ha : (φ ∘ P) N ≠ 0 := φ.map_ne_zero.mpr ha,
  nth_rewrite_lhs 0 [← φ.id_comp],
  rwa [← splits_map_iff, ← map_to_poly, splits_iff_card_roots, nat_degree_to_poly],
end

lemma vieta_to_poly {P : fin N.succ → F} (ha : P N ≠ 0) (hP : splits φ (to_poly P))
  (k : fin N.succ) :
  φ (P k)
  = φ (P N) * (-1) ^ (N - k)
    * (((to_poly (φ ∘ P)).roots.powerset_len (N - k)).map multiset.prod).sum :=
begin
  rw [to_poly_splits_iff_card_roots ha, map_to_poly] at hP,
  convert @vieta K _ _ (map φ (to_poly P)) _ k _;
  simp [leading_coeff ha, nat_degree_to_poly ha, fin.is_le k, hP, map_to_poly]
end

end split

end roots

end to_poly

namespace cubic

open polynomial multiset

variables [field F] [field K] {P : fin 4 → F}  {φ : F →+* K} {x y z : K}

section roots

/-! ### Roots over a splitting field -/

section split

theorem splits_iff_roots_eq_three (ha : P 3 ≠ 0) :
  splits φ (to_poly P) ↔ ∃ x y z : K, (to_poly (φ ∘ P)).roots = {x, y, z} :=
by { rw [to_poly_splits_iff_card_roots ha], norm_num, rw [card_eq_three], refl }

theorem splits_of_three_roots (ha : P 3 ≠ 0) {x y z : K}
  (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  splits φ (to_poly P) :=
(splits_iff_roots_eq_three ha).mpr ⟨x, y, z, h3⟩

theorem eq_prod_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  to_poly (φ ∘ P) = C (φ (P 3)) * (X - C x) * (X - C y) * (X - C z) :=
begin
  rw [map_to_poly, eq_prod_roots_of_splits $ splits_of_three_roots ha h3,
    leading_coeff ha, ← map_to_poly, h3],
  change C (φ (P 3)) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _,
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
end

theorem b_eq_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (P 2) = φ (P 3) * -(x + y + z) :=
calc φ (P 2) = - φ (P 3) * (z + y + x) : by
          { rw vieta_to_poly ha (splits_of_three_roots ha h3), norm_num [h3] }
... = _ : by ring

theorem c_eq_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (P 1) = φ (P 3) * (x * y + x * z + y * z) :=
calc φ (P 1) = φ (P 3) * (y * z + (x * z + x * y)) : by
          { rw vieta_to_poly ha (splits_of_three_roots ha h3), norm_num [h3] }
... = _ : by ring

theorem d_eq_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (P 0) = φ (P 3) * -(x * y * z) :=
calc φ (P 0) = -(φ (P 3) * (x * (y * z))) : by
          { rw vieta_to_poly ha (splits_of_three_roots ha h3), norm_num [h3] }
... = _ : by ring

end split

/-! ### Discriminant over a splitting field -/

section discriminant

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [ring R] (P : fin 4 → R) : R :=
P 2 ^ 2 * P 1 ^ 2 - 4 * P 3 * P 1 ^ 3 - 4 * P 2 ^ 3 * P 0 - 27 * P 3 ^ 2 * P 0 ^ 2
  + 18 * P 3 * P 2 * P 1 * P 0

theorem disc_eq_prod_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (disc P) = (φ (P 3) * φ (P 3) * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3],
  ring1
end

theorem disc_ne_zero_iff_roots_ne (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  disc P ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z :=
begin
  rw [← ring_hom.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two],
  simp only [mul_ne_zero_iff, sub_ne_zero],
  rw [ring_hom.map_ne_zero],
  tautology
end

theorem disc_ne_zero_iff_roots_nodup (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  disc P ≠ 0 ↔ (to_poly (φ ∘ P)).roots.nodup :=
begin
  rw [disc_ne_zero_iff_roots_ne ha h3, h3],
  change _ ↔ (x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem card_roots_of_disc_ne_zero [decidable_eq K] (ha : P 3 ≠ 0)
  (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) (hd : disc P ≠ 0) :
  (to_poly (φ ∘ P)).roots.to_finset.card = 3 :=
begin
  rw [to_finset_card_of_nodup $ (disc_ne_zero_iff_roots_nodup ha h3).mp hd,
        ← @to_poly_splits_iff_card_roots F K _ _ 3 P φ ha, splits_iff_roots_eq_three ha],
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩
end

end discriminant

end roots

end cubic
