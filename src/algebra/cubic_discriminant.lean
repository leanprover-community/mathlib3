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

variables {N : ℕ}

namespace vec_polynomial

/- Convert a vector to a polynomial. -/
def to_poly {R : Type*} [semiring R] {N : ℕ} (P : fin N → R) : R[X] := ∑ i : fin N, monomial i (P i)

@[simp] lemma degree_lt_equiv_symm_apply [semiring R] (P : fin N → R) :
  ((degree_lt_equiv R N).to_equiv.symm P : R[X]) = to_poly P :=
rfl

lemma to_poly_mem_degree_lt [semiring R] (P : fin N → R) : to_poly P ∈ degree_lt R N :=
((degree_lt_equiv R N).symm P).prop

section basic
variables [semiring R]

/-! ### Coefficients -/

section coeff
variables {P : fin N → R}

lemma coeff_gt_three (P : fin N.succ → R) (n : ℕ) (hn : N < n) :
  (to_poly P).coeff n = 0 :=
(submodule.mem_infi _).mp ((submodule.mem_infi _).mp (to_poly_mem_degree_lt P) n : _ ∈ _) hn

@[simp] lemma coeff_le_three (P : fin N → R) (n : fin N) :
  (to_poly P).coeff n = P n :=
begin
  rw ← degree_lt_equiv_symm_apply,
end

@[simp] lemma to_poly_injective (P Q : fin N → R) : to_poly P = to_poly Q ↔ P = Q :=
⟨λ h, by { ext i, rw [← coeff_le_three P, ← coeff_le_three Q, h] }, congr_arg _⟩

@[simp] lemma of_zero (ha : P = 0) : to_poly P = 0 := by simp [ha, ← degree_lt_equiv_symm_apply]

@[simp] lemma zero : to_poly (0 : fin N → R) = 0 := of_zero rfl

@[simp] lemma eq_zero_iff : (to_poly P) = 0 ↔ P = 0 := by rw [← zero, to_poly_injective]

end coeff

/-! ### Degrees -/

section degree
variables (P : fin N.succ → R)

lemma degree_le : (to_poly P).degree ≤ N :=
(degree_le_iff_coeff_zero _ _).mpr (λ m hm, coeff_gt_three P m (by simpa using hm))

lemma nat_degree_le : (to_poly P).nat_degree ≤ N :=
begin
  by_cases hP : to_poly P = 0,
  { have hP' : P = 0 := by simpa [eq_zero_iff] using hP,
    simp [hP'] },
  simpa [degree_eq_nat_degree hP] using degree_le P,
end

variables {P}

lemma degree (ha : P N ≠ 0) : (to_poly P).degree = N :=
begin
  refine le_antisymm (degree_le P) _,
  rw ← coeff_le_three P at ha,
  have := le_degree_of_ne_zero ha,
  convert this,
  -- library_search
end

lemma degree_of_zero (hP : P = 0) : (to_poly P).degree = ⊥ := by rwa [of_zero, degree_zero]

lemma leading_coeff (ha : P N ≠ 0) : (to_poly P).leading_coeff = P N := sorry --leading_coeff_cubic ha

end degree

/-! ### Map across a homomorphism -/

section map

variables {P : fin N → R} [semiring S] {φ : R →+* S}

lemma map_to_poly : to_poly (φ ∘ P) = polynomial.map φ (to_poly P) :=
by simp [to_poly, polynomial.map_sum]

end map

end basic

section roots

open multiset

/-! ### Roots over an extension -/

section extension

variables {P : fin N → R} [comm_ring R] [comm_ring S] {φ : R →+* S}

theorem mem_roots_iff [is_domain R] (h0 : (to_poly P) ≠ 0) (x : R) :
  x ∈ (to_poly P).roots ↔ ∑ i, P i * x ^ (i:ℕ) = 0 :=
begin
  rw [mem_roots h0, is_root, to_poly, eval_finset_sum],
  simp only [eval_monomial],
end

theorem card_roots_le {P : fin N.succ → R} [is_domain R] [decidable_eq R] :
  (to_poly P).roots.to_finset.card ≤ N :=
begin
  apply (to_finset_card_le (to_poly P).roots).trans,
  by_cases hP : (to_poly P) = 0,
  { exact (card_roots' (to_poly P)).trans (by { rw [hP, nat_degree_zero], exact zero_le N }) },
  { exact with_bot.coe_le_coe.1 ((card_roots hP).trans degree_le) },
end

end extension

variables {P : fin N.succ → F} [field F] [field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/

section split

theorem splits_iff_card_roots (ha : P N ≠ 0) :
  splits φ (to_poly P) ↔ (to_poly (φ ∘ P)).roots.card = N :=
begin
  replace ha : (φ ∘ P) N ≠ 0 := (ring_hom.map_ne_zero φ).mpr ha,
  nth_rewrite_lhs 0 [← ring_hom.id_comp φ],
  rw [← splits_map_iff, ← map_to_poly, splits_iff_card_roots,
      ← ((degree_eq_iff_nat_degree_eq $ ne_zero_of_a_ne_zero ha).mp $ degree ha : _ = 3)]
end

lemma vieta {P : fin N.succ → F} (hP : splits φ (to_poly P)) (k : fin N.succ) :
  φ (P k)
  = (-1) ^ (N - k) * φ (P N) * (((to_poly (φ ∘ P)).roots.powerset_len (N - k)).map multiset.prod).sum :=
sorry
  -- (finset.univ.prod (λ (i : σ), ⇑polynomial.C (r i) + polynomial.X)).coeff k = (finset.powerset_len (fintype.card σ - k) finset.univ).sum (λ (t : finset σ), t.prod (λ (i : σ), r i))


end split

end roots

end vec_polynomial


namespace cubic

open polynomial vec_polynomial multiset

variables {P : fin 4 → F} [field F] [field K] {φ : F →+* K} {x y z : K}

section roots

/-! ### Roots of a cubic over a splitting field -/

section split

theorem splits_iff_roots_eq_three (ha : P 3 ≠ 0) :
  splits φ (to_poly P) ↔ ∃ x y z : K, (to_poly (φ ∘ P)).roots = {x, y, z} :=
by { rw [splits_iff_card_roots ha], norm_num, rw [card_eq_three], refl }

theorem splits_of_three_roots (ha : P 3 ≠ 0) {x y z : K} (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
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

-- move this
@[simp] lemma foo {α : Type*} (a : α) : powerset_len 1 ({a} : multiset α) = {{a}} := sorry

theorem b_eq_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (P 2) = φ (P 3) * -(x + y + z) :=
calc φ (P 2) = - φ (P 3) * (z + y + x) : by { rw vieta (splits_of_three_roots ha h3), simp [h3] }
... = _ : by ring

theorem c_eq_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (P 1) = φ (P 3) * (x * y + x * z + y * z) :=
calc φ (P 1) = φ (P 3) * (y * z + (x * z + x * y)) : by { rw vieta (splits_of_three_roots ha h3), simp [h3] }
... = _ : by ring

theorem d_eq_three_roots (ha : P 3 ≠ 0) (h3 : (to_poly (φ ∘ P)).roots = {x, y, z}) :
  φ (P 0) = φ (P 3) * -(x * y * z) :=
calc φ (P 0) = -(φ (P 3) * (x * (y * z))) : by { rw vieta (splits_of_three_roots ha h3), simp [h3] }
... = _ : by ring

end split

/-! ### Discriminant of a cubic over a splitting field -/

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
        ← @vec_polynomial.splits_iff_card_roots F K 3 P _ _ φ ha, splits_iff_roots_eq_three ha],
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩
end

end discriminant

end roots

end cubic
