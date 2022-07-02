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

lemma to_poly_mem_degree_lt (P : degree_lt R N) : (P : R[X]) ∈ degree_lt R N := P.prop

variables (R N)

variables {R N}

def degree_lt.map [semiring S] (P : degree_lt R N) (φ : R →+* S) : degree_lt S N :=
⟨(P : R[X]).map φ, sorry⟩

postfix `#`:1000 := degree_lt.map

@[simp] lemma map_to_poly [semiring S] {P : degree_lt R N} {φ : R →+* S} :
  (P# φ : S[X]) = (P : R[X]).map φ :=
sorry

/-! ### Coefficients -/

section coeff
variables {P : degree_lt R N}

postfix `ᗮ`:1000 := polynomial.coeff ∘ (@degree_lt _ _ _).subtype

lemma coeff_to_poly_ge_four (P : degree_lt R N) (n : ℕ) (hn : N ≤ n) : Pᗮ n = 0 :=
(submodule.mem_infi _).mp ((submodule.mem_infi _).mp (to_poly_mem_degree_lt P) n : _ ∈ _) hn

end coeff

/-! ### Degrees -/

section degree

lemma degree_to_poly_lt (P : degree_lt R N) : (P : R[X]).degree < N :=
by simpa [mem_degree_lt] using to_poly_mem_degree_lt P

variables (P : degree_lt R N.succ)

lemma degree_to_poly_le : (P : R[X]).degree ≤ N :=
(degree_le_iff_coeff_zero _ _).mpr (λ m hm, coeff_to_poly_ge_four P m (by simpa using hm))

lemma nat_degree_to_poly_le : (P : R[X]).nat_degree ≤ N :=
begin
  by_cases hP : (P : R[X]) = 0,
  { simp [hP], },
  simpa [degree_eq_nat_degree hP] using degree_to_poly_le P,
end

variables {P}

lemma degree_to_poly (ha : Pᗮ N ≠ 0) : (P : R[X]).degree = N :=
le_antisymm (degree_to_poly_le P) $ le_degree_of_ne_zero ha

lemma nat_degree_to_poly (ha : Pᗮ N ≠ 0) : (P : R[X]).nat_degree = N :=
le_antisymm (nat_degree_to_poly_le P) $ le_nat_degree_of_ne_zero ha

lemma leading_coeff (ha : Pᗮ N ≠ 0) : (P : R[X]).leading_coeff = Pᗮ N :=
by { rw [leading_coeff, nat_degree_to_poly ha], refl }

end degree

end basic

section roots

open multiset

/-! ### Roots over an extension -/

section extension
variables [comm_ring R] [comm_ring S] {N: ℕ} {P : degree_lt R N} {φ : R →+* S}

theorem mem_roots_to_poly_iff [is_domain R] (h0 : (P : R[X]) ≠ 0) (x : R) :
  x ∈ (P : R[X]).roots ↔ ∑ i in finset.range N, Pᗮ i * x ^ (i:ℕ) = 0 :=
begin
  have : (P : R[X]).nat_degree < N := sorry,
  simp [mem_roots h0, is_root, eval_eq_sum_range' this],
end

theorem card_roots_to_poly_le {P : degree_lt R N.succ} [is_domain R] [decidable_eq R] :
  (P : R[X]).roots.to_finset.card ≤ N :=
(to_finset_card_le (P : R[X]).roots).trans $
(card_roots' (P : R[X])).trans $ nat_degree_to_poly_le P

end extension

/-! ### Roots over a splitting field -/

section split
variables [field F] [field K] {N : ℕ} {P : degree_lt F N.succ} {φ : F →+* K} {x y z : K}

theorem to_poly_splits_iff_card_roots (ha : Pᗮ N ≠ 0) :
  splits φ (P : F[X]) ↔ (P# φ : K[X]).roots.card = N :=
begin
  replace ha : φ (Pᗮ N) ≠ 0 := φ.map_ne_zero.mpr ha,
  rw ← polynomial.coeff_map at ha,
  nth_rewrite_lhs 0 [← φ.id_comp],
  rwa [← splits_map_iff, ← map_to_poly, splits_iff_card_roots, nat_degree_to_poly],
end

lemma vieta_to_poly {P : degree_lt F N.succ} (ha : Pᗮ N ≠ 0) (hP : splits φ (P : F[X]))
  (k : fin N.succ) :
  φ (Pᗮ k)
  = φ (Pᗮ N) * (-1) ^ (N - k)
    * (((P# φ : K[X]).roots.powerset_len (N - k)).map multiset.prod).sum :=
begin
  rw [to_poly_splits_iff_card_roots ha, map_to_poly] at hP,
  convert @vieta K _ _ (map φ (P : F[X])) _ k _;
  simp [leading_coeff ha, nat_degree_to_poly ha, fin.is_le k, hP, map_to_poly, polynomial.coeff_map]
end

end split

end roots

end to_poly

namespace cubic

open polynomial multiset

variables [field F] [field K] {P : degree_lt F 4}  {φ : F →+* K} {x y z : K}

section roots

/-! ### Roots over a splitting field -/

section split

theorem splits_iff_roots_eq_three (ha : Pᗮ 3 ≠ 0) :
  splits φ (P : F[X]) ↔ ∃ x y z : K, (P# φ : K[X]).roots = {x, y, z} :=
by { rw [to_poly_splits_iff_card_roots ha], norm_num, rw [card_eq_three], refl }

theorem splits_of_three_roots (ha : Pᗮ 3 ≠ 0) {x y z : K}
  (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  splits φ (P : F[X]) :=
(splits_iff_roots_eq_three ha).mpr ⟨x, y, z, h3⟩

theorem eq_prod_three_roots (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  (P# φ : K[X]) = C (φ (Pᗮ 3)) * (X - C x) * (X - C y) * (X - C z) :=
begin
  rw [map_to_poly, eq_prod_roots_of_splits $ splits_of_three_roots ha h3,
    leading_coeff ha, ← map_to_poly, h3],
  change C (φ (Pᗮ 3)) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _,
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
end

theorem b_eq_three_roots (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  φ (Pᗮ 2) = φ (Pᗮ 3) * -(x + y + z) :=
calc φ (Pᗮ 2) = - φ (Pᗮ 3) * (z + y + x) : by
          { convert vieta_to_poly ha (splits_of_three_roots ha h3) 2 using 1, rw h3, norm_num }
... = _ : by ring

theorem c_eq_three_roots (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  φ (Pᗮ 1) = φ (Pᗮ 3) * (x * y + x * z + y * z) :=
calc φ (Pᗮ 1) = φ (Pᗮ 3) * (y * z + (x * z + x * y)) : by
          { convert vieta_to_poly ha (splits_of_three_roots ha h3) 1 using 1, rw h3, norm_num }
... = _ : by ring

theorem d_eq_three_roots (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  φ (Pᗮ 0) = φ (Pᗮ 3) * -(x * y * z) :=
calc φ (Pᗮ 0) = -(φ (Pᗮ 3) * (x * (y * z))) : by
          { convert vieta_to_poly ha (splits_of_three_roots ha h3) 0, rw h3, norm_num  }
... = _ : by ring

end split

/-! ### Discriminant over a splitting field -/

section discriminant

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [ring R] (P : degree_lt R 4) : R :=
Pᗮ 2 ^ 2 * Pᗮ 1 ^ 2 - 4 * Pᗮ 3 * Pᗮ 1 ^ 3 - 4 * Pᗮ 2 ^ 3 * Pᗮ 0 - 27 * Pᗮ 3 ^ 2 * Pᗮ 0 ^ 2
  + 18 * Pᗮ 3 * Pᗮ 2 * Pᗮ 1 * Pᗮ 0

theorem disc_eq_prod_three_roots (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  φ (disc P) = (φ (Pᗮ 3) * φ (Pᗮ 3) * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3],
  ring1
end

theorem disc_ne_zero_iff_roots_ne (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  disc P ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z :=
begin
  rw [← ring_hom.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two],
  simp only [mul_ne_zero_iff, sub_ne_zero],
  rw [ring_hom.map_ne_zero],
  tautology
end

theorem disc_ne_zero_iff_roots_nodup (ha : Pᗮ 3 ≠ 0) (h3 : (P# φ : K[X]).roots = {x, y, z}) :
  disc P ≠ 0 ↔ (P# φ : K[X]).roots.nodup :=
begin
  rw [disc_ne_zero_iff_roots_ne ha h3, h3],
  change _ ↔ (x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem card_roots_of_disc_ne_zero [decidable_eq K] (ha : Pᗮ 3 ≠ 0)
  (h3 : (P# φ : K[X]).roots = {x, y, z}) (hd : disc P ≠ 0) :
  (P# φ : K[X]).roots.to_finset.card = 3 :=
begin
  rw [to_finset_card_of_nodup $ (disc_ne_zero_iff_roots_nodup ha h3).mp hd,
        ← @to_poly_splits_iff_card_roots F K _ _ 3 P φ ha, splits_iff_roots_eq_three ha],
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩
end

end discriminant

end roots

end cubic
