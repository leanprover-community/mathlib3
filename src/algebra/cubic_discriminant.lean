/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import field_theory.splitting_field

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

* `cubic`
* `disc`

## Main statements

* `disc_ne_zero_iff_roots_nodup`

## References

* https://en.wikipedia.org/wiki/Cubic_equation
* https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, polynomial, root, discriminant
-/

noncomputable theory

/-- The structure representing a cubic polynomial. -/
structure cubic (R : Type*) [has_zero R] := (a b c d : R)

instance (R : Type*) [has_zero R] : inhabited (cubic R) := ⟨⟨0, 0, 0, 0⟩⟩

namespace cubic

open cubic polynomial

/-! ## Coefficients -/

section coeff

variables {R S : Type*} [semiring R] [semiring S] {P Q : cubic R} (φ : R →+* S)

/-- Convert a cubic polynomial to a polynomial. -/
def to_poly (P : cubic R) : polynomial R := C P.d + C P.c * X + C P.b * X ^ 2 + C P.a * X ^ 3

/-- Map a cubic polynomial across a ring homomorphism. -/
def map (P : cubic R) : cubic S := ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

lemma map_eq : (map φ P).to_poly = polynomial.map φ P.to_poly :=
begin
  change (map φ P).to_poly = polynomial.map φ (C P.d + C P.c * X + C P.b * X ^ 2 + C P.a * X ^ 3),
  simp only [map_C, map_X, polynomial.map_add, polynomial.map_mul, polynomial.map_pow],
  refl
end

lemma coeffs :
  P.to_poly.coeff 3 = P.a ∧ P.to_poly.coeff 2 = P.b ∧ P.to_poly.coeff 1 = P.c
    ∧ P.to_poly.coeff 0 = P.d :=
by { rw [to_poly], simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X, coeff_C_mul_X], norm_num }

@[simp] theorem coeff_three : P.to_poly.coeff 3 = P.a := coeffs.1

@[simp] theorem coeff_two : P.to_poly.coeff 2 = P.b := coeffs.2.1

@[simp] theorem coeff_one : P.to_poly.coeff 1 = P.c := coeffs.2.2.1

@[simp] theorem coeff_zero : P.to_poly.coeff 0 = P.d := coeffs.2.2.2

lemma to_poly_injective (P Q : cubic R) : P.to_poly = Q.to_poly ↔ P = Q :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩,
  split,
  { rintro h,
    simp only,
    split,
    { apply_fun (λ p, coeff p 3) at h,
      rw [coeff_three, coeff_three] at h,
      exact h },
    { split,
      { apply_fun (λ p, coeff p 2) at h,
        rw [coeff_two, coeff_two] at h,
        exact h },
      { split,
        { apply_fun (λ p, coeff p 1) at h,
          rw [coeff_one, coeff_one] at h,
          exact h },
        { apply_fun (λ p, coeff p 0) at h,
          rw [coeff_zero, coeff_zero] at h,
          exact h } } } },
  { intro h,
    injection h with ha hb hc hd,
    rw [ha, hb, hc, hd] }
end

theorem a_of_eq (h : P.to_poly = Q.to_poly) : P.a = Q.a :=
by { rw [to_poly_injective] at h, rw [h] }

theorem b_of_eq (h : P.to_poly = Q.to_poly) : P.b = Q.b :=
by { rw [to_poly_injective] at h, rw [h] }

theorem c_of_eq (h : P.to_poly = Q.to_poly) : P.c = Q.c :=
by { rw [to_poly_injective] at h, rw [h] }

theorem d_of_eq (h : P.to_poly = Q.to_poly) : P.d = Q.d :=
by { rw [to_poly_injective] at h, rw [h] }

lemma of_a_eq_zero (ha : P.a = 0) : P.to_poly = C P.d + C P.c * X + C P.b * X ^ 2 :=
by { rw [to_poly, C_eq_zero.mpr ha, zero_mul, add_zero] }

lemma of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly = C P.d + C P.c * X :=
by { rw [to_poly, C_eq_zero.mpr ha, C_eq_zero.mpr hb], simp only [add_zero, zero_mul] }

lemma of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.to_poly = C P.d :=
begin
  rw [to_poly, C_eq_zero.mpr ha, C_eq_zero.mpr hb, C_eq_zero.mpr hc],
  simp only [add_zero, zero_mul]
end

lemma of_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) : P.to_poly = 0 :=
begin
  rw [to_poly, C_eq_zero.mpr ha, C_eq_zero.mpr hb, C_eq_zero.mpr hc, C_eq_zero.mpr hd],
  simp only [add_zero, zero_mul]
end

end coeff

/-! ## Degree -/

section degree

variables {R : Type*} [semiring R] {P : cubic R}

lemma degree_of_constant_lt : (C P.d).degree < 1 := lt_of_le_of_lt degree_C_le dec_trivial

lemma degree_of_linear_lt : (C P.d + C P.c * X).degree < 2 :=
begin
  apply lt_of_le_of_lt (degree_add_le _ _),
  rw [max_lt_iff],
  split,
  { exact lt_of_le_of_lt degree_C_le dec_trivial },
  { exact lt_of_le_of_lt (degree_C_mul_X_le _) dec_trivial }
end

lemma degree_of_quadratic_lt : (C P.d + C P.c * X + C P.b * X ^ 2).degree < 3 :=
begin
  apply lt_of_le_of_lt (degree_add_le _ _),
  rw [max_lt_iff],
  split,
  { exact lt_of_lt_of_le degree_of_linear_lt dec_trivial },
  { exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) dec_trivial }
end

theorem degree_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.degree = ↑3 :=
begin
  rw [to_poly, degree_add_eq_right_of_degree_lt],
  all_goals { rw [degree_C_mul_X_pow _ ha] },
  exact degree_of_quadratic_lt
end

theorem degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.to_poly.degree = ↑2 :=
begin
  rw [of_a_eq_zero ha, degree_add_eq_right_of_degree_lt],
  all_goals { rw [degree_C_mul_X_pow _ hb] },
  exact degree_of_linear_lt
end

theorem degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.to_poly.degree = ↑1 :=
begin
  rw [of_b_eq_zero ha hb, degree_add_eq_right_of_degree_lt],
  all_goals { rw [← pow_one X, degree_C_mul_X_pow _ hc] },
  exact degree_of_constant_lt
end

theorem degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
  P.to_poly.degree = ↑0 :=
by { rw [of_c_eq_zero ha hb hc, degree_C hd], refl }

theorem degree_of_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
  P.to_poly.degree = ⊥ :=
by { rw [of_zero ha hb hc hd], refl }

theorem degree_le : P.to_poly.degree ≤ 3 :=
begin
  by_cases ha : P.a = 0,
  { by_cases hb : P.b = 0,
    { by_cases hc : P.c = 0,
      { by_cases hd : P.d = 0,
        { rw [degree_of_zero ha hb hc hd],
          exact dec_trivial },
        { rw [degree_of_d_ne_zero ha hb hc hd],
          exact dec_trivial } },
      { rw [degree_of_c_ne_zero ha hb hc],
        exact dec_trivial } },
    { rw [degree_of_b_ne_zero ha hb],
      exact dec_trivial } },
  { rw [degree_of_a_ne_zero ha],
    exact dec_trivial },
end

lemma ne_zero (h : ¬P.a = 0 ∨ ¬P.b = 0 ∨ ¬P.c = 0 ∨ ¬P.d = 0) : P.to_poly ≠ 0 :=
begin
  apply @ne_zero_of_degree_gt _ _ _ ⊥,
  by_cases ha : P.a = 0,
  { rw [ha, ne_self_iff_false, false_or] at h,
    by_cases hb : P.b = 0,
    { rw [hb, ne_self_iff_false, false_or] at h,
      by_cases hc : P.c = 0,
      { rw [hc, ne_self_iff_false, false_or] at h,
        rw [degree_of_d_ne_zero ha hb hc h],
        exact dec_trivial },
      { rw [degree_of_c_ne_zero ha hb hc],
        exact dec_trivial } },
    { rw [degree_of_b_ne_zero ha hb],
      exact dec_trivial } },
  { rw [degree_of_a_ne_zero ha],
    exact dec_trivial }
end

theorem ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly ≠ 0 := (or_imp_distrib.mp ne_zero).1 ha

theorem ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).1 hb

theorem ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).1 hc

theorem ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).2 hd

theorem leading_coeff_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.leading_coeff = P.a :=
begin
  rw [to_poly, leading_coeff_add_of_degree_lt, leading_coeff_C_mul_X_pow],
  rw [degree_C_mul_X_pow _ ha],
  exact degree_of_quadratic_lt
end

theorem leading_coeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.to_poly.leading_coeff = P.b :=
begin
  rw [of_a_eq_zero ha, leading_coeff_add_of_degree_lt, leading_coeff_C_mul_X_pow],
  rw [degree_C_mul_X_pow _ hb],
  exact degree_of_linear_lt
end

theorem leading_coeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.leading_coeff = P.c :=
begin
  rw [of_b_eq_zero ha hb, leading_coeff_add_of_degree_lt, ← pow_one X, leading_coeff_C_mul_X_pow],
  rw [← pow_one X, degree_C_mul_X_pow _ hc],
  exact degree_of_constant_lt
end

theorem leading_coeff_of_constant (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
  P.to_poly.leading_coeff = P.d :=
by rw [of_c_eq_zero ha hb hc, leading_coeff_C]

end degree

/-! ## Roots -/

section roots

open multiset

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]

/-- The roots of a cubic polynomial. -/
def roots [is_domain R] (P : cubic R) : multiset R := P.to_poly.roots

lemma roots_eq {φ : R →+* S} {P : cubic R} : (map φ P).roots = (polynomial.map φ P.to_poly).roots :=
by rw [roots, map_eq]

theorem mem_roots_iff [is_domain R] {P : cubic R} (h0 : P.to_poly ≠ 0) (x : R) :
  x ∈ P.roots ↔ P.d + P.c * x + P.b * x ^ 2 + P.a * x ^ 3 = 0 :=
begin
  rw [roots, mem_roots h0, is_root, to_poly],
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
end

theorem card_roots_le [is_domain R] [decidable_eq R] {P : cubic R} : P.roots.to_finset.card ≤ 3 :=
begin
  apply le_trans (multiset.to_finset_card_le P.to_poly.roots),
  by_cases hP : P.to_poly = 0,
  { apply le_trans (card_roots' P.to_poly),
    rw [hP, nat_degree_zero],
    exact dec_trivial },
  { rw [← with_bot.coe_le_coe],
    exact le_trans (card_roots hP) (le_trans degree_le dec_trivial) }
end

variables {F K : Type*} [field F] [field K] [is_domain K] {φ : F →+* K} {P : cubic F} {x y z : K}

theorem splits_iff_card_roots (ha : P.a ≠ 0) : splits φ P.to_poly ↔ (map φ P).roots.card = 3 :=
begin
  replace ha : (map φ P).a ≠ 0 := (ring_hom.map_ne_zero φ).mpr ha,
  change splits ((ring_hom.id K).comp φ) P.to_poly ↔ card (map φ P).to_poly.roots = 3,
  rw [← splits_map_iff, ← map_eq, splits_iff_card_roots,
      ← (degree_eq_iff_nat_degree_eq $ ne_zero_of_a_ne_zero ha).mp $ degree_of_a_ne_zero ha]
end

theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) :
  splits φ P.to_poly ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} :=
by rw [splits_iff_card_roots ha, card_eq_three]

theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  (map φ P).to_poly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) :=
begin
  rw [map_eq, eq_prod_roots_of_splits $ (splits_iff_roots_eq_three ha).mpr $ exists.intro x $
        exists.intro y $ exists.intro z h3, leading_coeff_of_a_ne_zero ha, ← roots_eq, h3],
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _,
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
end

theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ :=
begin
  apply_fun to_poly using λ P Q, (to_poly_injective P Q).mp,
  rw [eq_prod_three_roots ha h3, to_poly],
  simp only [C_neg, C_add, C_mul],
  ring1
end

theorem b_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  φ P.b = φ P.a * -(x + y + z) :=
by injection eq_sum_three_roots ha h3

theorem c_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  φ P.c = φ P.a * (x * y + x * z + y * z) :=
by injection eq_sum_three_roots ha h3

theorem d_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  φ P.d = φ P.a * -(x * y * z) :=
by injection eq_sum_three_roots ha h3

end roots

/-! ## Discriminant -/

section discriminant

open multiset

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [ring R] (P : cubic R) : R :=
P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2
  + 18 * P.a * P.b * P.c * P.d

variables {F K : Type*} [field F] [field K] {φ : F →+* K} {P : cubic F} {x y z : K}

theorem disc_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  φ P.disc = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3],
  ring1
end

theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  P.disc ≠ 0 ↔ (map φ P).roots.nodup :=
begin
  rw [← ring_hom.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two],
  simp only [mul_ne_zero_iff, sub_ne_zero],
  rw [ring_hom.map_ne_zero, h3],
  change _ ↔ (x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem card_roots_of_roots_nodup [decidable_eq K] (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (hd : (map φ P).roots.nodup) :
  (map φ P).roots.to_finset.card = 3 :=
by rw [multiset.to_finset_card_of_nodup hd, (splits_iff_card_roots ha).mp hs]

end discriminant

end cubic
