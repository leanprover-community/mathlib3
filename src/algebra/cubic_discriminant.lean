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

* <https://en.wikipedia.org/wiki/Cubic_equation>
* <https://en.wikipedia.org/wiki/Discriminant>

## Tags

cubic, polynomial, root, discriminant
-/

noncomputable theory

/-- The structure representing a cubic polynomial. -/
structure cubic (R : Type*) [has_zero R] := (a b c d : R)

instance (R : Type*) [has_zero R] : inhabited (cubic R) := ⟨⟨0, 0, 0, 0⟩⟩

namespace cubic

open cubic polynomial

----------------------------------------------------------------------------------------------------
/-! ## Coefficients -/

section coeff

variables {R : Type*} [semiring R] (P Q : cubic R)

/-- Convert a cubic polynomial to a polynomial. -/
def to_poly : polynomial R := C P.d + C P.c * X + C P.b * X ^ 2 + C P.a * X ^ 3

lemma coeff_eq :
  P.to_poly.coeff 3 = P.a ∧ P.to_poly.coeff 2 = P.b ∧ P.to_poly.coeff 1 = P.c
    ∧ P.to_poly.coeff 0 = P.d :=
by { rw [to_poly], simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X, coeff_C_mul_X], norm_num }

@[simp]
theorem coeff_eq_a : P.to_poly.coeff 3 = P.a := (coeff_eq P).1

@[simp]
theorem coeff_eq_b : P.to_poly.coeff 2 = P.b := (coeff_eq P).2.1

@[simp]
theorem coeff_eq_c : P.to_poly.coeff 1 = P.c := (coeff_eq P).2.2.1

@[simp]
theorem coeff_eq_d : P.to_poly.coeff 0 = P.d := (coeff_eq P).2.2.2

lemma eq_iff : P.to_poly = Q.to_poly ↔ P = Q :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩,
  split,
  { rintro h,
    simp only,
    split,
    { apply_fun (λ p, coeff p 3) at h,
      rw [coeff_eq_a, coeff_eq_a] at h,
      exact h },
    { split,
      { apply_fun (λ p, coeff p 2) at h,
        rw [coeff_eq_b, coeff_eq_b] at h,
        exact h },
      { split,
        { apply_fun (λ p, coeff p 1) at h,
          rw [coeff_eq_c, coeff_eq_c] at h,
          exact h },
        { apply_fun (λ p, coeff p 0) at h,
          rw [coeff_eq_d, coeff_eq_d] at h,
          exact h } } } },
  { intro h,
    injection h with ha hb hc hd,
    rw [ha, hb, hc, hd] }
end

lemma to_poly.injective : function.injective (to_poly : cubic R → polynomial R) :=
λ P Q, (eq_iff P Q).mp

theorem a_of_eq (h : P.to_poly = Q.to_poly) : P.a = Q.a :=
by { rw [eq_iff] at h, cases P, cases Q, injection h }

theorem b_of_eq (h : P.to_poly = Q.to_poly) : P.b = Q.b :=
by { rw [eq_iff] at h, cases P, cases Q, injection h }

theorem c_of_eq (h : P.to_poly = Q.to_poly) : P.c = Q.c :=
by { rw [eq_iff] at h, cases P, cases Q, injection h }

theorem d_of_eq (h : P.to_poly = Q.to_poly) : P.d = Q.d :=
by { rw [eq_iff] at h, cases P, cases Q, injection h }

end coeff

----------------------------------------------------------------------------------------------------
/-! ## Degree -/

section degree

variables {R : Type*} [semiring R] {P : cubic R}

private lemma degree_lt (ha : P.a ≠ 0) :
  (C P.d + C P.c * X + C P.b * X ^ 2).degree < (C P.a * X ^ 3).degree :=
begin
  rw [degree_C_mul_X_pow _ ha],
  apply lt_of_le_of_lt (degree_add_le _ _),
  rw [max_lt_iff],
  split,
  { apply lt_of_le_of_lt (degree_add_le _ _),
    rw [max_lt_iff],
    split,
    { apply lt_of_le_of_lt degree_C_le,
      exact dec_trivial },
    { apply lt_of_le_of_lt (degree_C_mul_X_le _),
      exact dec_trivial } },
  { apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _),
    exact dec_trivial }
end

theorem degree_eq_three (ha : P.a ≠ 0) : P.to_poly.degree = ↑3 :=
by { rw [to_poly, degree_add_eq_right_of_degree_lt, degree_C_mul_X_pow _ ha], exact degree_lt ha }

theorem ne_zero (ha : P.a ≠ 0) : P.to_poly ≠ 0 :=
ne_zero_of_degree_gt $ by { rw [degree_eq_three ha, with_bot.coe_lt_coe], exact zero_lt_three }

theorem leading_coeff_eq_a (ha : P.a ≠ 0) : P.to_poly.leading_coeff = P.a :=
by { rw [to_poly, leading_coeff_add_of_degree_lt, leading_coeff_C_mul_X_pow], exact degree_lt ha }

end degree

----------------------------------------------------------------------------------------------------
/-! ## Roots -/

section roots

open multiset

variables {F K : Type*} [field F] [field K] {φ : F →+* K} {P : cubic F} {x y z : K}

/-- Map a cubic polynomial across a ring homomorphism. -/
def map (φ : F →+* K) (P : cubic F) : cubic K := ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

lemma map_eq : (map φ P).to_poly = polynomial.map φ P.to_poly :=
begin
  change (map φ P).to_poly = polynomial.map φ (C P.d + C P.c * X + C P.b * X ^ 2 + C P.a * X ^ 3),
  simp only [map_C, map_X, polynomial.map_add, polynomial.map_mul, polynomial.map_pow],
  refl
end

/-- The roots of a cubic polynomial. -/
def roots (P : cubic F) : multiset F := P.to_poly.roots

lemma roots_eq : (map φ P).roots = (polynomial.map φ P.to_poly).roots := by rw [roots, map_eq]

theorem mem_roots_iff (ha : P.a ≠ 0) (x : F) :
  x ∈ P.roots ↔ P.d + P.c * x + P.b * x ^ 2 + P.a * x ^ 3 = 0 :=
begin
  rw [roots, mem_roots (ne_zero ha), is_root, to_poly],
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
end

theorem roots_card_le_three [decidable_eq F] (ha : P.a ≠ 0) : P.roots.to_finset.card ≤ 3 :=
le_trans (multiset.to_finset_card_le P.to_poly.roots) $ with_bot.coe_le_coe.mp $
  has_le.le.trans_eq (card_roots $ ne_zero ha) (degree_eq_three ha)

theorem roots_card_eq_three (ha : P.a ≠ 0) (hs : splits φ P.to_poly) : (map φ P).roots.card = 3 :=
begin
  rw [← with_bot.coe_eq_coe, roots_eq, ← degree_eq_card_roots (ne_zero ha) hs, ← degree_eq_three ha]
end

theorem roots_eq_three (ha : P.a ≠ 0) (hs : splits φ P.to_poly) :
  ∃ x y z : K, (map φ P).roots = {x, y, z} :=
by rw [← card_eq_three, roots_card_eq_three ha hs]

theorem eq_prod_three_roots (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  (map φ P).to_poly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) :=
begin
  rw [map_eq, eq_prod_roots_of_splits hs, leading_coeff_eq_a ha, mul_assoc,
      mul_assoc, ← prod_singleton (X - C z)],
  change _ = C (φ P.a) * (multiset.map (λ w, X - C w) {x, y, z}).prod,
  rw [← h3, roots_eq]
end

theorem eq_sum_three_roots (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ :=
begin
  apply_fun to_poly using to_poly.injective,
  rw [eq_prod_three_roots ha hs h3, to_poly],
  simp only [C_neg, C_add, C_mul],
  ring1
end

theorem b_eq_three_roots (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  φ P.b = φ P.a * -(x + y + z) :=
by injection eq_sum_three_roots ha hs h3

theorem c_eq_three_roots (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  φ P.c = φ P.a * (x * y + x * z + y * z) :=
by injection eq_sum_three_roots ha hs h3

theorem d_eq_three_roots (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  φ P.d = φ P.a * -(x * y * z) :=
by injection eq_sum_three_roots ha hs h3

end roots

----------------------------------------------------------------------------------------------------
/-! ## Discriminant -/

section discriminant

open multiset

variables {F K : Type*} [field F] [field K] {φ : F →+* K} {P : cubic F} {x y z : K}

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [ring R] (P : cubic R) : R :=
P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2
  + 18 * P.a * P.b * P.c * P.d

theorem disc_eq_prod_three_roots (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  φ P.disc = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_three_roots ha hs h3, c_eq_three_roots ha hs h3, d_eq_three_roots ha hs h3],
  ring1
end

theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (hs : splits φ P.to_poly)
  (h3 : (map φ P).roots = {x, y, z}) :
  P.disc ≠ 0 ↔ (map φ P).roots.nodup :=
begin
  rw [← ring_hom.map_ne_zero φ, disc_eq_prod_three_roots ha hs h3, pow_two],
  simp only [mul_ne_zero_iff, sub_ne_zero],
  rw [ring_hom.map_ne_zero, h3],
  change _ ↔ (x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem roots_card_eq_three_of_roots_nodup [decidable_eq K] (ha : P.a ≠ 0)
  (hs : splits φ P.to_poly) (hd : (map φ P).roots.nodup) :
  (map φ P).roots.to_finset.card = 3 :=
by rw [multiset.to_finset_card_of_nodup hd, roots_card_eq_three ha hs]

end discriminant

----------------------------------------------------------------------------------------------------

end cubic
