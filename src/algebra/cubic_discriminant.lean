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

postfix `ᗮ`:1000 := polynomial.coeff

section roots

open multiset

/-! ### Roots over an extension -/

section extension
variables [comm_ring R] [comm_ring S] {P : R[X]} {φ : R →+* S}

theorem mem_roots_to_poly_iff [is_domain R] (h0 : P ≠ 0) (x : R) :
  x ∈ P.roots ↔ ∑ i in finset.range P.nat_degree.succ, Pᗮ i * x ^ (i:ℕ) = 0 :=
begin
  have : P.nat_degree < P.nat_degree := sorry,
  simp [mem_roots h0, is_root, eval_eq_sum_range' this],
end

theorem card_roots_to_poly_le {P : R[X]} [is_domain R] [decidable_eq R] :
  P.roots.to_finset.card ≤ P.nat_degree :=
(to_finset_card_le P.roots).trans $ card_roots' P

end extension

/-! ### Roots over a splitting field -/

section split
variables [field F] [field K] {P : F[X]} {φ : F →+* K} {x y z : K}

theorem to_poly_splits_iff_card_roots :
  splits φ (P : F[X]) ↔ (P.map φ).roots.card = P.nat_degree :=
begin
  nth_rewrite_lhs 0 [← φ.id_comp],
  rw [← splits_map_iff, splits_iff_card_roots, nat_degree_map],
end

end split

end roots

namespace cubic

open polynomial multiset

variables [field F] [field K] {P : F[X]}  {φ : F →+* K} {x y z : K}

section roots

/-! ### Roots over a splitting field -/

section split

theorem splits_iff_roots_eq_three (ha : P.nat_degree = 3) :
  splits φ (P : F[X]) ↔ ∃ x y z : K, (P.map φ).roots = {x, y, z} :=
by { rw [to_poly_splits_iff_card_roots], norm_num, rw [ha, card_eq_three], refl }

theorem splits_of_three_roots (ha : P.nat_degree = 3) {x y z : K}
  (h3 : (P.map φ).roots = {x, y, z}) :
  splits φ (P : F[X]) :=
(splits_iff_roots_eq_three ha).mpr ⟨x, y, z, h3⟩

theorem eq_prod_three_roots (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  (P.map φ) = C (φ (Pᗮ 3)) * (X - C x) * (X - C y) * (X - C z) :=
begin
  have : P.leading_coeff = Pᗮ 3 := congr_arg P.coeff ha,
  rw [eq_prod_roots_of_splits $ splits_of_three_roots ha h3, h3, this],
  change C (φ (Pᗮ 3)) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _,
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
end

theorem b_eq_three_roots (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  φ (Pᗮ 2) = φ (Pᗮ 3) * -(x + y + z) :=
calc φ (Pᗮ 2) = - φ (Pᗮ 3) * (z + y + x) : by
          { have : (P.map φ).leading_coeff = (P.map φ)ᗮ 3 := congr_arg (P.map φ).coeff ((nat_degree_map φ).trans ha),
            convert vieta (P.map φ) _ 2 _ using 1,
            { rw coeff_map },
            { simp [ha, nat_degree_map φ, this, h3, coeff_map] },
            { norm_num [ha, nat_degree_map, h3] },
            { simp [ha, this] } }
... = _ : by ring

theorem c_eq_three_roots (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  φ (Pᗮ 1) = φ (Pᗮ 3) * (x * y + x * z + y * z) :=
calc φ (Pᗮ 1) = φ (Pᗮ 3) * (y * z + (x * z + x * y)) : by
          { have : (P.map φ).roots.card = (P.map φ).nat_degree,
            { rw [nat_degree_map, ha, card_eq_three],
              exact ⟨_, _, _, h3⟩ },
            convert vieta (P.map φ) this 1 _ using 1, rw coeff_map, rw [h3], norm_num }
... = _ : by ring

theorem d_eq_three_roots (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  φ (Pᗮ 0) = φ (Pᗮ 3) * -(x * y * z) :=
calc φ (Pᗮ 0) = -(φ (Pᗮ 3) * (x * (y * z))) : by
          { convert vieta (P.map φ) (_ ) 0, rw h3, norm_num,  }
... = _ : by ring

end split

/-! ### Discriminant over a splitting field -/

section discriminant

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [ring R] (P : R[X]) : R :=
Pᗮ 2 ^ 2 * Pᗮ 1 ^ 2 - 4 * Pᗮ 3 * Pᗮ 1 ^ 3 - 4 * Pᗮ 2 ^ 3 * Pᗮ 0 - 27 * Pᗮ 3 ^ 2 * Pᗮ 0 ^ 2
  + 18 * Pᗮ 3 * Pᗮ 2 * Pᗮ 1 * Pᗮ 0

theorem disc_eq_prod_three_roots (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  φ (disc P) = (φ (Pᗮ 3) * φ (Pᗮ 3) * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3],
  ring1
end

theorem disc_ne_zero_iff_roots_ne (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  disc P ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z :=
begin
  have : P ≠ 0 := sorry,
  have : P.leading_coeff = Pᗮ 3 := congr_arg P.coeff ha,
  rw [← ring_hom.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two],
  simp only [mul_ne_zero_iff, sub_ne_zero],
  rw [ring_hom.map_ne_zero, ← this, leading_coeff_ne_zero],
  tautology
end

theorem disc_ne_zero_iff_roots_nodup (ha : P.nat_degree = 3) (h3 : (P.map φ).roots = {x, y, z}) :
  disc P ≠ 0 ↔ (P.map φ).roots.nodup :=
begin
  rw [disc_ne_zero_iff_roots_ne ha h3, h3],
  change _ ↔ (x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem card_roots_of_disc_ne_zero [decidable_eq K] (ha : P.nat_degree = 3)
  (h3 : (P.map φ).roots = {x, y, z}) (hd : disc P ≠ 0) :
  (P.map φ).roots.to_finset.card = 3 :=
begin
  rw [to_finset_card_of_nodup $ (disc_ne_zero_iff_roots_nodup ha h3).mp hd,
        ← @to_poly_splits_iff_card_roots F K, splits_iff_roots_eq_three ha],
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩
end

end discriminant

end roots

end cubic
