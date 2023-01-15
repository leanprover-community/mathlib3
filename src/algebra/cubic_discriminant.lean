/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import data.polynomial.splits

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

 * `cubic`: the structure representing a cubic polynomial.
 * `cubic.disc`: the discriminant of a cubic polynomial.

## Main statements

 * `cubic.disc_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
    the cubic has no duplicate roots.

## References

 * https://en.wikipedia.org/wiki/Cubic_equation
 * https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/

noncomputable theory

/-- The structure representing a cubic polynomial. -/
@[ext] structure cubic (R : Type*) := (a b c d : R)

namespace cubic

open cubic polynomial

open_locale polynomial

variables {R S F K : Type*}

instance [inhabited R] : inhabited (cubic R) := ⟨⟨default, default, default, default⟩⟩

instance [has_zero R] : has_zero (cubic R) := ⟨⟨0, 0, 0, 0⟩⟩

section basic

variables {P Q : cubic R} {a b c d a' b' c' d' : R} [semiring R]

/-- Convert a cubic polynomial to a polynomial. -/
def to_poly (P : cubic R) : R[X] := C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d

theorem C_mul_prod_X_sub_C_eq [comm_ring S] {w x y z : S} :
  C w * (X - C x) * (X - C y) * (X - C z)
    = to_poly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ :=
by { simp only [to_poly, C_neg, C_add, C_mul], ring1 }

theorem prod_X_sub_C_eq [comm_ring S] {x y z : S} :
  (X - C x) * (X - C y) * (X - C z)
    = to_poly ⟨1, -(x + y + z), (x * y + x * z + y * z), -(x * y * z)⟩ :=
by rw [← one_mul $ X - C x, ← C_1, C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul]

/-! ### Coefficients -/

section coeff

private lemma coeffs :
  (∀ n > 3, P.to_poly.coeff n = 0) ∧ P.to_poly.coeff 3 = P.a ∧ P.to_poly.coeff 2 = P.b
    ∧ P.to_poly.coeff 1 = P.c ∧ P.to_poly.coeff 0 = P.d :=
begin
  simp only [to_poly, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow],
  norm_num,
  intros n hn,
  repeat { rw [if_neg] },
  any_goals { linarith only [hn] },
  repeat { rw [zero_add] }
end

@[simp] lemma coeff_eq_zero {n : ℕ} (hn : 3 < n) : P.to_poly.coeff n = 0 := coeffs.1 n hn

@[simp] lemma coeff_eq_a : P.to_poly.coeff 3 = P.a := coeffs.2.1

@[simp] lemma coeff_eq_b : P.to_poly.coeff 2 = P.b := coeffs.2.2.1

@[simp] lemma coeff_eq_c : P.to_poly.coeff 1 = P.c := coeffs.2.2.2.1

@[simp] lemma coeff_eq_d : P.to_poly.coeff 0 = P.d := coeffs.2.2.2.2

lemma a_of_eq (h : P.to_poly = Q.to_poly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]

lemma b_of_eq (h : P.to_poly = Q.to_poly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]

lemma c_of_eq (h : P.to_poly = Q.to_poly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]

lemma d_of_eq (h : P.to_poly = Q.to_poly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]

lemma to_poly_injective (P Q : cubic R) : P.to_poly = Q.to_poly ↔ P = Q :=
⟨λ h, ext P Q (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg to_poly⟩

lemma of_a_eq_zero (ha : P.a = 0) : P.to_poly = C P.b * X ^ 2 + C P.c * X + C P.d :=
by rw [to_poly, ha, C_0, zero_mul, zero_add]

lemma of_a_eq_zero' : to_poly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d := of_a_eq_zero rfl

lemma of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly = C P.c * X + C P.d :=
by rw [of_a_eq_zero ha, hb, C_0, zero_mul, zero_add]

lemma of_b_eq_zero' : to_poly ⟨0, 0, c, d⟩ = C c * X + C d := of_b_eq_zero rfl rfl

lemma of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.to_poly = C P.d :=
by rw [of_b_eq_zero ha hb, hc, C_0, zero_mul, zero_add]

lemma of_c_eq_zero' : to_poly ⟨0, 0, 0, d⟩ = C d := of_c_eq_zero rfl rfl rfl

lemma of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
  P.to_poly = 0 :=
by rw [of_c_eq_zero ha hb hc, hd, C_0]

lemma of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : cubic R).to_poly = 0 := of_d_eq_zero rfl rfl rfl rfl

lemma zero : (0 : cubic R).to_poly = 0 := of_d_eq_zero'

lemma to_poly_eq_zero_iff (P : cubic R) : P.to_poly = 0 ↔ P = 0 :=
by rw [← zero, to_poly_injective]

private lemma ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.to_poly ≠ 0 :=
by { contrapose! h0, rw [(to_poly_eq_zero_iff P).mp h0], exact ⟨rfl, rfl, rfl, rfl⟩ }

lemma ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly ≠ 0 := (or_imp_distrib.mp ne_zero).1 ha

lemma ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).1 hb

lemma ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).1 hc

lemma ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.to_poly ≠ 0 :=
(or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).2 hd

@[simp] lemma leading_coeff_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.leading_coeff = P.a :=
leading_coeff_cubic ha

@[simp] lemma leading_coeff_of_a_ne_zero' (ha : a ≠ 0) : (to_poly ⟨a, b, c, d⟩).leading_coeff = a :=
leading_coeff_of_a_ne_zero ha

@[simp] lemma leading_coeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) :
  P.to_poly.leading_coeff = P.b :=
by rw [of_a_eq_zero ha, leading_coeff_quadratic hb]

@[simp] lemma leading_coeff_of_b_ne_zero' (hb : b ≠ 0) : (to_poly ⟨0, b, c, d⟩).leading_coeff = b :=
leading_coeff_of_b_ne_zero rfl hb

@[simp] lemma leading_coeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.leading_coeff = P.c :=
by rw [of_b_eq_zero ha hb, leading_coeff_linear hc]

@[simp] lemma leading_coeff_of_c_ne_zero' (hc : c ≠ 0) : (to_poly ⟨0, 0, c, d⟩).leading_coeff = c :=
leading_coeff_of_c_ne_zero rfl rfl hc

@[simp] lemma leading_coeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
  P.to_poly.leading_coeff = P.d :=
by rw [of_c_eq_zero ha hb hc, leading_coeff_C]

@[simp] lemma leading_coeff_of_c_eq_zero' : (to_poly ⟨0, 0, 0, d⟩).leading_coeff = d :=
leading_coeff_of_c_eq_zero rfl rfl rfl

lemma monic_of_a_eq_one (ha : P.a = 1) : P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_a_ne_zero $ by { rw [ha], exact one_ne_zero }, ha]
end

lemma monic_of_a_eq_one' : (to_poly ⟨1, b, c, d⟩).monic := monic_of_a_eq_one rfl

lemma monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_b_ne_zero ha $ by { rw [hb], exact one_ne_zero }, hb]
end

lemma monic_of_b_eq_one' : (to_poly ⟨0, 1, c, d⟩).monic := monic_of_b_eq_one rfl rfl

lemma monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.to_poly.monic :=
begin
  nontriviality,
  rw [monic, leading_coeff_of_c_ne_zero ha hb $ by { rw [hc], exact one_ne_zero }, hc]
end

lemma monic_of_c_eq_one' : (to_poly ⟨0, 0, 1, d⟩).monic := monic_of_c_eq_one rfl rfl rfl

lemma monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
  P.to_poly.monic :=
by rw [monic, leading_coeff_of_c_eq_zero ha hb hc, hd]

lemma monic_of_d_eq_one' : (to_poly ⟨0, 0, 0, 1⟩).monic := monic_of_d_eq_one rfl rfl rfl rfl

end coeff

/-! ### Degrees -/

section degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
@[simps] def equiv : cubic R ≃ {p : R[X] // p.degree ≤ 3} :=
{ to_fun    := λ P, ⟨P.to_poly, degree_cubic_le⟩,
  inv_fun   := λ f, ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩,
  left_inv  := λ P, by ext; simp only [subtype.coe_mk, coeffs],
  right_inv := λ f,
  begin
    ext (_ | _ | _ | _ | n); simp only [subtype.coe_mk, coeffs],
    have h3 : 3 < n + 4 := by linarith only,
    rw [coeff_eq_zero h3,
        (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2 _ $ with_bot.coe_lt_coe.mpr h3]
  end }

@[simp] lemma degree_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.degree = 3 := degree_cubic ha

@[simp] lemma degree_of_a_ne_zero' (ha : a ≠ 0) : (to_poly ⟨a, b, c, d⟩).degree = 3 :=
degree_of_a_ne_zero ha

lemma degree_of_a_eq_zero (ha : P.a = 0) : P.to_poly.degree ≤ 2 :=
by simpa only [of_a_eq_zero ha] using degree_quadratic_le

lemma degree_of_a_eq_zero' : (to_poly ⟨0, b, c, d⟩).degree ≤ 2 := degree_of_a_eq_zero rfl

@[simp] lemma degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.to_poly.degree = 2 :=
by rw [of_a_eq_zero ha, degree_quadratic hb]

@[simp] lemma degree_of_b_ne_zero' (hb : b ≠ 0) : (to_poly ⟨0, b, c, d⟩).degree = 2 :=
degree_of_b_ne_zero rfl hb

lemma degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly.degree ≤ 1 :=
by simpa only [of_b_eq_zero ha hb] using degree_linear_le

lemma degree_of_b_eq_zero' : (to_poly ⟨0, 0, c, d⟩).degree ≤ 1 := degree_of_b_eq_zero rfl rfl

@[simp] lemma degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.degree = 1 :=
by rw [of_b_eq_zero ha hb, degree_linear hc]

@[simp] lemma degree_of_c_ne_zero' (hc : c ≠ 0) : (to_poly ⟨0, 0, c, d⟩).degree = 1 :=
degree_of_c_ne_zero rfl rfl hc

lemma degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.to_poly.degree ≤ 0 :=
by simpa only [of_c_eq_zero ha hb hc] using degree_C_le

lemma degree_of_c_eq_zero' : (to_poly ⟨0, 0, 0, d⟩).degree ≤ 0 := degree_of_c_eq_zero rfl rfl rfl

@[simp] lemma degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
  P.to_poly.degree = 0 :=
by rw [of_c_eq_zero ha hb hc, degree_C hd]

@[simp] lemma degree_of_d_ne_zero' (hd : d ≠ 0) : (to_poly ⟨0, 0, 0, d⟩).degree = 0 :=
degree_of_d_ne_zero rfl rfl rfl hd

@[simp] lemma degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
  P.to_poly.degree = ⊥ :=
by rw [of_d_eq_zero ha hb hc hd, degree_zero]

@[simp] lemma degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : cubic R).to_poly.degree = ⊥ :=
degree_of_d_eq_zero rfl rfl rfl rfl

@[simp] lemma degree_of_zero : (0 : cubic R).to_poly.degree = ⊥ := degree_of_d_eq_zero'

@[simp] lemma nat_degree_of_a_ne_zero (ha : P.a ≠ 0) : P.to_poly.nat_degree = 3 :=
nat_degree_cubic ha

@[simp] lemma nat_degree_of_a_ne_zero' (ha : a ≠ 0) : (to_poly ⟨a, b, c, d⟩).nat_degree = 3 :=
nat_degree_of_a_ne_zero ha

lemma nat_degree_of_a_eq_zero (ha : P.a = 0) : P.to_poly.nat_degree ≤ 2 :=
by simpa only [of_a_eq_zero ha] using nat_degree_quadratic_le

lemma nat_degree_of_a_eq_zero' : (to_poly ⟨0, b, c, d⟩).nat_degree ≤ 2 :=
nat_degree_of_a_eq_zero rfl

@[simp] lemma nat_degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.to_poly.nat_degree = 2 :=
by rw [of_a_eq_zero ha, nat_degree_quadratic hb]

@[simp] lemma nat_degree_of_b_ne_zero' (hb : b ≠ 0) : (to_poly ⟨0, b, c, d⟩).nat_degree = 2 :=
nat_degree_of_b_ne_zero rfl hb

lemma nat_degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.to_poly.nat_degree ≤ 1 :=
by simpa only [of_b_eq_zero ha hb] using nat_degree_linear_le

lemma nat_degree_of_b_eq_zero' : (to_poly ⟨0, 0, c, d⟩).nat_degree ≤ 1 :=
nat_degree_of_b_eq_zero rfl rfl

@[simp] lemma nat_degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
  P.to_poly.nat_degree = 1 :=
by rw [of_b_eq_zero ha hb, nat_degree_linear hc]

@[simp] lemma nat_degree_of_c_ne_zero' (hc : c ≠ 0) : (to_poly ⟨0, 0, c, d⟩).nat_degree = 1 :=
nat_degree_of_c_ne_zero rfl rfl hc

@[simp] lemma nat_degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
  P.to_poly.nat_degree = 0 :=
by rw [of_c_eq_zero ha hb hc, nat_degree_C]

@[simp] lemma nat_degree_of_c_eq_zero' : (to_poly ⟨0, 0, 0, d⟩).nat_degree = 0 :=
nat_degree_of_c_eq_zero rfl rfl rfl

@[simp] lemma nat_degree_of_zero : (0 : cubic R).to_poly.nat_degree = 0 := nat_degree_of_c_eq_zero'

end degree

/-! ### Map across a homomorphism -/

section map

variables [semiring S] {φ : R →+* S}

/-- Map a cubic polynomial across a semiring homomorphism. -/
def map (φ : R →+* S) (P : cubic R) : cubic S := ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

lemma map_to_poly : (map φ P).to_poly = polynomial.map φ P.to_poly :=
by simp only [map, to_poly, map_C, map_X, polynomial.map_add, polynomial.map_mul,
              polynomial.map_pow]

end map

end basic

section roots

open multiset

/-! ### Roots over an extension -/

section extension

variables {P : cubic R} [comm_ring R] [comm_ring S] {φ : R →+* S}

/-- The roots of a cubic polynomial. -/
def roots [is_domain R] (P : cubic R) : multiset R := P.to_poly.roots

lemma map_roots [is_domain S] : (map φ P).roots = (polynomial.map φ P.to_poly).roots :=
by rw [roots, map_to_poly]

theorem mem_roots_iff [is_domain R] (h0 : P.to_poly ≠ 0) (x : R) :
  x ∈ P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 :=
begin
  rw [roots, mem_roots h0, is_root, to_poly],
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
end

theorem card_roots_le [is_domain R] [decidable_eq R] : P.roots.to_finset.card ≤ 3 :=
begin
  apply (to_finset_card_le P.to_poly.roots).trans,
  by_cases hP : P.to_poly = 0,
  { exact (card_roots' P.to_poly).trans (by { rw [hP, nat_degree_zero], exact zero_le 3 }) },
  { exact with_bot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le) }
end

end extension

variables {P : cubic F} [field F] [field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/

section split

theorem splits_iff_card_roots (ha : P.a ≠ 0) : splits φ P.to_poly ↔ (map φ P).roots.card = 3 :=
begin
  replace ha : (map φ P).a ≠ 0 := (_root_.map_ne_zero φ).mpr ha,
  nth_rewrite_lhs 0 [← ring_hom.id_comp φ],
  rw [roots, ← splits_map_iff, ← map_to_poly, splits_iff_card_roots,
      ← ((degree_eq_iff_nat_degree_eq $ ne_zero_of_a_ne_zero ha).mp $
          degree_of_a_ne_zero ha : _ = 3)]
end

theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) :
  splits φ P.to_poly ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} :=
by rw [splits_iff_card_roots ha, card_eq_three]

theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  (map φ P).to_poly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) :=
begin
  rw [map_to_poly, eq_prod_roots_of_splits $ (splits_iff_roots_eq_three ha).mpr $ exists.intro x $
        exists.intro y $ exists.intro z h3, leading_coeff_of_a_ne_zero ha, ← map_roots, h3],
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _,
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
end

theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ :=
begin
  apply_fun to_poly,
  any_goals { exact λ P Q, (to_poly_injective P Q).mp },
  rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
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

end split

/-! ### Discriminant over a splitting field -/

section discriminant

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [ring R] (P : cubic R) : R :=
P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2
  + 18 * P.a * P.b * P.c * P.d

theorem disc_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  φ P.disc = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 :=
begin
  simp only [disc, ring_hom.map_add, ring_hom.map_sub, ring_hom.map_mul, map_pow],
  simp only [ring_hom.map_one, map_bit0, map_bit1],
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3],
  ring1
end

theorem disc_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  P.disc ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z :=
begin
  rw [←_root_.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two],
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self, and_iff_right ha, and_assoc],
end

theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
  P.disc ≠ 0 ↔ (map φ P).roots.nodup :=
begin
  rw [disc_ne_zero_iff_roots_ne ha h3, h3],
  change _ ↔ (x ::ₘ y ::ₘ {z}).nodup,
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton],
  simp only [nodup_singleton],
  tautology
end

theorem card_roots_of_disc_ne_zero [decidable_eq K] (ha : P.a ≠ 0)
  (h3 : (map φ P).roots = {x, y, z}) (hd : P.disc ≠ 0) : (map φ P).roots.to_finset.card = 3 :=
begin
  rw [to_finset_card_of_nodup $ (disc_ne_zero_iff_roots_nodup ha h3).mp hd,
      ← splits_iff_card_roots ha, splits_iff_roots_eq_three ha],
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩
end

end discriminant

end roots

end cubic
