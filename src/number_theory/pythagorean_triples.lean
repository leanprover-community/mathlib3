/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Paul van Wamelen.
-/
import algebra.field
import algebra.gcd_domain
import algebra.group_with_zero_power
import tactic

/-!
# Pythagorean Triples
The main result is the classification of pythagorean triples. The final result is for general
pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof.
-/

noncomputable theory
open_locale classical

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def pythagorean_triple (x y z : ℤ) : Prop := x*x + y*y = z*z

variables {K : Type*} [field K]

/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circle_equiv_gen (hk : ∀ x : K, 1 + x^2 ≠ 0) :
  K ≃ {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1} :=
{ to_fun := λ x, ⟨⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩,
    by { field_simp [hk x, div_pow], ring },
    by { simp only [ne.def, div_eq_iff (hk x), ←neg_mul_eq_neg_mul, one_mul, neg_add,
      sub_eq_add_neg, add_left_inj],
      rw [eq_neg_iff_add_eq_zero],
      convert hk 1,
      simp }⟩,
  inv_fun := λ p, p.1.1 / (p.1.2 + 1),
  left_inv := λ x,
    begin
      have h2 : (1 + 1 : K) = 2, { norm_num },
      have h3 : (2 : K) ≠ 0, { rw ←h2, convert hk 1, rw one_pow 2 },
      field_simp [hk x, h2, h3, add_assoc, add_comm, add_sub_cancel'_right, mul_comm]
    end,
  right_inv := λ ⟨⟨x, y⟩, hxy, hy⟩,
    begin
      change x ^ 2 + y ^ 2 = 1 at hxy,
      have h2 : y + 1 ≠ 0, { apply mt eq_neg_of_add_eq_zero, exact hy },
      have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1),
      { rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm], ring },
      have h4 : (2 : K) ≠ 0, { rw (by norm_num : (2 : K) = 1 + 1), convert hk 1, rw one_pow 2 },
      simp only [prod.mk.inj_iff, subtype.mk_eq_mk], apply and.intro,
      { field_simp [h2, h3], field_simp [h2, h4, pow_two], ring },
      { field_simp [h2, h3, h4], rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm], ring }
    end }

lemma circle_equiv_fun (hk : ∀ x : K, 1 + x^2 ≠ 0) (x : K) :
  (circle_equiv_gen hk x : K × K) = ⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩ := by refl

lemma circle_equiv_inv (hk : ∀ x : K, 1 + x^2 ≠ 0)
  (v : {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1}) :
  (circle_equiv_gen hk).symm v = v.val.1 / (v.val.2 + 1) := by refl
