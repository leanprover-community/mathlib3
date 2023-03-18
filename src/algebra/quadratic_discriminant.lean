/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import algebra.char_p.invertible
import order.filter.at_top_bot
import tactic.linarith
import tactic.field_simp
import tactic.linear_combination

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * x * x + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.
- `discrim_le_zero_of_nonpos`, `discrim_lt_zero`, `discrim_lt_zero_of_neg`: versions of this
  statement with other inequalities.

## Tags

polynomial, quadratic, discriminant, root
-/

open filter

section ring
variables {R : Type*}

/-- Discriminant of a quadratic -/
def discrim [ring R] (a b c : R) : R := b^2 - 4 * a * c

@[simp] lemma discrim_neg [ring R] (a b c : R) : discrim (-a) (-b) (-c) = discrim a b c :=
by simp [discrim]

variables [comm_ring R] {a b c : R}

lemma discrim_eq_sq_of_quadratic_eq_zero {x : R} (h : a * x * x + b * x + c = 0) :
  discrim a b c = (2 * a * x + b) ^ 2 :=
begin
  rw [discrim],
  linear_combination -4 * a * h
end

/--
A quadratic has roots if and only if its discriminant equals some square.
-/
lemma quadratic_eq_zero_iff_discrim_eq_sq [ne_zero (2 : R)] [no_zero_divisors R]
  (ha : a ≠ 0) {x : R} :
  a * x * x + b * x + c = 0 ↔ discrim a b c = (2 * a * x + b) ^ 2 :=
begin
  refine ⟨discrim_eq_sq_of_quadratic_eq_zero, λ h, _⟩,
  rw [discrim] at h,
  have ha : 2 * 2 * a ≠ 0 := mul_ne_zero (mul_ne_zero (ne_zero.ne _) (ne_zero.ne _)) ha,
  apply mul_left_cancel₀ ha,
  linear_combination -h
end

/-- A quadratic has no root if its discriminant has no square root. -/
lemma quadratic_ne_zero_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) (x : R) :
  a * x * x + b * x + c ≠ 0 :=
mt discrim_eq_sq_of_quadratic_eq_zero $ h _

end ring

section field
variables {K : Type*} [field K] [ne_zero (2 : K)] {a b c x : K}

/-- Roots of a quadratic equation. -/
lemma quadratic_eq_zero_iff (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
  a * x * x + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) :=
begin
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha, h, sq, mul_self_eq_mul_self_iff],
  field_simp,
  apply or_congr,
  { split; intro h'; linear_combination -h' },
  { split; intro h'; linear_combination h' },
end

/-- A quadratic has roots if its discriminant has square roots -/
lemma exists_quadratic_eq_zero (ha : a ≠ 0) (h : ∃ s, discrim a b c = s * s) :
  ∃ x, a * x * x + b * x + c = 0 :=
begin
  rcases h with ⟨s, hs⟩,
  use (-b + s) / (2 * a),
  rw quadratic_eq_zero_iff ha hs,
  simp
end

/-- Root of a quadratic when its discriminant equals zero -/
lemma quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0) (h : discrim a b c = 0) (x : K) :
  a * x * x + b * x + c = 0 ↔ x = -b / (2 * a) :=
begin
  have : discrim a b c = 0 * 0, by rw [h, mul_zero],
  rw [quadratic_eq_zero_iff ha this, add_zero, sub_zero, or_self]
end

end field

section linear_ordered_field
variables {K : Type*} [linear_ordered_field K] {a b c : K}

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive. -/
lemma discrim_le_zero (h : ∀ x : K, 0 ≤ a * x * x + b * x + c) : discrim a b c ≤ 0 :=
begin
  rw [discrim, sq],
  obtain ha|rfl|ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0,
  -- if a < 0
  { have : tendsto (λ x, (a * x + b) * x + c) at_top at_bot :=
     tendsto_at_bot_add_const_right _ c ((tendsto_at_bot_add_const_right _ b
       (tendsto_id.neg_const_mul_at_top ha)).at_bot_mul_at_top tendsto_id),
    rcases (this.eventually (eventually_lt_at_bot 0)).exists with ⟨x, hx⟩,
    exact false.elim ((h x).not_lt $ by rwa ← add_mul) },
  -- if a = 0
  { rcases eq_or_ne b 0 with (rfl|hb),
    { simp },
    { have := h ((-c - 1) / b), rw [mul_div_cancel' _ hb] at this, linarith } },
  -- if a > 0
  { have ha' : 0 ≤ 4 * a := mul_nonneg zero_le_four ha.le,
    have := h (-b / (2 * a)),
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a)))),
    field_simp [ha.ne'],
    ring }
end

lemma discrim_le_zero_of_nonpos (h : ∀ x : K, a * x * x + b * x + c ≤ 0) : discrim a b c ≤ 0 :=
discrim_neg a b c ▸ discrim_le_zero (by simpa only [neg_mul, ← neg_add, neg_nonneg])

/--
If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
lemma discrim_lt_zero (ha : a ≠ 0) (h : ∀ x : K, 0 < a * x * x + b * x + c) : discrim a b c < 0 :=
begin
  have : ∀ x : K, 0 ≤ a*x*x + b*x + c := assume x, le_of_lt (h x),
  refine lt_of_le_of_ne (discrim_le_zero this) _,
  assume h',
  have := h (-b / (2 * a)),
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0,
  { rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))] },
  linarith
end

lemma discrim_lt_zero_of_neg (ha : a ≠ 0) (h : ∀ x : K, a * x * x + b * x + c < 0) :
  discrim a b c < 0 :=
discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) (by simpa only [neg_mul, ← neg_add, neg_pos])

end linear_ordered_field
