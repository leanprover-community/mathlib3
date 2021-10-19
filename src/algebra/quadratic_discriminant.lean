/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import algebra.char_p.invertible
import order.filter.at_top_bot
import tactic.linarith

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

## Tags

polynomial, quadratic, discriminant, root
-/

open filter

section ring
variables {R : Type*}

/-- Discriminant of a quadratic -/
def discrim [ring R] (a b c : R) : R := b^2 - 4 * a * c

variables [comm_ring R] [integral_domain R] {a b c : R}

/--
A quadratic has roots if and only if its discriminant equals some square.
-/
lemma quadratic_eq_zero_iff_discrim_eq_sq (h2 : (2 : R) ≠ 0) (ha : a ≠ 0) (x : R) :
  a * x * x + b * x + c = 0 ↔ discrim a b c = (2 * a * x + b) ^ 2 :=
begin
  split,
  { assume h,
    calc discrim a b c
        = 4 * a * (a * x * x + b * x + c) + b * b - 4 * a * c : by { rw [h, discrim], ring }
    ... = (2*a*x + b)^2 : by ring },
  { assume h,
    have ha : 2 * 2 * a ≠ 0 := mul_ne_zero (mul_ne_zero h2 h2) ha,
    apply mul_left_cancel₀ ha,
    calc
      2 * 2 * a * (a * x * x + b * x + c) = (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) : by ring
      ... = 0 : by { rw [← h, discrim], ring }
      ... = 2*2*a*0 : by ring }
end

/-- A quadratic has no root if its discriminant has no square root. -/
lemma quadratic_ne_zero_of_discrim_ne_sq (h2 : (2 : R) ≠ 0) (ha : a ≠ 0)
  (h : ∀ s : R, discrim a b c ≠ s * s) (x : R) :
  a * x * x + b * x + c ≠ 0 :=
begin
  assume h',
  rw [quadratic_eq_zero_iff_discrim_eq_sq h2 ha, sq] at h',
  exact h _ h'
end

end ring

section field
variables {K : Type*} [field K] [invertible (2 : K)] {a b c x : K}

/-- Roots of a quadratic -/
lemma quadratic_eq_zero_iff (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
  a * x * x + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) :=
begin
  have h2 : (2 : K) ≠ 0 := nonzero_of_invertible 2,
  rw [quadratic_eq_zero_iff_discrim_eq_sq h2 ha, h, sq, mul_self_eq_mul_self_iff],
  have ne : 2 * a ≠ 0 := mul_ne_zero h2 ha,
  have : x = 2 * a * x / (2 * a) := (mul_div_cancel_left x ne).symm,
  have h₁ : 2 * a * ((-b + s) / (2 * a)) = -b + s := mul_div_cancel' _ ne,
  have h₂ : 2 * a * ((-b - s) / (2 * a)) = -b - s := mul_div_cancel' _ ne,
  split,
  { intro h', rcases h',
    { left, rw h', simpa [add_comm] },
    { right, rw h', simpa [add_comm, sub_eq_add_neg] } },
  { intro h', rcases h', { left, rw [h', h₁], ring }, { right, rw [h', h₂], ring } }
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

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
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
  { rcases em (b = 0) with (rfl|hb),
    { simp },
    { have := h ((-c - 1) / b), rw [mul_div_cancel' _ hb] at this, linarith } },
  -- if a > 0
  { have := calc
      4 * a * (a * (-(b / a) * (1 / 2)) * (-(b / a) * (1 / 2)) + b * (-(b / a) * (1 / 2)) + c)
          = (a * (b / a)) * (a * (b / a)) - 2 * (a * (b / a)) * b + 4 * a * c : by ring
      ... = -(b * b - 4 * a * c) : by { simp only [mul_div_cancel' b (ne_of_gt ha)], ring },
    have ha' : 0 ≤ 4 * a, by linarith,
    have h := (mul_nonneg ha' (h (-(b / a) * (1 / 2)))),
    rw this at h, rwa ← neg_nonneg }
end

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

end linear_ordered_field
