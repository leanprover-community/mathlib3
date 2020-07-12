/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import tactic.linarith

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

The discriminant of a quadratic `a*x*x + b*x + c` is `b*b - 4*a*c`.

## Main statements
• Roots of a quadratic can be written as `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`,
  where `s` is the square root of the discriminant.
• If the discriminant has no square root, then the corresponding quadratic has no root.
• If a quadratic is always non-negative, then its discriminant is non-positive.

## Tags

polynomial, quadratic, discriminant, root
-/

variables {α : Type*}

section lemmas

variables [linear_ordered_field α] {a b c : α}

lemma exists_le_mul_self : ∀ a : α, ∃ x : α, a ≤ x * x :=
begin
  classical, -- TODO: otherwise linarith performance sucks
  assume a, cases le_total 1 a with ha ha,
  { use a, exact le_mul_of_ge_one_left (by linarith) ha },
  { use 1, linarith }
end

lemma exists_lt_mul_self : ∀ a : α, ∃ x : α, a < x * x :=
begin
  classical, -- todo: otherwise linarith performance sucks
  assume a, rcases (exists_le_mul_self a) with ⟨x, hx⟩,
  cases le_total 0 x with hx' hx',
  { use (x + 1),
    have : (x+1)*(x+1) = x*x + 2*x + 1, {ring},
    exact lt_of_le_of_lt hx (by rw this; linarith) },
  { use (x - 1),
    have : (x-1)*(x-1) = x*x - 2*x + 1, {ring},
    exact lt_of_le_of_lt hx (by rw this; linarith) }
end

end lemmas

variables [linear_ordered_field α] {a b c x : α}

/-- Discriminant of a quadratic -/
def discrim [ring α] (a b c : α) : α := b^2 - 4 * a * c

/--
A quadratic has roots if and only if its discriminant equals some square.
-/
lemma quadratic_eq_zero_iff_discrim_eq_square (ha : a ≠ 0) :
  ∀ x : α, a * x * x + b * x + c = 0 ↔  discrim a b c = (2 * a * x + b)^2 :=
by classical; exact -- TODO: otherwise linarith performance sucks
assume x, iff.intro
  (assume h, calc
      discrim a b c = 4*a*(a*x*x + b*x + c) + b*b - 4*a*c : by rw [h, discrim]; ring
      ... = (2*a*x + b)^2 : by ring)
  (assume h,
    have ha : 2*2*a ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero two_ne_zero) ha,
    mul_left_cancel' ha $
    calc
      2 * 2 * a * (a * x * x + b * x + c) = (2*a*x + b)^2 - (b^2 - 4*a*c) : by ring
      ... = 0 : by { rw [← h, discrim], ring }
      ... = 2*2*a*0 : by ring)

/-- Roots of a quadratic -/
lemma quadratic_eq_zero_iff (ha : a ≠ 0) {s : α} (h : discrim a b c = s * s) :
  ∀ x : α, a * x * x + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := assume x,
begin
  classical, -- TODO: otherwise linarith performance sucks
  rw [quadratic_eq_zero_iff_discrim_eq_square ha, h, pow_two, mul_self_eq_mul_self_iff],
  have ne : 2 * a ≠ 0 := mul_ne_zero two_ne_zero ha,
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
lemma exist_quadratic_eq_zero (ha : a ≠ 0) (h : ∃ s, discrim a b c = s * s) :
  ∃ x, a * x * x + b * x + c = 0 :=
begin
  rcases h with ⟨s, hs⟩,
  use (-b + s) / (2 * a),
  rw quadratic_eq_zero_iff ha hs,
  simp
end

/-- Root of a quadratic when its discriminant equals zero -/
lemma quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0) (h : discrim a b c = 0) :
  ∀ x : α, a * x * x + b * x + c = 0 ↔ x = -b / (2 * a) := assume x,
begin
  classical, -- TODO: otherwise linarith performance sucks
  have : discrim a b c = 0 * 0 := eq.trans h (by ring),
  rw quadratic_eq_zero_iff ha this,
  simp
end

/-- A quadratic has no root if its discriminant has no square root. -/
lemma quadratic_ne_zero_of_discrim_ne_square (ha : a ≠ 0) (h : ∀ s : α, discrim a b c ≠ s * s) :
  ∀ (x : α), a * x * x + b * x + c ≠ 0 :=
begin
  assume x h',
  rw [quadratic_eq_zero_iff_discrim_eq_square ha, pow_two] at h',
  have := h _,
  contradiction
end

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
lemma discriminant_le_zero {a b c : α} (h : ∀ x : α,  0 ≤ a*x*x + b*x + c) : discrim a b c ≤ 0 :=
by classical; exact -- TODO: otherwise linarith performance sucks
have hc : 0 ≤ c, by { have := h 0, linarith },
begin
  rw [discrim, pow_two],
  cases lt_trichotomy a 0 with ha ha,
  -- if a < 0
  cases classical.em (b = 0) with hb hb,
  { rw hb at *,
    rcases exists_lt_mul_self (-c/a) with ⟨x, hx⟩,
    have := mul_lt_mul_of_neg_left hx ha,
    rw [mul_div_cancel' _ (ne_of_lt ha), ← mul_assoc] at this,
    have h₂ := h x, linarith },
  { cases classical.em (c = 0) with hc' hc',
    { rw hc' at *,
      have : -(a*-b*-b + b*-b + 0) = (1-a)*(b*b), {ring},
      have h := h (-b), rw [← neg_nonpos, this] at h,
      have : b * b ≤ 0 := nonpos_of_mul_nonpos_left h (by linarith),
      linarith },
    { have h := h (-c/b),
      have : a*(-c/b)*(-c/b) + b*(-c/b) + c = a*((c/b)*(c/b)),
      { rw mul_div_cancel' _ hb, ring },
      rw this at h,
      have : 0 ≤ a := nonneg_of_mul_nonneg_right h (mul_self_pos $ div_ne_zero hc' hb),
      linarith [ha] } },
  cases ha with ha ha,
  -- if a = 0
  cases classical.em (b = 0) with hb hb,
    { rw [ha, hb], linarith },
    { have := h ((-c-1)/b), rw [ha, mul_div_cancel' _ hb] at this, linarith },
  -- if a > 0
  have := calc
    4*a* (a*(-(b/a)*(1/2))*(-(b/a)*(1/2)) + b*(-(b/a)*(1/2)) + c)
      = (a*(b/a)) * (a*(b/a)) - 2*(a*(b/a))*b + 4*a*c : by ring
    ... = -(b*b - 4*a*c) : by { simp only [mul_div_cancel' b (ne_of_gt ha)], ring },
  have ha' : 0 ≤ 4*a, {linarith},
  have h := (mul_nonneg ha' (h (-(b/a) * (1/2)))),
  rw this at h, rwa ← neg_nonneg
end

/--
If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
lemma discriminant_lt_zero {a b c : α} (ha : a ≠ 0) (h : ∀ x : α,  0 < a*x*x + b*x + c) :
  discrim a b c < 0 :=
begin
  classical, -- TODO: otherwise linarith performance sucks
  have : ∀ x : α, 0 ≤ a*x*x + b*x + c := assume x, le_of_lt (h x),
  refine lt_of_le_of_ne (discriminant_le_zero this) _,
  assume h',
  have := h (-b / (2 * a)),
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0,
  { rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))] },
  linarith
end
