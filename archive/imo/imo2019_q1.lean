/-
Copyright (c) 2020 Kevin Buzzard and Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kevin Lacker
-/

import tactic.linarith

/-!
# IMO 2019 Q1

Determine all functions `f : ℤ → ℤ` such that, for all integers `a` and `b`,
`f(2a) + 2f(b) = f(f(a + b))`.
-/

theorem imo2019Q1 (f : ℤ → ℤ) :
(∀ a b : ℤ, f (2 * a) + 2 * (f b) = f (f (a + b))) ↔
(∀ x, f x = 0) ∨ ∃ c, ∀ x, f x = 2 * x + c :=
begin
  split, swap,
  { -- easy way: f(x)=0 and f(x)=2x+c work.
    intro h,
    cases h,
    { -- zero function works
      intros a b,
      rw [h (2 * a), h b, h (f (a + b))],
      simp
    },
    { -- f(x)=2x+c works
      intros a b,
      cases h with c h,
      repeat {rw h},
      ring
    },
  },
  -- hard way.
  intro h, -- functional equation
  -- a=b=0 and a=-1,b=1 give this:
  have h0 : f 0 + 2 * f 0 = f(-2) + 2 * f 1,
    convert h 0 0,
    convert h (-1) 1,
  -- a=0 gives this:
  have h1 : ∀ b, f 0 + 2 * f b = f (f b),
    intro b, convert h 0 b, simp,
  -- a=-1 gives this:
  have h2 : ∀ b, f (-2) + 2 * f (b + 1) = f (f b),
    intro b, convert h (-1) (b+1); ring,
  -- equating right hand sides of h1 and h2 gives this:
  have h3 : ∃ m, ∀ b, f (b + 1) - f b = m,
    use f 1 - f 0,
    intro b,
    apply (mul_left_inj' (show (2 : ℤ) ≠ 0, from dec_trivial)).1,
    rw sub_mul,
    have h4 : f (b + 1) * 2 = f (f b) - f (-2),
      rw [←h2 b], simp [mul_comm],
    have h5 : f b * 2 = f (f b) - f 0,
      rw [←h1 b], simp [mul_comm],
    rw [h4, h5],
    rw eq_sub_of_add_eq h0.symm,
    ring,
  cases h3 with m h3,
  -- h3 and induction on b (upwards and downwards) gives this:
  have h4 : ∀ b, f b = m * b + f 0,
    intro b,
    apply int.induction_on' b 0, simp,
    { intros k hk hf,
      rw [eq_add_of_sub_eq (h3 k), hf],
      ring
    },
    { intros k hk hf,
      have h4 := h3 (k - 1),
      replace h4 := eq_add_of_sub_eq h4,
      rw add_comm m at h4,
      replace h4 := eq_sub_of_add_eq h4.symm,
      rw h4,
      rw add_comm at hf,
      rw eq_sub_of_add_eq hf.symm,
      rw sub_add_cancel,
      ring,
    },
  -- now sub h4 into h
  conv at h in (f (2 * _) + 2 * f _ = f (f (_))) begin
    rw h4 (2 * a),
    rw h4 b,
    rw h4 (a + b),
    rw h4 (m * (a + b) + f 0),
  end,
  -- and now it's straightforward from a=b=0 and a=0,b=1.
  have h5 : 2 * f 0 = m * f 0,
    { have h6 := h 0 0,
      simp at h6,
      linarith [h6],
    },
  by_cases h6 : f 0 = 0, swap,
  have h5' : f 0 * 2 = f 0 * m := by rw [mul_comm, h5, mul_comm],
    have h7 := (mul_right_inj' h6).1 h5',
    right,
    use (f 0),
    intro x,
    convert h4 x,
  rw h6 at h,
  by_cases h7 : m = 0,
    left,
    intro x,
    convert h4 x,
    rw [h6, h7],
    simp,
  have h8 : 2 * m = m * m,
    simpa using h 0 1,
  have h8' : m * 2 = m * m,
    rw [←h8, mul_comm],
  replace h8 := (mul_right_inj' h7).1 h8',
  right,
  use (f 0),
  intro x,
  convert h4 x,
end
