/-
Copyright (c) 2021 Alain Verberkmoes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Verberkmoes
-/

import tactic
open int

/-!
# IMO 2011 Q5

Let `f` be a function from the set of integers to the set
of positive integers.  Suppose that, for any two integers
`m` and `n`, the difference `f(m) − f(n)` is divisible by
`f(m − n)`.  Prove that, for all integers `m` and `n` with
`f(m) ≤ f(n)`, the number `f(n)` is divisible by `f(m)`.
-/

theorem imo2011_q5 (f : ℤ → ℤ) (hpos : ∀ n : ℤ, 0 < f n)
  (hdvd : ∀ m n : ℤ, f (m - n) ∣ f m - f n) :
∀ m n : ℤ, f m ≤ f n → f m ∣ f n :=
begin
  intros m n h_fm_le_fn,
  cases lt_or_eq_of_le h_fm_le_fn with h_fm_lt_fn h_fm_eq_fn,
  { -- m < n
    let d := f m - f (m - n),
    have h_fn_dvd_d : f n ∣ d,
    { rw ←sub_sub_self m n,
      exact hdvd m (m - n) },
    have h_d_lt_fn : d < f n,
    { refine lt_trans _ h_fm_lt_fn,
      exact sub_lt_self _ (hpos (m - n)) },
    have h_neg_d_lt_fn : -d < f n,
    { rw neg_sub,
      refine lt_trans (sub_lt_self _ (hpos m)) _,
      refine lt_of_le_of_lt _ (sub_lt_self _ (hpos m)),
      refine le_of_dvd (sub_pos.mpr h_fm_lt_fn) _,
      rw [←neg_sub (f m), dvd_neg],
      exact hdvd m n },
    have h_d_eq_zero : d = 0,
    { have hd : d > 0 ∨ d = 0 ∨ d < 0, from trichotomous d 0,
      rcases hd with (hd | hd | hd),
      { -- hd : d > 0
        have h₁ : f n ≤ d, from le_of_dvd hd h_fn_dvd_d,
        have h₂ : ¬ f n ≤ d, from not_le.mpr h_d_lt_fn,
        contradiction },
      { -- hd : d = 0
        exact hd },
      { -- hd : d < 0
        have h₁ : f n ≤ -d,
        { refine le_of_dvd _ _,
          { exact neg_pos.mpr hd },
          { exact (dvd_neg _ _).mpr h_fn_dvd_d } },
        have h₂ : ¬ f n ≤ -d := not_le.mpr h_neg_d_lt_fn,
        contradiction } },
    have h₁ : f m = f (m - n), from sub_eq_zero.mp h_d_eq_zero,
    have h₂ : f (m - n) ∣ f m - f n, from hdvd m n,
    rw ←h₁ at h₂,
    exact (dvd_iff_dvd_of_dvd_sub h₂).mp (dvd_refl _) },
  { -- m = n
    rw h_fm_eq_fn }
end