/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.order.rearrangement
import data.nat.interval
import data.real.basic
import data.finset.sort

variables {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : a ≤ b + c) (h2 : b ≤ c + a)
  (h3 : c ≤ a + b)
include ha hb hc h1 h2 h3

theorem IMO_1983_Q6 : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) :=
begin
  by_cases h : c ≤ b ∧ b ≤ a,
  { have h4 : a * (b + c - a) ≤ b * (a + c - b) ∧ b * (a + c - b) ≤ c * (a + b - c),
    { sorry },
    have h5 : 1 / a ≤ 1 / b ∧ 1 / b ≤ 1 / c,
    { sorry },
    sorry },
end
