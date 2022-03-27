/-
Copyright (c) 2020 Ruben Van de Velde, Stanislas Polu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Stanislas Polu
-/

import data.real.basic
import analysis.normed_space.basic

/-!
# IMO 1972 B2

Problem: `f` and `g` are real-valued functions defined on the real line. For all `x` and `y`,
`f(x + y) + f(x - y) = 2f(x)g(y)`. `f` is not identically zero and `|f(x)| ≤ 1` for all `x`.
Prove that `|g(x)| ≤ 1` for all `x`.
-/

/--
This proof begins by introducing the supremum of `f`, `k ≤ 1` as well as `k' = k / ∥g y∥`. We then
suppose that the conclusion does not hold (`hneg`) and show that `k ≤ k'` (by
`2 * (∥f x∥ * ∥g y∥) ≤ 2 * k` obtained from the main hypothesis `hf1`) and that `k' < k` (obtained
from `hneg` directly), finally raising a contradiction with `k' < k'`.

(Authored by Stanislas Polu inspired by Ruben Van de Velde).
-/
example (f g : ℝ → ℝ)
  (hf1 : ∀ x, ∀ y, (f(x+y) + f(x-y)) = 2 * f(x) * g(y))
  (hf2 : ∀ y, ∥f(y)∥ ≤ 1)
  (hf3 : ∃ x, f(x) ≠ 0)
  (y : ℝ) :
  ∥g(y)∥ ≤ 1 :=
begin
  classical,
  set S := set.range (λ x, ∥f x∥),
  -- Introduce `k`, the supremum of `f`.
  let k : ℝ := Sup (S),

  -- Show that `∥f x∥ ≤ k`.
  have hk₁ : ∀ x, ∥f x∥ ≤ k,
  { have h : bdd_above S, from ⟨1, set.forall_range_iff.mpr hf2⟩,
    intro x,
    exact le_cSup h (set.mem_range_self x), },
  -- Show that `2 * (∥f x∥ * ∥g y∥) ≤ 2 * k`.
  have hk₂ : ∀ x, 2 * (∥f x∥ * ∥g y∥) ≤ 2 * k,
  { intro x,
    calc 2 * (∥f x∥ * ∥g y∥)
        = ∥2 * f x * g y∥ : by simp [real.norm_eq_abs, abs_mul, mul_assoc]
    ... = ∥f (x + y) + f (x - y)∥ : by rw hf1
    ... ≤ ∥f (x + y)∥ + ∥f (x - y)∥ : norm_add_le _ _
    ... ≤ k + k : add_le_add (hk₁ _) (hk₁ _)
    ... = 2 * k : (two_mul _).symm, },

  -- Suppose the conclusion does not hold.
  by_contra' hneg,
  set k' := k / ∥g y∥,

  -- Demonstrate that `k' < k` using `hneg`.
  have H₁ : k' < k,
  { have h₁ : 0 < k,
    { obtain ⟨x, hx⟩ := hf3,
      calc 0
          < ∥f x∥ : norm_pos_iff.mpr hx
      ... ≤ k : hk₁ x },
    rw div_lt_iff,
    apply lt_mul_of_one_lt_right h₁ hneg,
    exact trans zero_lt_one hneg },

  -- Demonstrate that `k ≤ k'` using `hk₂`.
  have H₂ : k ≤ k',
  { have h₁ : ∃ x : ℝ, x ∈ S,
    { use ∥f 0∥, exact set.mem_range_self 0, },
    have h₂ : ∀ x, ∥f x∥ ≤ k',
    { intros x,
      rw le_div_iff,
      { apply (mul_le_mul_left zero_lt_two).mp (hk₂ x) },
      { exact trans zero_lt_one hneg } },
    apply cSup_le h₁,
    rintros y' ⟨yy, rfl⟩,
    exact h₂ yy },

  -- Conclude by obtaining a contradiction, `k' < k'`.
  apply lt_irrefl k',
  calc k'
      < k : H₁
  ... ≤ k' : H₂,
end


/-- IMO 1972 B2

Problem: `f` and `g` are real-valued functions defined on the real line. For all `x` and `y`,
`f(x + y) + f(x - y) = 2f(x)g(y)`. `f` is not identically zero and `|f(x)| ≤ 1` for all `x`.
Prove that `|g(x)| ≤ 1` for all `x`.

This is a more concise version of the proof proposed by Ruben Van de Velde.
-/
example (f g : ℝ → ℝ)
  (hf1 : ∀ x, ∀ y, (f (x+y) + f(x-y)) = 2 * f(x) * g(y))
  (hf2 : bdd_above (set.range (λ x, ∥f x∥)))
  (hf3 : ∃ x, f(x) ≠ 0)
  (y : ℝ) :
  ∥g(y)∥ ≤ 1 :=
begin
  obtain ⟨x, hx⟩ := hf3,
  set k := ⨆ x, ∥f x∥,
  have h : ∀ x, ∥f x∥ ≤ k := le_csupr hf2,
  by_contra' H,
  have hgy : 0 < ∥g y∥,
    by linarith,
  have k_pos : 0 < k := lt_of_lt_of_le (norm_pos_iff.mpr hx) (h x),
  have : k / ∥g y∥ < k := (div_lt_iff hgy).mpr (lt_mul_of_one_lt_right k_pos H),
  have : k ≤ k / ∥g y∥,
  { suffices : ∀ x, ∥f x∥ ≤ k / ∥g y∥, from csupr_le this,
    intro x,
    suffices : 2 * (∥f x∥ * ∥g y∥) ≤ 2 * k,
      by { rwa [le_div_iff hgy, ←mul_le_mul_left zero_lt_two], apply_instance },
    calc 2 * (∥f x∥ * ∥g y∥)
        = ∥2 * f x * g y∥           : by simp [abs_mul, mul_assoc]
    ... = ∥f (x + y) + f (x - y)∥   : by rw hf1
    ... ≤ ∥f (x + y)∥ + ∥f (x - y)∥ : abs_add _ _
    ... ≤ 2 * k                     : by linarith [h (x+y), h (x -y)] },
  linarith,
end
