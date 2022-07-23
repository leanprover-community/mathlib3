/-
Copyright (c) 2022 boboquack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: boboquack.
-/
import data.real.basic
import tactic

/-!
# IMO 2022 Q2

Let `ℝ+` denote the set of positive real numbers. Find all functions `f : ℝ+ → ℝ+` 
such that for each `x ∈ ℝ+`, there is exactly one `y ∈ ℝ+` satisfying
`x f(y) + y f(x) ≤ 2`.

## Sketch of solution

`f(x) := 1/x` is the only solution. We first verify this is a solution, always
taking `x = y`. To show this is the only solution, we first prove that the given
identity implies `x = y` because otherwise we can derive `f(x) ≥ 1/x` and `f(y) ≥ 1/y`,
swiftly leading to contradiction. This then shows `f(x) ≤ 1/x` for all `x`, but
if this inequality is strict anywhere we obtain contradiction in the uniqueness
of `y` by taking `y` close enough to `x` (specified explicitly in this
formalisation), hence `f(x) := 1/x` is the only solution.

We make repeated use of the `recips_sum_two` lemma, which is a trivial consequence
of the AM-GM inequality but which can also be obtained from square factorisation.
For ease of manipulation, we take `0 < (each variable)` as hypotheses rather than
proving known facts about the reals translate to `ℝ+`.
-/

lemma recips_sum_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
  (hi : x * y⁻¹ + y * x⁻¹ ≤ 2) : x = y := 
begin 
  -- clear denominators and expand
  rw ← (mul_le_mul_right (mul_pos hx hy)) at hi,
  rw (show (x * y⁻¹ + y * x⁻¹) * (x * y) = x * x + y * y, by 
  { field_simp [hx.ne', hy.ne'],
    left, 
    ring,}) at hi,
  -- the conclusion is now trivial from `(x - y)² = 0` implying `x=y`
  nlinarith,
end

notation `ℝ+` := set.Ioi (0 : ℝ) 

theorem imo2022Q2 (f : ℝ+ → ℝ+) : 
  (∀ x : ℝ+, ∃! y : ℝ+, (x * f y + y * f x : ℝ) ≤ 2) ↔ ∀ x : ℝ+, (f x : ℝ) = x⁻¹ := 
begin 
  split, 
  swap,
  { -- First, the easy direction: showing `f(x) := 1/x` is indeed a solution
    intros hf x,
    rw hf x,
    -- Show `f` is positive over `ℝ+` and claim `y=x` works
    refine ⟨x, _⟩,
    dsimp only [hf x],
    have i0x : (0 : ℝ) < x, by exact set.mem_Ioi.mpr (subtype.mem x),
    refine ⟨_, λ y, λ hyx, _⟩, 
    { -- With this `f`, the inequality clearly holds with equality for `y=x`, ...
      rw [hf x],
      norm_num [i0x.ne'] },
    { -- whereas if the inequality holds, the conclusion is exactly our lemma.
      rw hf y at hyx,
      have i0y : (0 : ℝ) < y, by exact set.mem_Ioi.mpr (subtype.mem y),
      rw subtype.ext (recips_sum_two i0x i0y hyx), }, }, 
  { -- Now, the hard direction: showing that this is the only solution
    intro uf,
    have f_pos : ∀ x : ℝ+, (0 : ℝ) < f x, by 
    { exact (λ x, set.mem_Ioi.mpr (subtype.mem (f x))), },
    -- We first show that the unique `y` in the statement is always equal to `x`
    have uf_imp_eq : ∀ {a b : ℝ+}, (a * f b + b * f a : ℝ) ≤ 2 → a = b, by
    { intros a b hi,
      have i0a : (0 : ℝ) < a, by exact set.mem_Ioi.mpr (subtype.mem a),
      have i0b : (0 : ℝ) < b, by exact set.mem_Ioi.mpr (subtype.mem b),
      by_contra ic,
      -- With some sleight of hand, we assume `a f(a) < 1`, and prove this implies `a`
      -- is the unique value such that the inequality holds and thus that `a = b`
      -- which suffices to show that we only need to deal with `a⁻¹ ≤ f(a)`
      have : (b * a⁻¹ : ℝ) ≤ b * f a, by 
      { rw [mul_le_mul_left i0b, ←one_mul (a⁻¹ : ℝ), mul_inv_le_iff i0a],
        contrapose ic,
        rcases uf a with ⟨y, hy, uy⟩,
        rw [uy b hi, uy a (by linarith), not_not], },
      -- Similarly, we show we only need to deal with `b⁻¹ ≤ f(b)`
      have : (a * b⁻¹ : ℝ) ≤ a * f b, by 
      { rw [mul_le_mul_left i0a, ←one_mul (b⁻¹ : ℝ), mul_inv_le_iff i0b],
        contrapose ic,
        rcases uf b with ⟨z, hz, uz⟩,
        rw [uz a (by linarith), uz b (by linarith), not_not], },
      -- But if both of these hold, then we can use our lemma again to get `a = b`.
      exact ic (subtype.ext (recips_sum_two i0a i0b (by linarith))), },
    -- Using the above lemma, it is easy to show that `f(x) ≤ x⁻¹` everywhere 
    -- since the unique `y` must satisfy `y = x`.
    have f_le_inv: ∀ a : ℝ+, (f a : ℝ) ≤ a⁻¹, by 
    { intro a,
      rcases uf a with ⟨b, hb, ub⟩,
      have := hb,
      rw ←(uf_imp_eq this) at hb,
      rw inv_eq_one_div,
      have i0a : (0 : ℝ) < a, by exact set.mem_Ioi.mpr (subtype.mem a),
      exact (le_div_iff' i0a).mpr (by linarith), },
    intro x,
    have i0x : (0 : ℝ) < x, by exact set.mem_Ioi.mpr (subtype.mem x),
    by_contra hi,
    -- Now, suppose the inequality is tight. First, we perform some rewriting.
    have : (x * f x : ℝ) < 1, by
    { rw [←lt_div_iff' i0x, ←inv_eq_one_div],
      exact lt_iff_le_and_ne.mpr ⟨f_le_inv _, hi⟩, },
    rcases uf x with ⟨z, hz, uz⟩,
    have : (x : ℝ) = z, by exact congr_arg coe (uz x (by linarith)),
    -- If we pick a point `y` close enough to `x`, it turns out that the condition
    -- that `y` is not the unique value satisfying the inequality alongside 
    -- `f(y) ≤ y⁻¹` is enough to show the desired result. In particular, while
    -- ε-δ arguments can suffice to show this, we can give the explicit value of
    -- `y = (2 - x f(x)) / f(x)` to prove this result (this is not tight). Thus,
    -- we simply need to verify from our assumptions that the inequality does
    -- hold for `x` and `y` and also that `x ≠ y`, which are both easy.
    have iy : (x : ℝ) < ((2 - x * f x) / f x), by 
    { rw lt_div_iff (f_pos x),
      linarith, },
    have : ((2 - x * f x) / f x : ℝ) = z, by exact congr_arg coe 
      (uz ⟨(2 - x * f x) / f x, lt_trans i0x iy⟩ (by 
      { field_simp [(f_pos x).ne'],
        have := (mul_lt_mul_left i0x).mpr (lt_of_le_of_lt 
          (f_le_inv ⟨(2 - x * f x) / f x, lt_trans i0x iy⟩)
          (show (((2 - x * f x) / f x)⁻¹ : ℝ) < f x, by 
          { rw [inv_eq_one_div, one_div_div,  
              div_lt_iff ((show (0 : ℝ) < 2 - x * f x, by linarith))],
            nth_rewrite 0 ←mul_one (f x : ℝ), 
            rw [mul_lt_mul_left (f_pos x)],
            linarith, })),
        linarith, }) ), 
    linarith, },
end
