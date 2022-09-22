/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import analysis.seminorm
/-!
# The lattice of seminorms is not distributive

We provide an example of three seminorms over the ℝ-vector space ℝ×ℝ which don't satisfy the lattice
distributivity property `(p ⊔ q1) ⊓ (p ⊔ q2) ≤ p ⊔ (q1 ⊓ q2)`.

This proves the lattice `seminorm ℝ (ℝ × ℝ)` is not distributive.

## References

* https://en.wikipedia.org/wiki/Seminorm#Examples
-/

open seminorm
open_locale nnreal

namespace seminorm_not_distrib

@[simps] noncomputable def p : seminorm ℝ (ℝ×ℝ) :=
(norm_seminorm ℝ ℝ).comp (linear_map.fst _ _ _) ⊔ (norm_seminorm ℝ ℝ).comp (linear_map.snd _ _ _)

@[simps] noncomputable def q1 : seminorm ℝ (ℝ×ℝ) :=
(4 : ℝ≥0) • (norm_seminorm ℝ ℝ).comp (linear_map.fst _ _ _)

@[simps] noncomputable def q2 : seminorm ℝ (ℝ×ℝ) :=
(4 : ℝ≥0) • (norm_seminorm ℝ ℝ).comp (linear_map.snd _ _ _)

lemma eq_one : (p ⊔ (q1 ⊓ q2)) (1, 1) = 1 :=
begin
  suffices : (⨅ x : ℝ × ℝ, q1 x + q2 (1 - x)) ≤ 1, by simpa,
  apply cinfi_le_of_le bdd_below_range_add ((0, 1) : ℝ×ℝ), dsimp [q1, q2],
  simp only [abs_zero, smul_zero, sub_self, add_zero, zero_le_one],
end

/-- This is a counterexample to the distributivity of the lattice `seminorm ℝ (ℝ × ℝ)`. -/
lemma not_distrib : ¬((p ⊔ q1) ⊓ (p ⊔ q2) ≤ p ⊔ (q1 ⊓ q2)) :=
begin
  intro le_sup_inf,
  have c : ¬(4/3 ≤ (1:ℝ)) := by norm_num,
  apply c, nth_rewrite 2 ← eq_one,
  apply le_trans _ (le_sup_inf _),
  apply le_cinfi, intro x,
  cases le_or_lt x.fst (1/3) with h1 h1,
  { cases le_or_lt x.snd (2/3) with h2 h2,
    { calc 4/3 = 4 * (1 - 2/3) : by norm_num
           ... ≤ 4 * (1 - x.snd) : (mul_le_mul_left zero_lt_four).mpr (sub_le_sub_left h2 _)
           ... ≤ 4 * |1 - x.snd| : (mul_le_mul_left zero_lt_four).mpr (le_abs_self _)
           ... = q2 ((1, 1) - x) : rfl
           ... ≤ (p ⊔ q2) ((1, 1) - x) : le_sup_right
           ... ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) : le_add_of_nonneg_left (map_nonneg _ _) },
    { calc 4/3 = 2/3 + (1 - 1/3) : by norm_num
           ... ≤ x.snd + (1 - x.fst) : add_le_add (le_of_lt h2) (sub_le_sub_left h1 _)
           ... ≤ |x.snd| + |1 - x.fst| : add_le_add (le_abs_self _) (le_abs_self _)
           ... ≤ p x + p ((1, 1) - x) : add_le_add le_sup_right le_sup_left
           ... ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) : add_le_add le_sup_left le_sup_left } },
  { calc 4/3 = 4 * (1/3) : by norm_num
         ... ≤ 4 * x.fst : (mul_le_mul_left zero_lt_four).mpr (le_of_lt h1)
         ... ≤ 4 * |x.fst| : (mul_le_mul_left zero_lt_four).mpr (le_abs_self _)
         ... = q1 x : rfl
         ... ≤ (p ⊔ q1) x : le_sup_right
         ... ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) : le_add_of_nonneg_right (map_nonneg _ _) }
end

end seminorm_not_distrib
