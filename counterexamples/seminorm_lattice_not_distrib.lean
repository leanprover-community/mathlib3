/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import analysis.seminorm
/-!
# The lattice of seminorms is not distributive

We provide an example of three seminorms over the ℝ-vector space ℝ×ℝ whih dont verify the lattice
distributivity property (p ⊔ q1) ⊓ (p ⊔ q2) ≤ p ⊔ (q1 ⊓ q2).

This proves the lattice (seminorm ℝ ℝ×ℝ) is not distributive.

## References

* https://en.wikipedia.org/wiki/Seminorm#Examples
-/

private lemma bdd_below_range_add {𝕜 E : Type*} [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
  (x : E) (p q : seminorm 𝕜 E) :
  bdd_below (set.range (λ (u : E), p u + q (x - u))) :=
by { use 0, rintro _ ⟨x, rfl⟩, exact add_nonneg (p.nonneg _) (q.nonneg _) }

noncomputable def p : seminorm ℝ (ℝ×ℝ) :=
{ to_fun := λ x, |x.fst| ⊔ |x.snd|,
  triangle' := λ x y, begin
    apply sup_le,
    { apply le_trans (abs_add _ _), apply add_le_add, exact le_sup_left, exact le_sup_left },
    { apply le_trans (abs_add _ _), apply add_le_add, exact le_sup_right, exact le_sup_right }
  end,
  smul' := λ a x, begin
    change |a * x.fst| ⊔ |a * x.snd| = |a| * (|x.fst| ⊔ |x.snd|),
    rw abs_mul, rw abs_mul,
    cases (le_or_lt (|x.fst|) (|x.snd|)),
    { rw sup_eq_right.mpr h, exact sup_eq_right.mpr (mul_le_mul_of_nonneg_left h (abs_nonneg _)) },
    { have h := le_of_lt h,
      rw sup_eq_left.mpr h, exact sup_eq_left.mpr (mul_le_mul_of_nonneg_left h (abs_nonneg _)) }
  end }

noncomputable def q1 : seminorm ℝ (ℝ×ℝ) :=
{ to_fun := λ x, 4 * |x.fst|,
  triangle' := λ x y, begin
    rw [← mul_add, mul_le_mul_left], { exact abs_add _ _ }, { norm_num }
  end,
  smul' := λ a x, begin
    change 4 * |a * x.fst| = |a| * (4 * |x.fst|),
    rw abs_mul, ring
  end }

noncomputable def q2 : seminorm ℝ (ℝ×ℝ) :=
{ to_fun := λ x, 4 * |x.snd|,
  triangle' := λ x y, begin
    rw [← mul_add, mul_le_mul_left], { exact abs_add _ _ }, { norm_num }
  end,
  smul' := λ a x, begin
    change 4 * |a * x.snd| = |a| * (4 * |x.snd|),
    rw abs_mul, ring
  end }

lemma eq_one : (p ⊔ (q1 ⊓ q2)) (1, 1) = 1 := begin
  change |1| ⊔ |1| ⊔ (q1 ⊓ q2) (1, 1) = 1,
  rw [sup_idem, abs_one, sup_eq_left],
  apply cinfi_le_of_le (bdd_below_range_add _ _ _) ((0, 1) : ℝ×ℝ),
  simp only [prod.mk_sub_mk, sub_zero, sub_self], change (4 * |(0:ℝ)| + 4 * |(0:ℝ)| ≤ 1),
  simp only [abs_zero, mul_zero, add_zero, zero_le_one]
end

/-- This is a counterexample to the distributivity of the lattice (seminorm ℝ (ℝ×ℝ)). -/
lemma not_distrib : ¬((p ⊔ q1) ⊓ (p ⊔ q2) ≤ p ⊔ (q1 ⊓ q2)) := begin
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
           ... ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) : le_add_of_nonneg_left ((p ⊔ q1).nonneg _) },
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
         ... ≤ (p ⊔ q1) x + (p ⊔ q2) ((1, 1) - x) : le_add_of_nonneg_right ((p ⊔ q2).nonneg _) }
end
