/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.order.rearrangement
import data.nat.interval
import data.real.basic
import data.finset.sort
import data.fin.vec_notation
import tactic.fin_cases
import logic.equiv.fin
import tactic.norm_fin
import tactic.ring_exp
/--
# IMO 1983 Q6

Let `a`, `b` and `c` be the lengths of the sides of a triangle. Prove that
`a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) ≥ 0`

# Solution

Without loss of generality, we can assume that `a ≥ b ≥ c`, which implies that
`1 / a ≤ 1 / b ≤ 1 / c` and `a * (b + c - a) ≤ b * (a + c - b) ≤ c * (a + b - c)`
Then, using the rearrangment inequality we have that
`b * (a + c - b) / a + c * (a + b - c) / b + a * (b + c - a) / c ≥ `
  `a * (b + c - a) / a + b  * (a + c - b) / b + c * (a + b - c) / b`, which can be simplified to
  `0 ≤ b * (b - c) / a + c * (c - a) / b + a * (a - b) / c`
Then, multiplying both sides by `a * b * c` gives the required inequality
-/

variables {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : a ≤ b + c) (h2 : b ≤ c + a)
  (h3 : c ≤ a + b)
include ha hb hc h1 h2 h3

theorem IMO_1983_Q6 : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) :=
begin
  -- how do I split into cases without considering all `6` cases?
  by_cases h : c ≤ b ∧ b ≤ a,
  { have h4 : a * (b + c - a) ≤ b * (a + c - b) ∧ b * (a + c - b) ≤ c * (a + b - c),
    { split;
      nlinarith },
    have h5 : a⁻¹ ≤ b⁻¹ ∧ b⁻¹ ≤ c⁻¹,
    { split;
      rw [inv_le_inv];
      linarith },
    set f : fin 3 → ℝ := ![a⁻¹, b⁻¹, c⁻¹] with hf,
    set g : fin 3 → ℝ := ![a * (b + c  - a), b * (a + c - b), c * (a + b - c)] with hg,
    have hfm : monotone f,
    { rw hf,
      intros i j hij,
      fin_cases i;
      fin_cases j,
      swap 4,
      iterate 3 { simp, linarith },
      iterate 3 { exfalso, apply not_lt.mpr hij, norm_fin }},
    have hgm : monotone g,
    -- follow proof as above
    { rw hg,
      intros i j hij,
      fin_cases i;
      fin_cases j,
      swap 4,
      iterate 3 { simp, linarith },
      iterate 3 { exfalso, apply not_lt.mpr hij, norm_fin } },
    have hσ : {x | (fin_rotate 3) x ≠ x} ⊆ (@finset.univ (fin 3) _),
    { simp only [finset.coe_univ, set.subset_univ]},
    have hfg : monovary_on f g (@finset.univ (fin 3) _),
    { apply monovary.monovary_on,
      exact monotone.monovary hfm hgm },
    have h := monovary_on.sum_smul_comp_perm_le_sum_smul hfg hσ,
    simp only [fin_rotate_succ_apply, smul_eq_mul] at h,
    have huniv : (@finset.univ (fin 3) _) = {0, 1, 2},
    { ext x, fin_cases x; simp },
    rw huniv at h,
    iterate 4 { rw [finset.sum_insert _] at h },
    { iterate 2 { rw finset.sum_singleton at h },
      have h6 : (1 : fin 3) + 1 = 2 := by norm_fin,
      have h7 : (2 : fin 3) + 1 = 0 := by norm_fin,
      simp only [hf, hg, h6, h7, matrix.cons_val_zero, fin.zero_add, matrix.cons_val_one,
        matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.cons_append, matrix.empty_append,
        matrix.cons_vec_alt0, matrix.empty_vec_alt0, ← mul_assoc] at h,
      rw [inv_mul_cancel (ne_of_gt ha), inv_mul_cancel (ne_of_gt hb),
        inv_mul_cancel (ne_of_gt hc)] at h,
      have h8 :  a⁻¹ * b * (a + c - b) + (b⁻¹ * c * (a + b - c) + c⁻¹ * a * (b + c - a)) =
        a + b + c +  a⁻¹ * b * (c - b) + b⁻¹ * c * (a - c) + c⁻¹ * a * (b - a),
      { simp only [mul_sub, mul_add, mul_assoc, mul_comm b a, mul_comm c b, mul_comm a c],
        simp only [← mul_assoc],
        rw [inv_mul_cancel (ne_of_gt ha), inv_mul_cancel (ne_of_gt hb), inv_mul_cancel (ne_of_gt hc)],
        ring_exp_eq },
      have h9 : b + c - a + (a + c - b + (a + b - c)) = a + b + c := by abel,
      rw [one_mul, one_mul, one_mul, h8, h9] at h,
      replace h : a⁻¹ * b * (c - b) + b⁻¹ * c * (a - c) + c⁻¹ * a * (b - a) ≤ 0,
      { rw ← add_le_add_iff_left (a + b + c),
        convert h using 1;
        ring_exp_eq },
      replace h : 0 ≤ a⁻¹ * b * (b - c) + b⁻¹ * c * (c - a) + c⁻¹ * a * (a - b),
      { rw [← neg_zero, ← neg_le],
        convert h;
        { simp only [mul_sub], ring_exp_eq }},
      have habc : 0 < a * b * c := by norm_num [ha, hb, hc],
      rw [← mul_le_mul_left habc, mul_zero, mul_add, mul_add] at h,
      convert h using 1,
      rw (show a * b * c * (a⁻¹ * b * (b - c)) = a⁻¹ * a * b ^ 2 * c * (b - c), by ring_exp_eq),
      rw (show a * b * c * (b⁻¹ * c * (c - a)) = b⁻¹ * b * c ^ 2 * a * (c - a), by ring_exp_eq),
      rw (show a * b * c * (c⁻¹ * a * (a - b)) = c⁻¹ * c * a ^ 2 * b * (a - b), by ring_exp_eq),
      rw [inv_mul_cancel (ne_of_gt ha), inv_mul_cancel (ne_of_gt hb), inv_mul_cancel (ne_of_gt hc)],
      ring_exp_eq },
    all_goals { simp, norm_fin }},
    sorry
end
