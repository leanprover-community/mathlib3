/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import analysis.special_functions.pow

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test). We prove this
test in `nnreal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to
prove `summable_one_div_rpow`.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/

open filter
open_locale big_operators ennreal nnreal topological_space

namespace finset

variables {M : Type*} [ordered_add_comm_monoid M] {f : ℕ → M}

lemma le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
  (∑ k in Ico 1 (2 ^ n), f k) ≤ ∑ k in range n, (2 ^ k) •ℕ f (2 ^ k) :=
begin
  induction n with n ihn, { simp },
  suffices : (∑ k in Ico (2 ^ n) (2 ^ (n + 1)), f k) ≤ (2 ^ n) •ℕ f (2 ^ n),
  { rw [sum_range_succ, add_comm, ← sum_Ico_consecutive],
    exact add_le_add ihn this,
    exacts [n.one_le_two_pow, nat.pow_le_pow_of_le_right zero_lt_two n.le_succ] },
  have : ∀ k ∈ Ico (2 ^ n) (2 ^ (n + 1)), f k ≤ f (2 ^ n) :=
    λ k hk, hf (pow_pos zero_lt_two _) (Ico.mem.mp hk).1,
  convert sum_le_sum this,
  simp [pow_succ, two_mul]
end

lemma le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
  (∑ k in range (2 ^ n), f k) ≤ f 0 + ∑ k in range n, (2 ^ k) •ℕ f (2 ^ k) :=
begin
  convert add_le_add_left (le_sum_condensed' hf n) (f 0),
  rw [← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ, sum_range_zero, add_zero]
end

lemma sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
  (∑ k in range n, (2 ^ k) •ℕ f (2 ^ (k + 1))) ≤ ∑ k in Ico 2 (2 ^ n + 1), f k :=
begin
  induction n with n ihn, { simp },
  suffices : (2 ^ n) •ℕ f (2 ^ (n + 1)) ≤ ∑ k in Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f k,
  { rw [sum_range_succ, add_comm, ← sum_Ico_consecutive],
    exact add_le_add ihn this,
    exacts [add_le_add_right n.one_le_two_pow _,
      add_le_add_right (nat.pow_le_pow_of_le_right zero_lt_two n.le_succ) _] },
  have : ∀ k ∈ Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f (2 ^ (n + 1)) ≤ f k :=
    λ k hk, hf (n.one_le_two_pow.trans_lt $ (nat.lt_succ_of_le le_rfl).trans_le (Ico.mem.mp hk).1)
      (nat.le_of_lt_succ $ (Ico.mem.mp hk).2),
  convert sum_le_sum this,
  simp [pow_succ, two_mul]
end

lemma sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
  (∑ k in range (n + 1), (2 ^ k) •ℕ f (2 ^ k)) ≤ f 1 + 2 •ℕ ∑ k in Ico 2 (2 ^ n + 1), f k :=
begin
  convert add_le_add_left (nsmul_le_nsmul_of_le_right (sum_condensed_le' hf n) 2) (f 1),
  simp [sum_range_succ', add_comm, pow_succ, mul_nsmul, sum_nsmul]
end

end finset

namespace ennreal

variable {f : ℕ → ennreal}

lemma le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
  (∑' k, f k) ≤ f 0 + ∑' k : ℕ, (2 ^ k) * f (2 ^ k) :=
begin
  rw [ennreal.tsum_eq_supr_nat' (nat.tendsto_pow_at_top_at_top_of_one_lt _root_.one_lt_two)],
  refine supr_le (λ n, (finset.le_sum_condensed hf n).trans (add_le_add_left _ _)),
  simp only [nsmul_eq_mul, nat.cast_pow, nat.cast_two],
  apply ennreal.sum_le_tsum
end

lemma tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
  (∑' k : ℕ, (2 ^ k) * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k :=
begin
  rw [ennreal.tsum_eq_supr_nat' (tendsto_at_top_mono nat.le_succ tendsto_id), two_mul, ← two_nsmul],
  refine supr_le (λ n, le_trans _ (add_le_add_left (nsmul_le_nsmul_of_le_right
    (ennreal.sum_le_tsum $ finset.Ico 2 (2^n + 1)) _) _)),
  simpa using finset.sum_condensed_le hf n
end

end ennreal

namespace nnreal

/-- Cauchy condensation test for a series of `nnreal` version. -/
lemma summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
  summable (λ k : ℕ, (2 ^ k) * f (2 ^ k)) ↔ summable f :=
begin
  simp only [← ennreal.tsum_coe_ne_top_iff_summable, ne.def, not_iff_not, ennreal.coe_mul,
    ennreal.coe_pow, ennreal.coe_two],
  split; intro h,
  { replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ennreal) ≤ f m :=
      λ m n hm hmn, ennreal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn),
    simpa [h, ennreal.add_eq_top] using (ennreal.tsum_condensed_le hf) },
  { replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ennreal) ≤ f m :=
      λ m n hm hmn, ennreal.coe_le_coe.2 (hf hm hmn),
    simpa [h, ennreal.add_eq_top] using (ennreal.le_tsum_condensed hf) }
end

end nnreal

/-- Cauchy condensation test for series of nonnegative real numbers. -/
lemma summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
  (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
  summable (λ k : ℕ, (2 ^ k) * f (2 ^ k)) ↔ summable f :=
begin
  set g : ℕ → ℝ≥0 := λ n, ⟨f n, h_nonneg n⟩,
  have : f = λ n, g n := rfl,
  simp only [this],
  have : ∀ ⦃m n⦄, 0 < m → m ≤ n → g n ≤ g m := λ m n hm h, nnreal.coe_le_coe.2 (h_mono hm h),
  exact_mod_cast nnreal.summable_condensed_iff this
end

open real

/-- Test for congergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
@[simp] lemma summable_nat_rpow_inv {p : ℝ} : summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p :=
begin
  cases le_or_lt 0 p with hp hp,
  { rw ← summable_condensed_iff_of_nonneg,
    { simp_rw [nat.cast_pow, nat.cast_two, ← rpow_nat_cast, ← rpow_mul zero_lt_two.le, mul_comm _ p,
        rpow_mul zero_lt_two.le, rpow_nat_cast, ← inv_pow', ← mul_pow,
        summable_geometric_iff_norm_lt_1],
      nth_rewrite 0 [← rpow_one 2],
      rw [← division_def, ← rpow_sub zero_lt_two, norm_eq_abs,
        abs_of_pos (rpow_pos_of_pos zero_lt_two _), rpow_lt_one_iff zero_lt_two.le],
      norm_num },
    { intro n,
      exact inv_nonneg.2 (rpow_nonneg_of_nonneg n.cast_nonneg _) },
    { intros m n hm hmn,
      exact inv_le_inv_of_le (rpow_pos_of_pos (nat.cast_pos.2 hm) _)
         (rpow_le_rpow m.cast_nonneg (nat.cast_le.2 hmn) hp) } },
  { suffices : ¬summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ),
    { have : ¬(1 < p) := λ hp₁, hp.not_le (zero_le_one.trans hp₁.le),
      simpa [this, -one_div] },
    { intro h,
      obtain ⟨k : ℕ, hk₁ : ((k ^ p)⁻¹ : ℝ) < 1, hk₀ : k ≠ 0⟩ :=
        ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and
          (eventually_cofinite_ne 0)).exists,
      apply hk₀,
      rw [← zero_lt_iff_ne_zero, ← @nat.cast_pos ℝ] at hk₀,
      simpa [inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp,
        hp.not_lt, hk₀] using hk₁ } }
end

@[simp] lemma nnreal.summable_one_div_rpow {p : ℝ} : summable (λ n, (n ^ p)⁻¹ : ℕ → ℝ≥0) ↔ 1 < p :=
by simp [← nnreal.summable_coe]
