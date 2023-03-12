import trench.infinite_prod
import analysis.p_series

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal filter

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

lemma real.converges_prod_one_add_nat_rpow_inv_iff {a : ℝ} :
  converges_prod (λ n : ℕ, (1 : ℝ) + (n ^ a)⁻¹) ↔ 1 < a :=
begin
  rw [converges_prod_one_add_iff_summable, real.summable_nat_rpow_inv],
  intro,
  positivity
end

lemma real.converges_prod_one_sub_nat_rpow_inv_iff {a : ℝ} :
  converges_prod (λ n : ℕ, (1 : ℝ) - (n ^ a)⁻¹) ↔ 1 < a :=
begin
  rw [converges_prod_one_sub_iff_summable, real.summable_nat_rpow_inv],
  intro,
  positivity
end

lemma real.converges_prod_one_add_pow {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) :
  converges_prod (λ n : ℕ, (1 : ℝ) + (x ^ n))  :=
begin
  rw [converges_prod_one_add_iff_summable],
  { refine summable_geometric_of_norm_lt_1 _,
    simp [abs_lt, hx', neg_one_lt_zero.trans_le hx] },
  { intro,
    positivity }
end

lemma real.summable_pow_two_pow {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) :
  summable (λ (b : ℕ), x ^ 2 ^ b) :=
begin
   have : ‖x‖ < 1,
  { simp [abs_lt, hx', neg_one_lt_zero.trans_le hx] },
  refine summable_of_nonneg_of_le _ _ (summable_geometric_of_norm_lt_1 this),
  { intro,
    positivity },
  intro,
  exact pow_le_pow_of_le_one hx hx'.le (nat.lt_pow_self one_lt_two _).le
end

lemma real.converges_prod_one_add_pow_two_pow {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) :
  converges_prod (λ n : ℕ, (1 : ℝ) + (x ^ (2 ^ n)))  :=
begin
  rw [converges_prod_one_add_iff_summable],
  { exact real.summable_pow_two_pow hx hx' },
  { intro,
    positivity }
end

lemma has_prod_one_sub_two_div :
  has_prod (λ n : ℕ, (1 : ℝ) - 2 / ((n + 2) * (n + 3))) (1 / 3) :=
begin
  have hx' : ∀ x : ℕ, (2 : ℝ) < (x + 2) * (x + 3),
  { intro,
    norm_cast,
    ring_nf,
    simp [nat.succ_lt_succ_iff] },
  have hx : ∀ x : ℕ, (0 : ℝ) < (x + 2) * (x + 3) := λ _, zero_lt_two.trans (hx' _),
  have hb : ∀ b : ℕ, 0 <  (1 : ℝ) - 2 / ((b + 2) * (b + 3)),
  { intro b,
    rw [sub_pos, div_lt_iff (hx b), one_mul],
    exact hx' _ },
  suffices : tendsto (λ (s : finset ℕ), ∏ (x : ℕ) in s,
    surj_units ((1 - 2 / ((x + 2 : ℝ) * (↑x + 3))) : ℝ)) at_top (𝓝 (surj_units (1 / 3 : ℝ))),
  { convert has_prod_of_tendsto_of_forall_is_unit this (λ b, is_unit_iff_ne_zero.mpr (hb b).ne'),
    rw eq_comm,
    simp [is_unit_iff_ne_zero, three_ne_zero] },
  have h_anti : antitone (λ (s : finset ℕ), ∏ (x : ℕ) in s, (1 - 2 / ((x + 2 : ℝ) * (↑x + 3)))),
  { refine antitone_prod_of_le_one' _ (λ _, (hb _).le),
    intros,
    simp only [sub_le_self_iff],
    positivity },
  refine ((tendsto_surj_units_of_ne_zero _ _).comp
    ((tendsto_at_top_iff_tendsto_range_at_top' h_anti).mpr _)).congr _,
  { intro s,
    simp only [comp_app],
    rw prod_surj_units s (λ i : ℕ, (1 - 2 / ((↑i + 2 : ℝ) * (↑i + 3)))),
    simp [is_unit_iff_ne_zero, (hb _).ne'] },
  { norm_num },
  have : ∀ x : ℕ, (1 : ℝ) - 2 / ((↑x + 2) * (↑x + 3)) = (x + 1) * (x + 4) * ((x + 2) * (x + 3))⁻¹,
  { intro x,
    field_simp [(hx x).ne'],
    ring },
  have key : ∀ k, ∏ x in range k, (x + 1 : ℝ) * (x + 4) * ((x + 2) * (x + 3))⁻¹ = (k + 3) /
    (3 * k + 3),
  { intro k,
    induction k with k IH,
    { norm_num },
    rw [prod_range_succ, IH],
    have : ∀ k : ℕ, (3 * k + 3 : ℝ) ≠ 0,
    { intro,
      norm_cast,
      simp },
    rw eq_div_iff (this _),
    field_simp [(hx k).ne', this k],
    ring },
  simp_rw [this, key],
  rw [tendsto_iff_norm_tendsto_zero],
  simp only [real.norm_eq_abs],
  have ht : tendsto (λ n : ℕ, (2 : ℝ) / (3 * n + 3)) at_top (𝓝 0),
  { rw ←mul_zero (2 : ℝ),
    simp_rw div_eq_mul_inv,
    refine tendsto.const_mul _ (tendsto_inv_at_top_zero.comp _),
    refine tendsto_at_top_add_const_right _ _ _,
    refine tendsto.const_mul_at_top zero_lt_three _,
    exact tendsto_coe_nat_at_top_at_top },
  refine squeeze_zero (λ n, abs_nonneg _) _ ht,
  intros n,
  have h3 : (1 : ℝ) / 3 = (n + 1) / (3 * n + 3),
  { rw eq_div_iff,
    { field_simp,
      ring },
    { norm_cast,
      simp } },
  rw [h3, div_sub_div_same, add_sub_add_left_eq_sub, abs_le],
  norm_num,
  positivity
end
