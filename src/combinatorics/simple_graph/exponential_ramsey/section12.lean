/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.simple_graph.exponential_ramsey.necessary_log_estimates
import analysis.special_functions.log.monotone

/-!
# Section 12
-/
namespace simple_graph

open_locale big_operators exponential_ramsey nat real

open filter nat real set asymptotics

lemma g_monotone {x₀ x₁ y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1)
  (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x₁) :
  g x₀ y ≤ g x₁ y :=
begin
  rw [g_eq, g_eq, add_assoc, add_assoc, add_le_add_iff_left],
  refine add_le_add (mul_le_mul_of_nonneg_right hx (logb_nonneg one_lt_two (by norm_num1))) _,
  rcases eq_or_lt_of_le hy₀ with rfl | hy₀,
  { rw [zero_mul, zero_mul] },
  refine mul_le_mul_of_nonneg_left _ hy₀.le,
  refine logb_le_logb_of_le one_le_two (by positivity) _,
  refine mul_le_mul_of_nonneg_left _ (by norm_num1),
  exact div_le_div_of_le hy₀.le (add_le_add_right hx _)
end

lemma f_antitone_aux {y : ℝ}
  (hl : ∀ x₀ x₁, 0 ≤ x₀ → x₀ ≤ x₁ → x₁ ≤ 1 → f1 x₁ y ≤ f1 x₀ y)
  (hu : ∀ x₀ x₁, 0.75 ≤ x₀ → x₀ ≤ x₁ → x₁ ≤ 1 → f2 x₁ y ≤ f2 x₀ y) :
  ∀ x₀ x₁, 0 ≤ x₀ → x₀ ≤ x₁ → x₁ ≤ 1 → f x₁ y ≤ f x₀ y :=
begin
  have : ∀ x y, x ≤ 1 → f2 x y ≤ f1 x y,
  { intros x y hx,
    rw [f1, f2, sub_le_self_iff],
    refine mul_nonneg (one_div_nonneg.2 (mul_nonneg (log_nonneg one_le_two) (by norm_num1))) _,
    refine div_nonneg _ _; linarith only [hx] },
  intros x₀ x₁ hx₀ hx hx₁,
  rw [f],
  split_ifs,
  { rw [f],
    split_ifs,
    { exact hu _ _ ‹3 / 4 ≤ x₀› hx hx₁ },
    exact (this _ _ hx₁).trans (hl _ _ hx₀ hx hx₁) },
  rw [not_le] at h,
  rw [f, if_neg (hx.trans_lt h).not_le],
  exact hl _ _ hx₀ hx hx₁,
end

lemma f_antitone {x₀ x₁ y : ℝ} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x₁) (hx₁ : x₁ ≤ 1) :
  f x₁ y ≤ f x₀ y :=
begin
  refine f_antitone_aux _ _ _ _ hx₀ hx hx₁,
  { rw ←antitone_on_Icc_iff,
    exact strict_anti_on_f1.antitone_on },
  { rw ←antitone_on_Icc_iff,
    exact strict_anti_on_f2.antitone_on.mono (Icc_subset_Icc_left (by norm_num1)) },
end

lemma x_le_iff_y_le {x y : ℝ} (h : x = 3 / 5 * y + 0.5454) :
  x ≤ 3 / 4 ↔ y ≤ 0.341 :=
begin
  rw [h],
  split;
  { intro,
    linarith }
end

lemma le_x_iff_le_y {x y : ℝ} (h : x = 3 / 5 * y + 0.5454) :
  3 / 4 ≤ x ↔ 0.341 ≤ y :=
begin
  rw [h],
  split;
  { intro,
    linarith }
end

lemma claim_a34 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f x y < 1.9993 :=
begin
  rw [f],
  split_ifs with h₁ h₁,
  { exact claim_a4 ⟨h₁, hx.2⟩ hy h },
  exact claim_a3 ⟨hx.1, le_of_not_le h₁⟩ h,
end

lemma main_calculation {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75) :
  min (f x y) (g x y) < 1.9993 :=
begin
  have hxy : 3 / 5 * y + 0.5454 ∈ Icc (0 : ℝ) 1,
  { cases hy,
    split;
    linarith },
  set xy := 3 / 5 * y + 0.5454,
  cases le_total x xy,
  { refine (min_le_right _ _).trans_lt _,
    refine (claim_a2 hy rfl).trans_le' _,
    exact g_monotone hy.1 (hy.2.trans (by norm_num1)) hx.1 h },
  refine (min_le_left _ _).trans_lt _,
  refine (claim_a34 hxy hy rfl).trans_le' _,
  exact f_antitone hxy.1 h hx.2,
end

lemma main_calculation_useful {x y z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75) :
  max (min (f x y) (g x y)) 1.95 + (z - 1.9993) < z :=
begin
  rw [←max_add_add_right, max_lt_iff],
  exact ⟨by linarith [main_calculation hx hy], by linarith⟩,
end

lemma two_pow_calculation : (2 - 1 / 1429 : ℝ) ≤ logb 2 3.999 :=
begin
  have h₁ : (3.999 : ℝ) = (2 ^ (2 : ℝ)) * (1 - 1 / 4000 : ℝ),
  { norm_num1 },
  rw [h₁, logb_mul, logb_rpow two_pos one_lt_two.ne'],
  rotate,
  { norm_num1 },
  { norm_num1 },
  suffices : - (1 / 1429) ≤ logb 2 (1 - 1 / 4000),
  { linarith only [this] },
  rw [logb, le_div_iff (log_pos one_lt_two), neg_mul, neg_le, ←log_inv],
  refine (log_le_sub_one_of_pos (by norm_num1)).trans _,
  rw [mul_comm, mul_one_div, le_div_iff],
  { refine log_two_gt_d9.le.trans' _,
    norm_num1 },
  norm_num1
end

theorem exponential_ramsey : ∀ᶠ k : ℕ in at_top, (ramsey_number ![k, k] : ℝ) ≤ 3.999 ^ k :=
begin
  have hη : (0 : ℝ) < (2 - 1 / 1429) - 1.9993 := by norm_num1,
  filter_upwards [eleven_one _ hη, eventually_gt_at_top 0] with k hk hk₀,
  obtain ⟨x, hx, y, hy, h⟩ := hk,
  have := (h.trans_lt (main_calculation_useful hx hy)).le.trans two_pow_calculation,
  rwa [div_le_iff', ←logb_pow, logb_le_logb one_lt_two] at this,
  { rw [nat.cast_pos, ramsey_number_pos, fin.forall_fin_two],
    simp [hk₀.ne'] },
  { exact pow_pos (by norm_num1) _ },
  { rwa nat.cast_pos }
end

theorem exponential_ramsey' : ∃ K : ℕ, ∀ k ≥ K, (ramsey_number ![k, k] : ℝ) ≤ 3.999 ^ k :=
eventually_at_top.1 exponential_ramsey

lemma theorem_one_explicit :
  ∀ᶠ k : ℕ in at_top, (ramsey_number ![k, k] : ℝ) ≤ (4 - 2 ^ (- 10 : ℤ)) ^ k :=
by filter_upwards [exponential_ramsey] with k hk using
  hk.trans (pow_le_pow_of_le_left (by norm_num1) (by norm_num1) _)

theorem theorem_one :
  ∃ ε > 0, ∀ᶠ k : ℕ in at_top, (ramsey_number ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
⟨(2 : ℝ) ^ (-10 : ℤ), by norm_num1, theorem_one_explicit⟩

theorem theorem_one' :
  ∃ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (ramsey_number ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
⟨(2 : ℝ) ^ (-10 : ℤ), by norm_num1, eventually_at_top.1 theorem_one_explicit⟩

theorem theorem_one'' : ∃ c < 4, ∀ᶠ k : ℕ in at_top, (ramsey_number ![k, k] : ℝ) ≤ c ^ k :=
⟨3.999, by norm_num1, exponential_ramsey⟩

-- With the main theorem done, we take a short detour to get a version which holds for all k
-- but not with an explicit ε
lemma error_increasing : antitone_on (λ x : ℝ, sqrt x ^ x⁻¹) {x | exp 1 ≤ x} :=
begin
  have : ∀ x, 0 < x → sqrt x ^ x⁻¹ = exp ((log x / x) * 2⁻¹),
  { intros x hx,
    rw [sqrt_eq_rpow, ←rpow_mul hx.le, rpow_def_of_pos hx, one_div, div_eq_mul_inv, ←mul_assoc,
      mul_right_comm] },
  intros x hx y hy h,
  dsimp,
  rw [this _ ((exp_pos _).trans_le hx), this _ ((exp_pos _).trans_le hy), exp_le_exp],
  refine mul_le_mul_of_nonneg_right _ (by norm_num1),
  exact real.log_div_self_antitone_on hx hy h
end

-- for really small numbers, use the known values to get an exponential improvement
theorem tiny_bound : ∀ k ≤ 4, (ramsey_number ![k, k] : ℝ) ≤ (4 - 1) ^ k
| 0 _ := by simp
| 1 _ := by norm_num [ramsey_number_one_succ]
| 2 _ := by norm_num [ramsey_number_two_left]
| 3 _ := by rw [←diagonal_ramsey, diagonal_ramsey_three]; norm_num
| 4 _ := by rw [←diagonal_ramsey, diagonal_ramsey_four]; norm_num
| (n+5) h := by linarith [h]

-- for moderate numbers, use Erdos-Szekeres with Stirling to get an exponential improvement
-- note this works precisely because we have a constant upper bound on k
theorem medium_bound {K k : ℕ} {c : ℝ} (hkl : 4 < k) (hk' : k ≤ K)
  (hc : c = 4 - 4 * (sqrt K) ^ (-K⁻¹ : ℝ)) :
  (ramsey_number ![k, k] : ℝ) ≤ (4 - c) ^ k :=
begin
  refine diagonal_ramsey_upper_bound_simpler.trans _,
  rw [hc, sub_sub_self, mul_pow, div_eq_mul_inv],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  have h₁ : (0 : ℝ) < k := by positivity,
  have h₂ : (0 : ℝ) < k⁻¹ := by positivity,
  rw [←rpow_le_rpow_iff _ _ h₂, ←rpow_nat_cast _ k, ←rpow_mul, mul_inv_cancel h₁.ne', rpow_one,
    rpow_neg (sqrt_nonneg _), inv_rpow (sqrt_nonneg _)],
  rotate,
  { positivity },
  { positivity },
  { positivity },
  refine inv_le_inv_of_le (rpow_pos_of_pos (sqrt_pos_of_pos (nat.cast_pos.2 (by linarith))) _) _,
  have h₃ : exp 1 ≤ k := (nat.cast_le.2 hkl.le).trans' (exp_one_lt_d9.le.trans (by norm_num1)),
  have h₄ : (k : ℝ) ≤ K := nat.cast_le.2 hk',
  exact error_increasing h₃ (h₃.trans h₄) h₄
end

-- Without making the lower bound explicit in `exponential_ramsey`, we can't make `ε` here explicit
-- either.
theorem global_bound : ∃ ε > 0, ∀ k, (ramsey_number ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
begin
  obtain ⟨K, hK₄, hK : ∀ k : ℕ, _ ≤ _ → _ ≤ _⟩ := (at_top_basis' 4).mem_iff.1 exponential_ramsey,
  let c := 4 - 4 * (sqrt K) ^ (-K⁻¹ : ℝ),
  have : 0 < c,
  { rw [sub_pos, mul_lt_iff_lt_one_right, rpow_neg (sqrt_nonneg _)],
    swap, { norm_num1 },
    refine inv_lt_one (one_lt_rpow _ _),
    { rw [lt_sqrt zero_le_one, one_pow, nat.one_lt_cast],
      linarith only [hK₄] },
    positivity },
  refine ⟨min 0.001 c, lt_min (by norm_num1) this, _⟩,
  intro k,
  cases le_total K k,
  { refine (hK k h).trans (pow_le_pow_of_le_left (by norm_num1) _ _),
    rw [le_sub_comm],
    refine (min_le_left _ _).trans (by norm_num1) },
  cases le_or_lt k 4 with h₄ h₄,
  { refine (tiny_bound k h₄).trans _,
    refine pow_le_pow_of_le_left (by norm_num1) _ _,
    rw [le_sub_comm],
    exact (min_le_left _ _).trans (by norm_num1) },
  refine (medium_bound h₄ h rfl).trans _,
  refine pow_le_pow_of_le_left _ _ _,
  { rw [sub_sub_self],
    positivity },
  rw [sub_le_sub_iff_left],
  exact min_le_right _ _
end

end simple_graph
