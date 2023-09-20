import combinatorics.simple_graph.exponential_ramsey.necessary_log_estimates

namespace simple_graph

open_locale big_operators exponential_ramsey nat real

open filter nat real set asymptotics

lemma g_monotone {x₀ x₁ y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1)
  (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x₁) (hx₁ : x₁ ≤ 1) :
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

lemma f_antitone_aux {y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1)
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

lemma f_antitone {x₀ x₁ y : ℝ} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x₁) (hx₁ : x₁ ≤ 1)
  (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
  f x₁ y ≤ f x₀ y :=
begin
  refine f_antitone_aux hy₀ hy₁ _ _ _ _ hx₀ hx hx₁,
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

lemma claim_a3 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 0.75) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f1 x y < 1.9993 := sorry

lemma claim_a4 {x y : ℝ} (hx : x ∈ Icc (0.75 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f2 x y < 1.9993 := sorry

lemma claim_a34 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f x y < 1.9993 :=
begin
  rw [f],
  split_ifs with h₁ h₁,
  { exact claim_a4 ⟨h₁, hx.2⟩ hy h },
  exact claim_a3 ⟨hx.1, le_of_not_le h₁⟩ hy h,
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
    refine (claim_a2 hxy hy rfl).trans_le' _,
    exact g_monotone hy.1 (hy.2.trans (by norm_num1)) hx.1 h hxy.2 },
  refine (min_le_left _ _).trans_lt _,
  refine (claim_a34 hxy hy rfl).trans_le' _,
  exact f_antitone hxy.1 h hx.2 hy.1 (hy.2.trans (by norm_num1)),
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

end simple_graph
