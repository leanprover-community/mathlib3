import combinatorics.simple_graph.exponential_ramsey.section11

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


lemma f_deriv_aux {x : ℝ} (hx : x ≠ 2) : has_deriv_at (λ x : ℝ, 1 / (2 - x)) (1 / (2 - x) ^ 2) x :=
by simpa using ((has_deriv_at_id' x).const_sub 2).inv (sub_ne_zero_of_ne hx.symm)


lemma log_of_neg {x : ℝ} : log (-x) = log x := by rw [←log_abs, abs_neg, log_abs]
lemma logb_of_neg {b x : ℝ} : logb b (-x) = logb b x := by rw [logb, log_of_neg, logb]

lemma mul_bin_ent_inv {x : ℝ} : x * bin_ent 2 (1 / x) = - bin_ent 2 x :=
begin
  rcases eq_or_ne x 0 with rfl | hx₀,
  { simp },
  rcases eq_or_ne x 1 with rfl | hx₁,
  { simp },
  have : 1 - x⁻¹ = x⁻¹ * -(1 - x),
  { rw [neg_sub, mul_sub_one, inv_mul_cancel hx₀] },
  rw [bin_ent, bin_ent, one_div, this, mul_neg, logb_of_neg, logb_mul, logb_inv, neg_mul_neg,
    neg_mul, sub_neg_eq_add, mul_assoc, ←mul_add, mul_inv_cancel_left₀ hx₀],
  { ring_nf },
  { rwa [ne.def, inv_eq_zero] },
  { rwa [sub_ne_zero, ne_comm] },
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

lemma logb_base {b : ℝ} (hb : 1 < b) : logb b b = 1 := by rw [logb, div_self (log_pos hb).ne']

lemma bin_ent_one_half : bin_ent 2 (1 / 2) = 1 :=
begin
  rw [bin_ent],
  norm_num1,
  rw [one_div, logb_inv, logb_base one_lt_two],
  norm_num1
end

lemma f1_zero_left {y : ℝ} : f1 0 y = y + 2 :=
by rw [f1, sub_zero, bin_ent_one_half, zero_add, mul_one]

lemma f1_one_left {y : ℝ} : f1 1 y = y + 1 := by { rw [add_comm y], norm_num [f1] }

lemma logb_two_three_lower : 1054 / 665 < logb 2 3 :=
begin
  rw [div_lt_iff, mul_comm],
  swap, { norm_num1 },
  have : (665 : ℝ) = (665 : ℕ) := by norm_num1,
  rw [this, ←logb_pow, lt_logb_iff_rpow_lt],
  { norm_num1 },
  { norm_num1 },
  exact pow_pos (by norm_num1) _,
end

lemma logb_two_three_upper : logb 2 3 < 485 / 306 :=
begin
  rw [lt_div_iff, mul_comm],
  swap, { norm_num1 },
  have : (306 : ℝ) = (306 : ℕ) := by norm_num1,
  rw [this, ←logb_pow, logb_lt_iff_lt_rpow],
  { norm_num1 },
  { norm_num1 },
  exact pow_pos (by norm_num1) _,
end

lemma bin_ent_one_third : bin_ent 2 (1 / 3) = logb 2 3 - 2 / 3 :=
begin
  rw [bin_ent],
  norm_num1,
  rw [one_div, logb_inv, logb_div, logb_base one_lt_two],
  { ring_nf },
  { norm_num1 },
  { norm_num1 },
end

lemma bin_ent_one_third_lower : 0.91 ≤ bin_ent 2 (1 / 3) :=
begin
  rw [bin_ent_one_third, le_sub_iff_add_le],
  norm_num1,
  rw [div_le_iff, mul_comm],
  swap, { norm_num1 },
  have : (300 : ℝ) = (300 : ℕ) := by norm_num1,
  rw [this, ←logb_pow, le_logb_iff_rpow_le],
  { norm_num1 },
  { norm_num1 },
  exact pow_pos (by norm_num1) _,
end

lemma bin_ent_one_third_upper : bin_ent 2 (1 / 3) ≤ 0.92 :=
begin
  rw [bin_ent_one_third, sub_le_iff_le_add],
  norm_num1,
  rw [le_div_iff, mul_comm],
  swap, { norm_num1 },
  have : (75 : ℝ) = (75 : ℕ) := by norm_num1,
  rw [this, ←logb_pow, logb_le_iff_le_rpow],
  { norm_num1 },
  { norm_num1 },
  exact pow_pos (by norm_num1) _,
end

--   - log x ≤ x ^ (-1 / e)
--   - log (y ^ (-e)) ≤ y      --  y = x ^ (-1 / e)
--   e log y ≤ y
--   log y ≤ y / e
lemma log_le_div_exp_of_pos {y : ℝ} (hy : 0 ≤ y) : log y ≤ y / exp 1 :=
begin
  rcases eq_or_lt_of_le hy with rfl | hy',
  { simp },
  have := log_le_sub_one_of_pos (div_pos hy' (exp_pos 1)),
  rwa [log_div hy'.ne' (exp_pos _).ne', log_exp, sub_le_sub_iff_right] at this,
end

lemma neg_log_le_rpow {x : ℝ} (hx : 0 < x) : - log x ≤ x ^ (- 1 / exp 1) :=
begin
  have : 0 ≤ x ^ (- 1 / exp 1),
  { refine (rpow_pos_of_pos hx _).le },
  have := log_le_div_exp_of_pos this,
  rwa [log_rpow hx, div_mul_eq_mul_div, neg_one_mul, div_le_iff (exp_pos _),
    div_mul_cancel _ (exp_pos _).ne'] at this,
end

lemma log_mul_continuous : continuous (λ x, x * log x) :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  rcases ne_or_eq x 0 with hx | rfl,
  { exact continuous_at_id.mul (continuous_at_log hx) },
  rw [continuous_at, zero_mul, tendsto_zero_iff_abs_tendsto_zero],
  have h1e : 0 < 1 - 1 / exp 1,
  { refine sub_pos_of_lt _,
    rw [div_lt_iff (exp_pos _), one_mul],
    exact exp_one_gt_d9.trans_le' (by norm_num1) },
  have : ∀ x : ℝ, 0 < x → x < 1 → |x * log x| ≤ x ^ (1 - 1 / exp 1),
  { intros x hx₀ hx₁,
    rw [abs_mul, abs_of_pos hx₀, abs_of_neg (log_neg hx₀ hx₁), sub_eq_add_neg, rpow_add hx₀,
      rpow_one, ←neg_div],
    exact mul_le_mul_of_nonneg_left (neg_log_le_rpow hx₀) hx₀.le },
  have : ∀ x : ℝ, 0 ≤ x → x < 1 → |x * log x| ≤ x ^ (1 - 1 / exp 1),
  { intros x hx,
    rcases lt_or_eq_of_le hx with hx' | rfl,
    { exact this _ hx' },
    intro,
    rw [zero_mul, abs_zero, zero_rpow h1e.ne'] },
  have : ∀ᶠ x : ℝ in nhds 0, |x * log x| ≤ |x| ^ (1 - 1 / exp 1), -- might be useful
  { filter_upwards [eventually_abs_sub_lt 0 (zero_lt_one' ℝ)] with x hx,
    rw [sub_zero] at hx,
    refine (this (|x|) (abs_nonneg _) hx).trans' _,
    rw [log_abs, abs_mul, abs_mul, abs_abs] },
  refine squeeze_zero' _ this _,
  { filter_upwards with x using abs_nonneg _ },
  suffices : tendsto (λ (x : ℝ), |x| ^ (1 - 1 / exp 1)) (nhds 0) (nhds (|0| ^ (1 - 1 / exp 1))),
  { convert this using 2,
    rw [abs_zero, zero_rpow h1e.ne'] },
  exact (continuous_abs.tendsto _).rpow_const (or.inr h1e.le),
end

lemma bin_ent_continuous {b : ℝ} : continuous (λ x, bin_ent b x) :=
begin
  simp only [bin_ent_eq],
  exact ((log_mul_continuous.neg).add
    (log_mul_continuous.comp (continuous_const.sub continuous_id')).neg).div_const _,
end

lemma f_deriv_aux2 {x : ℝ} (hx₁ : x ≠ 1) :
  has_deriv_at (λ x : ℝ, x * bin_ent 2 x) (2 * bin_ent 2 x + logb 2 (1 - x)) x :=
begin
  rcases ne_or_eq x 0 with hx₀ | rfl,
  { have : has_deriv_at (λ x : ℝ, x * bin_ent 2 x) _ x :=
      has_deriv_at.mul (has_deriv_at_id' _) (bin_ent_deriv _ _ hx₀ hx₁),
    convert this using 1,
    rw [bin_ent],
    ring },
  rw [has_deriv_at_iff_is_o_nhds_zero],
  simp only [zero_add, zero_mul, sub_zero, bin_ent_zero, logb_one, mul_zero, smul_zero],
  rw is_o_iff_tendsto,
  swap,
  { rintro x rfl,
    simp },
  have : ∀ x, x * bin_ent 2 x / x = bin_ent 2 x,
  { intros x,
    rcases eq_or_ne x 0 with rfl | hx,
    { simp },
    rw [mul_div_cancel_left _ hx] },
  simp only [this],
  convert (@bin_ent_continuous 2).continuous_at using 1,
  simp
end

-- nicely defined when 1 < x
lemma f_deriv_aux3 {x : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
  has_deriv_at (λ x : ℝ, x * bin_ent 2 (1 / x)) (logb 2 x - logb 2 (x - 1)) x :=
begin
  simp only [mul_bin_ent_inv],
  convert (bin_ent_deriv _ _ hx₀ hx₁).neg using 1,
  rw [neg_sub, ←neg_sub x, logb_of_neg],
end

lemma f1_deriv {x y : ℝ} (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) :
  has_deriv_at (λ x', f1 x' y) (1 + logb 2 ((1 - x) / (2 - x))) x :=
begin
  have : has_deriv_at (λ x', f1 x' y)
      (1 + ((logb 2 (2 - x) - logb 2 (2 - x - 1)) * -1)) x,
  { refine ((has_deriv_at_id' _).add_const _).add _,
    refine (f_deriv_aux3 _ _).comp _ (has_deriv_at.const_sub 2 (has_deriv_at_id' x)),
    { exact sub_ne_zero_of_ne hx₂.symm },
    contrapose! hx₁,
    linarith only [hx₁] },
  convert this using 1,
  rw [add_right_inj, mul_neg_one, neg_sub, logb_div],
  { ring_nf },
  { contrapose! hx₁,
    linarith only [hx₁] },
  { exact sub_ne_zero_of_ne hx₂.symm },
end

lemma self_lt_bin_ent {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1 / 2) : x < bin_ent 2 x :=
begin
  cases le_or_lt (1 / 3) x,
  { refine hx'.trans_lt _,
    refine ((strict_mono_on_bin_ent_zero_half one_lt_two).monotone_on ⟨_, _⟩ ⟨hx.le, hx'⟩
      h).trans_lt' _,
    { norm_num1 },
    { norm_num1 },
    refine bin_ent_one_third_lower.trans_lt' _,
    norm_num1 },
  rw [←sub_pos],
  let f : ℝ → ℝ := λ x, bin_ent 2 x - x,
  have hf0 : f 0 = 0 := by simp [f],
  have h₁ : ∀ x ∈ Ioo (0 : ℝ) (1 / 3), has_deriv_at f (logb 2 (1 - x) - logb 2 x - 1) x,
  { intros x hx,
    refine (bin_ent_deriv 2 x hx.1.ne' _).sub (has_deriv_at_id' x),
    linarith only [hx.2] },
  have h₂ : ∀ (x : ℝ), x ∈ Ioo (0 : ℝ) (1 / 3) → 0 < logb 2 (1 - x) - logb 2 x - 1,
  { rintro y ⟨hy₀, hy₁⟩,
    rw [sub_pos, ←logb_div _ hy₀.ne', lt_logb_iff_rpow_lt one_lt_two, rpow_one, lt_div_iff hy₀],
    { linarith only [hy₁] },
    { refine div_pos (by linarith only [hy₁]) hy₀ },
    linarith only [hy₁] },
  have : strict_mono_on f (Icc (0 : ℝ) (1 / 3)),
  { refine convex.strict_mono_on_of_deriv_pos (convex_Icc _ _) _ _,
    { exact (bin_ent_continuous.sub continuous_id').continuous_on },
    rw [interior_Icc],
    intros x hx,
    rw has_deriv_at.deriv (h₁ x hx),
    exact h₂ x hx },
  specialize this ⟨le_rfl, by norm_num1⟩ ⟨hx.le, h.le⟩ hx,
  rwa [hf0] at this,
end

lemma self_le_bin_ent {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : x ≤ bin_ent 2 x :=
begin
  rcases lt_or_eq_of_le hx with hx₀ | rfl,
  { exact (self_lt_bin_ent hx₀ hx').le },
  simp
end

lemma continuous_on_mul_bin_ent_inv : continuous (λ x, x * bin_ent 2 (1 / x)) :=
begin
  simp only [mul_bin_ent_inv],
  exact bin_ent_continuous.neg
end

lemma continuous_on_f1 {y : ℝ} : continuous_on (λ x, f1 x y) {2}ᶜ :=
begin
  refine (continuous_id'.add continuous_const).continuous_on.add _,
  refine (continuous_const.sub continuous_id').continuous_on.mul _,
  refine continuous_on.comp bin_ent_continuous.continuous_on _ (set.maps_to_univ _ _),
  simp only [one_div],
  refine continuous_on.inv₀ (continuous_const.sub continuous_id').continuous_on _,
  simp only [sub_ne_zero],
  simp [eq_comm],
end

lemma strict_anti_on_f1 {y : ℝ} : strict_anti_on (λ x, f1 x y) (Icc (0 : ℝ) 1) :=
begin
  refine convex.strict_anti_on_of_deriv_neg (convex_Icc _ _) _ _,
  { exact continuous_on_f1.mono (by norm_num) },
  rw [interior_Icc],
  intros x hx,
  rw (f1_deriv hx.2.ne (by linarith only [hx.2])).deriv,
  have : 0 < 2 - x := by linarith only [hx.2],
  rw [←lt_neg_iff_add_neg', logb_lt_iff_lt_rpow one_lt_two (div_pos (sub_pos_of_lt hx.2) this),
    div_lt_iff this, rpow_neg_one, ←one_div],
  linarith [hx.1]
end

lemma eq_on_f2 {y : ℝ} :
  eq_on (λ x, f2 x y) (λ x, f1 x y - 1 / (log 2 * 40) * (1 - 1 / (2 - x))) {2}ᶜ :=
begin
  rintro x hx,
  dsimp,
  rw [f2, f1, sub_right_inj, one_sub_div],
  { ring_nf },
  rw [sub_ne_zero],
  exact ne.symm hx
end

lemma continuous_on_f2 {y : ℝ} : continuous_on (λ x, f2 x y) {2}ᶜ :=
begin
  refine (continuous_on_f1.sub (continuous_on_const.mul _)).congr eq_on_f2,
  refine continuous_on_const.sub _,
  simp only [one_div],
  refine (continuous_const.sub continuous_id').continuous_on.inv₀ _,
  intro x,
  rw [sub_ne_zero],
  exact ne.symm
end

lemma f2_has_deriv_at {x y : ℝ} (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) :
  has_deriv_at (λ x, f2 x y)
    (1 + logb 2 ((1 - x) / (2 - x)) + 1 / (log 2 * 40) * (1 / (2 - x) ^ 2)) x :=
begin
  refine has_deriv_at.congr_of_eventually_eq _ (eq_on.eventually_eq_of_mem eq_on_f2 _),
  swap,
  { simp only [compl_singleton_mem_nhds_iff],
    exact hx₂ },
  refine has_deriv_at.add (f1_deriv hx₁ hx₂) _,
  simp only [←mul_neg, neg_sub],
  refine has_deriv_at.const_mul _ _,
  refine has_deriv_at.sub_const _ _,
  exact f_deriv_aux hx₂,
end

lemma strict_anti_on_f2 {y : ℝ} :
  strict_anti_on (λ x, f2 x y) (Icc (1 / 2 : ℝ) 1) :=
begin
  refine convex.strict_anti_on_of_deriv_neg (convex_Icc _ _) (continuous_on_f2.mono _) _,
  { norm_num },
  rw [interior_Icc],
  rintro x ⟨hx₁, hx₂⟩,
  have h2x : x < 2 := by linarith only [hx₂],
  rw (f2_has_deriv_at hx₂.ne h2x.ne).deriv,
  have : 0 < log 2 := log_pos one_lt_two,
  have h₁ : logb 2 ((1 - x) / (2 - x)) ≤ logb 2 (1 / 3),
  { refine logb_le_logb_of_le one_le_two (div_pos (sub_pos_of_lt hx₂) (sub_pos_of_lt h2x)) _,
    rw [div_le_iff (sub_pos_of_lt h2x)],
    linarith only [hx₁] },
  rw [one_div, logb_inv] at h₁,
  replace h₁ : logb 2 ((1 - x) / (2 - x)) < - 1.5,
  { refine h₁.trans_lt _,
    rw [neg_lt_neg_iff],
    refine logb_two_three_lower.trans_le' _,
    norm_num1 },
  have h₂ : 1 / (log 2 * 40) * (1 / (2 - x) ^ 2) ≤ 1 / (log 2 * 40),
  { refine mul_le_of_le_one_right _ _,
    { positivity },
    refine div_le_one_of_le _ (sq_nonneg _),
    rw one_le_sq_iff;
    linarith only [hx₂] },
  replace h₂ : 1 / (log 2 * 40) * (1 / (2 - x) ^ 2) ≤ 0.05,
  { refine h₂.trans _,
    rw [mul_comm, ←div_div, div_le_div_iff this, mul_comm, mul_one_div, one_mul],
    { exact log_two_gt_d9.le.trans' (by norm_num1) },
    norm_num1 },
  linarith only [h₁, h₂],
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

lemma claim_a2 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  g x y < 1.9993 :=
begin
  clear hx,
  subst x,
  rw [g_eq],
end

#exit

lemma claim_a3 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.341)
  (h : x = 3 / 5 * y + 0.5454) :
  f1 x y < 1.9993 := sorry

lemma claim_a4 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0.341 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f2 x y < 1.9993 := sorry

lemma claim_a34 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f x y < 1.9993 :=
begin
  rw [f],
  simp only [le_x_iff_le_y h],
  split_ifs with h₁ h₁,
  { exact claim_a4 hx ⟨h₁, hy.2⟩ h },
  exact claim_a3 hx ⟨hy.1, le_of_not_le h₁⟩ h,
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
