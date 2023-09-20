import combinatorics.simple_graph.exponential_ramsey.section11
import combinatorics.simple_graph.exponential_ramsey.log2_estimates
import combinatorics.simple_graph.exponential_ramsey.log_small

open set real simple_graph

section interval
lemma add_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
  x + y ∈ Icc (a + c) (b + d) :=
by simp only [mem_Icc] at hx hy ⊢; split; linarith

lemma sub_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
  x - y ∈ Icc (a - d) (b - c) :=
by simp only [mem_Icc] at hx hy ⊢; split; linarith

lemma mul_interval {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
  (ha : 0 < a) (hc : 0 < c) : x * y ∈ Icc (a * c) (b * d) :=
by simp only [mem_Icc] at hx hy ⊢; split; nlinarith

lemma mul_interval_of_neg_pos {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
  (ha : b < 0) (hc : 0 < c) : x * y ∈ Icc (a * d) (b * c) :=
by simp only [mem_Icc] at hx hy ⊢; split; nlinarith

lemma mul_interval_of_pos_neg {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
  (ha : 0 < a) (hc : d < 0) : x * y ∈ Icc (b * c) (a * d) :=
by simp only [mem_Icc] at hx hy ⊢; split; nlinarith

lemma mul_interval_of_neg {x y a b c d : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
  (hb : b < 0) (hc : d < 0) : x * y ∈ Icc (b * d) (a * c) :=
by simp only [mem_Icc] at hx hy ⊢; split; nlinarith

lemma const_interval {x : ℝ} : x ∈ Icc x x := by simp
lemma neg_interval {x a b : ℝ} (hx : x ∈ Icc a b) : -x ∈ Icc (-b) (-a) :=
by rwa [←preimage_neg_Icc, neg_mem_neg]

lemma interval_end {x a b c d : ℝ} (hx : x ∈ Icc a b) (hca : c ≤ a) (hbd : b ≤ d) : x ∈ Icc c d :=
Icc_subset_Icc hca hbd hx

end interval

section simple_values

lemma one_div_log_two_interval : 1 / log 2 ∈ Icc (1.442695040888963407 : ℝ) 1.442695040888963408 :=
begin
  rw [mem_Icc, le_one_div _ (log_pos one_lt_two), one_div_le (log_pos one_lt_two)],
  { exact ⟨log_two_lt_d20.le.trans (by norm_num1), log_two_gt_d20.le.trans' (by norm_num1)⟩ },
  { norm_num1 },
  { norm_num1 },
end

lemma log_three_interval : log 3 ∈ Icc (1.0986122886681096 : ℝ) 1.0986122886681097 :=
⟨log_three_gt_d20.le, log_three_lt_d20.le⟩

-- 1.5849625007211561814537389439478165087598144076924810604557526545...
lemma logb_two_three_interval : logb 2 3 ∈ Icc (1.58496250072115 : ℝ) 1.58496250072116 :=
begin
  rw [logb, div_eq_mul_one_div],
  refine interval_end (mul_interval log_three_interval one_div_log_two_interval _ _) _ _;
  norm_num1
end

lemma log_five_interval : log 5 ∈ Icc (1.609437912434100374 : ℝ) 1.609437912434100375 :=
⟨log_five_gt_d20.le, log_five_lt_d20.le⟩

-- 2.3219280948873623478703194294893901758648313930245806120547563958...
lemma logb_two_five_interval : logb 2 5 ∈ Icc (2.32192809488736234 : ℝ) 2.32192809488736235 :=
begin
  rw [logb, div_eq_mul_one_div],
  refine interval_end (mul_interval log_five_interval one_div_log_two_interval _ _) _ _;
  norm_num1
end

end simple_values

section generic

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

lemma bin_ent_one_half : bin_ent 2 (1 / 2) = 1 :=
begin
  rw [bin_ent],
  norm_num1,
  rw [one_div, logb_inv, logb_base two_pos one_lt_two.ne'],
  norm_num1
end

-- lemma logb_two_three_lower : 1054 / 665 < logb 2 3 :=
-- begin
--   rw [div_lt_iff, mul_comm],
--   swap, { norm_num1 },
--   have : (665 : ℝ) = (665 : ℕ) := by norm_num1,
--   rw [this, ←_root_.logb_pow, lt_logb_iff_rpow_lt],
--   { norm_num1 },
--   { norm_num1 },
--   exact pow_pos (by norm_num1) _,
-- end

-- lemma logb_two_three_upper : logb 2 3 < 485 / 306 :=
-- begin
--   rw [lt_div_iff, mul_comm],
--   swap, { norm_num1 },
--   have : (306 : ℝ) = (306 : ℕ) := by norm_num1,
--   rw [this, ←_root_.logb_pow, logb_lt_iff_lt_rpow],
--   { norm_num1 },
--   { norm_num1 },
--   exact pow_pos (by norm_num1) _,
-- end

lemma bin_ent_one_third : bin_ent 2 (1 / 3) = logb 2 3 - 2 / 3 :=
begin
  rw [bin_ent],
  norm_num1,
  rw [one_div, logb_inv, logb_div, logb_base two_pos one_lt_two.ne'],
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
  rw [this, ←_root_.logb_pow, le_logb_iff_rpow_le],
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
  rw [this, ←_root_.logb_pow, logb_le_iff_le_rpow],
  { norm_num1 },
  { norm_num1 },
  exact pow_pos (by norm_num1) _,
end

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

open filter

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

lemma continuous_logb {b : ℝ} : continuous_on (logb b) {0}ᶜ :=
continuous_on_log.div_const _

lemma continuous_on.logb {α : Type*} [topological_space α] {b : ℝ} {f : α → ℝ} {s : set α}
  (hf : continuous_on f s) (hf' : ∀ x ∈ s, f x ≠ 0) : continuous_on (λ x, logb b (f x)) s :=
continuous_on.comp continuous_logb hf (by simpa using hf')

lemma bin_ent_continuous {b : ℝ} : continuous (λ x, bin_ent b x) :=
begin
  simp only [bin_ent_eq],
  exact ((log_mul_continuous.neg).add
    (log_mul_continuous.comp (continuous_const.sub continuous_id')).neg).div_const _,
end

lemma logb_mul_continuous {b : ℝ} : continuous (λ x, x * logb b x) :=
begin
  simp only [logb, mul_div_assoc'],
  refine log_mul_continuous.div_const _
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

end generic

section

open filter

lemma f_deriv_aux {x : ℝ} (hx : x ≠ 2) : has_deriv_at (λ x : ℝ, 1 / (2 - x)) (1 / (2 - x) ^ 2) x :=
by simpa using ((has_deriv_at_id' x).const_sub 2).inv (sub_ne_zero_of_ne hx.symm)

lemma f1_zero_left {y : ℝ} : f1 0 y = y + 2 :=
by rw [f1, sub_zero, bin_ent_one_half, zero_add, mul_one]

lemma f1_one_left {y : ℝ} : f1 1 y = y + 1 := by { rw [add_comm y], norm_num [f1] }

--   - log x ≤ x ^ (-1 / e)
--   - log (y ^ (-e)) ≤ y      --  y = x ^ (-1 / e)
--   e log y ≤ y
--   log y ≤ y / e

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
  rw asymptotics.is_o_iff_tendsto,
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

lemma f1_deriv_helper {x : ℝ} (hx₁ : x ≠ 2) :
  has_deriv_at (λ x, (2 - x) * bin_ent 2 (1 / (2 - x))) (logb 2 (1 - 1 / (2 - x))) x :=
begin
  sorry
  -- have : has_deriv_at (λ x, (2 - x) * bin_ent (1 / (2 - x)))
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

#exit

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
  { refine _root_.logb_le_logb_of_le one_le_two (div_pos (sub_pos_of_lt hx₂) (sub_pos_of_lt h2x)) _,
    rw [div_le_iff (sub_pos_of_lt h2x)],
    linarith only [hx₁] },
  rw [one_div, logb_inv] at h₁,
  replace h₁ : logb 2 ((1 - x) / (2 - x)) < - 1.5,
  { refine h₁.trans_lt _,
    rw [neg_lt_neg_iff],
    refine logb_two_three_interval.1.trans_lt' _,
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

end

section values
open real

noncomputable def x_value : ℝ := (0.4339 + 2727 / 8000) / 0.4339
lemma x_value_eq : x_value = 30991 / 17356 := by norm_num [x_value]

lemma logb_x_value : 0.8364148 < logb 2 x_value ∧ logb 2 x_value < 0.8364149 :=
begin
  rw x_value_eq,
  refine log_base2_start (by norm_num1) le_rfl _,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.5941966840 1.5941966844,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.270731533 1.270731535,
  refine log_base2_square _,
  weaken 1.614758628 1.614758640,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.30372271 1.30372280,
  refine log_base2_square _,
  weaken 1.69969290 1.69969320,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.44447797 1.44447850,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.0432583 1.0432591,
  norm_num1,
  refine log_base2_square _,
  refine log_base2_square _,
  weaken 1.1845881 1.1845928,
  refine log_base2_square _,
  weaken 1.4032489 1.4032610,
  refine log_base2_square _,
  weaken 1.969107 1.969142,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.938691 1.938761,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.879261 1.879398,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.76581 1.76607,
  norm_num1,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.55904 1.55951,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.2153 1.2161,
  refine log_base2_square _,
  weaken 1.4769 1.4789,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.0906 1.0936,
  refine log_base2_square _,
  weaken 1.1894 1.1960,
  refine log_base2_square _,
  weaken 1.4146 1.4305,
  refine log_base2_square _,
  refine log_base2_half _,
  weaken 1.0005 1.0232,
  refine log_base2_square _,
  weaken 1.001 1.047,
  refine log_base2_square _,
  weaken 1.002 1.097,
  refine log_base2_square _,
  exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1),
end

lemma logb_two_x_value_interval : logb 2 x_value ∈ Icc (0.8364148 : ℝ) 0.8364149 :=
⟨logb_x_value.1.le, logb_x_value.2.le⟩

end values

open real simple_graph

lemma has_deriv_at.logb {f : ℝ → ℝ} {x b f' : ℝ} (hf : has_deriv_at f f' x)
  (hx : f x ≠ 0) : has_deriv_at (λ y, logb b (f y)) (f' / (f x * log b)) x :=
by simpa [div_div] using (hf.log hx).div_const (log b)

lemma has_deriv_at_logb {x b : ℝ} (hx : x ≠ 0) :
  has_deriv_at (logb b) (1 / (x * log b)) x :=
(has_deriv_at_id' _).logb hx

-- this expression is nicer to compare to g
noncomputable def g' (y : ℝ) := logb 2 (5 / 2) + (3 / 5 * y + 0.5454) * logb 2 (5 / 3) +
    y * logb 2 ((y + 2727 / 8000) / ((25 / 16) * y))

lemma g_line {x y : ℝ} (h : x = 3 / 5 * y + 0.5454) :
  g x y = g' y :=
begin
  subst x,
  rw [g_eq, g'],
  rcases eq_or_ne y 0 with rfl | hy,
  { rw [zero_mul, zero_mul] },
  congr' 3,
  field_simp [hy],
  ring_nf
end

-- for eval
lemma g'_eq1 {y : ℝ} (hy : 0 ≤ y) :
  g' y =
    (1.5454 - 7 / 5 * y) * logb 2 5 - (0.5454 + 3 / 5 * y) * logb 2 3 +
    y * logb 2 ((y + 2727 / 8000) / y) + 4 * y - 1 :=
begin
  rw [g', mul_comm (25 / 16) y, ←div_div, logb_div, logb_div, logb_base two_pos one_lt_two.ne'],
  rotate,
  { norm_num1 },
  { norm_num1 },
  { norm_num1 },
  { norm_num1 },
  rcases eq_or_lt_of_le hy with rfl | hy₀,
  { ring_nf },
  have : logb 2 (25 / 16) = 2 * logb 2 5 - 4,
  { have : (25 / 16 : ℝ) = 5 ^ 2 / 2 ^ 4, { norm_num1 },
    rw [this, logb_div, _root_.logb_pow, _root_.logb_pow, logb_base],
    all_goals { norm_num } },
  rw [logb_div, this],
  { ring_nf },
  { positivity },
  { norm_num1 },
end

-- for diff
lemma g'_eq2 {y : ℝ} (hy : 0 ≤ y) :
  g' y =
    (1.5454 * logb 2 5 - 0.5454 * logb 2 3 - 1) +
    y * (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3) +
    y * (logb 2 (y + 2727 / 8000) - logb 2 y) :=
begin
  rw [g'_eq1 hy],
  rcases eq_or_lt_of_le hy with rfl | hy₀,
  { simp },
  have : y + 2727 / 8000 ≠ 0, by linarith,
  rw [logb_div this hy₀.ne'],
  ring_nf
end

lemma continuous_g' : continuous_on g' (set.Ici 0) :=
begin
  refine continuous_on.congr _ (λ y, g'_eq2),
  refine continuous_on.add (continuous.continuous_on (by continuity)) _,
  simp only [mul_sub],
  refine (continuous_on_id.mul (continuous_on.logb (continuous_on_id.add _) _)).sub
    logb_mul_continuous.continuous_on,
  { exact continuous_on_const },
  intros x hx,
  rw [mem_Ici] at hx,
  dsimp,
  linarith
end

-- for diff
noncomputable def g'_deriv (y : ℝ) : ℝ := ((4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3) +
    ((logb 2 (y + 2727 / 8000) - logb 2 y) - 2727 / 8000 / log 2 / (y + 2727 / 8000)))

-- for eval
noncomputable def g'_deriv_alt (y : ℝ) : ℝ := ((4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3) +
    ((logb 2 ((y + 2727 / 8000) / y)) - 2727 / 8000 / (y + 2727 / 8000) * (1 / log 2)))

-- for diff
lemma has_deriv_at_g' {y : ℝ} (hy : 0 < y) : has_deriv_at g' (g'_deriv y) y :=
begin
  have hy5 : y + 2727 / 8000 ≠ 0, by linarith,
  have h₁ : has_deriv_at
    (λ y, (1.5454 * logb 2 5 - 0.5454 * logb 2 3 - 1) +
      y * (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3) +
      y * (logb 2 (y + 2727 / 8000) - logb 2 y))
    (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3 +
      (1 * (logb 2 (y + 2727 / 8000) - logb 2 y) +
      y * (1 / ((y + 2727 / 8000) * log 2) - 1 / (y * log 2)))) y,
  { refine ((has_deriv_at_mul_const _).const_add _).add ((has_deriv_at_id' y).mul _),
    refine (((has_deriv_at_id' y).add_const _).logb _).sub (has_deriv_at_logb hy.ne'),
    linarith },
  have h₂ : (4 - 7 / 5 * logb 2 5 - 3 / 5 * logb 2 3 +
      (1 * (logb 2 (y + 2727 / 8000) - logb 2 y) +
      y * (1 / ((y + 2727 / 8000) * log 2) - 1 / (y * log 2)))) =
    (g'_deriv y),
  { rw [one_mul, mul_sub, mul_one_div, mul_one_div, ←div_div y y, div_self hy.ne', ←div_div,
      ←sub_div, div_sub' _ _ _ hy5, mul_one, ←sub_sub, sub_self, zero_sub, div_div,
      mul_comm _ (log 2), neg_div, ←sub_eq_add_neg, ←div_div, g'_deriv] },
  rw [←h₂],
  have : set.eq_on g' _ (set.Ici 0) := λ y hy, g'_eq2 hy,
  refine h₁.congr_of_eventually_eq (eq_on.eventually_eq_of_mem this _),
  exact Ici_mem_nhds hy,
end

lemma g'_deriv_alt_eq {y : ℝ} (hy : 0 < y) : g'_deriv_alt y = g'_deriv y :=
begin
  have hy5 : y + 2727 / 8000 ≠ 0, by linarith,
  rw [g'_deriv_alt, g'_deriv, logb_div hy5 hy.ne'],
  congr' 2,
  rw [div_mul_div_comm, div_div, mul_one, mul_comm],
end

lemma has_deriv_at_g'_deriv {y : ℝ} (hy : 0 < y) :
  has_deriv_at g'_deriv (- (1 / log 2) * (7436529/64000000) / (y * (y + 2727 / 8000) ^ 2)) y :=
begin
  have hy5 : y + 2727 / 8000 ≠ 0, by linarith,
  have : has_deriv_at g'_deriv (1 / ((y + 2727 / 8000) * log 2) - 1 / (y * log 2) -
    (0 * (y + 2727 / 8000) - 2727 / 8000 / log 2 * 1) / (y + 2727 / 8000) ^ 2) y,
  { exact (((((has_deriv_at_id' y).add_const _).logb hy5).sub (has_deriv_at_logb hy.ne')).sub
      ((has_deriv_at_const _ _).div ((has_deriv_at_id' y).add_const _) hy5)).const_add _ },
  convert this using 1,
  have hy6 : y * 8000 + 2727 ≠ 0, by linarith,
  field_simp [hy6, hy.ne', (log_pos one_lt_two).ne'],
  ring,
end

lemma strict_anti_on_g'_deriv : strict_anti_on g'_deriv (set.Ioi 0) :=
begin
  refine convex.strict_anti_on_of_has_deriv_at_neg (convex_Ioi 0) (λ y, has_deriv_at_g'_deriv) _,
  rw [interior_Ioi],
  rintro x (hx : 0 < x),
  refine mul_neg_of_neg_of_pos _ (by positivity),
  simp only [one_div, neg_mul, right.neg_neg_iff],
  have := log_pos one_lt_two,
  positivity
end

-- lemma (1.5454 - 7 / 5 * y) * logb 2 5 - (0.5454 + 3 / 5 * y) * logb 2 3 +
--     y * logb 2 ((y + 2727 / 8000) / y) + 4 * y - 1

lemma g'_eval_max : g' 0.4339 ∈ Icc (1.99928 : ℝ) 1.99929 :=
begin
  rw g'_eq1,
  swap,
  { norm_num1 },
  rw [add_sub_assoc],
  refine interval_end
    (add_interval
      (add_interval
        (sub_interval
          (mul_interval const_interval logb_two_five_interval (by norm_num1) (by norm_num1))
          (mul_interval const_interval logb_two_three_interval (by norm_num1) (by norm_num1)))
        (mul_interval const_interval logb_two_x_value_interval (by norm_num1) (by norm_num1)))
    const_interval)
    (by norm_num1)
    (by norm_num1),
end

lemma g_deriv_eval_max : g'_deriv 0.4339 ∈ Icc (0.000000 : ℝ) 0.000001 :=
begin
  rw [←g'_deriv_alt_eq],
  swap, { norm_num1 },
  rw [g'_deriv_alt],
  refine interval_end
    (add_interval
      (sub_interval
        (sub_interval const_interval
          (mul_interval const_interval logb_two_five_interval (by norm_num1) (by norm_num1)))
          (mul_interval const_interval logb_two_three_interval (by norm_num1) (by norm_num1)))
      (sub_interval logb_two_x_value_interval
        (mul_interval const_interval one_div_log_two_interval (by norm_num1) (by norm_num1))))
    (by norm_num1)
    (by norm_num1),
end

lemma claim_a2_aux {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 0.75) : g' y < 1.9993 :=
begin
  cases le_total y 0.4339,
  { have hdif : differentiable_on ℝ g' (interior (Icc 0 (4339 / 10000))),
    { rw [interior_Icc],
      intros x hx,
      exact (has_deriv_at_g' hx.1).differentiable_at.differentiable_within_at },
    have hder : ∀ x ∈ interior (Icc (0 : ℝ) 0.4339), 0.000000 ≤ deriv g' x,
    { rw [interior_Icc],
      rintro x ⟨hx₀, hx₁⟩,
      rw (has_deriv_at_g' hx₀).deriv,
      refine (strict_anti_on_g'_deriv hx₀ (by norm_num) hx₁).le.trans' _,
      exact g_deriv_eval_max.1 },
    have := convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 0.4339)
      (continuous_g'.mono Icc_subset_Ici_self) hdif hder y ⟨hy.1, h⟩ 0.4339 (by norm_num) h,
    rw le_sub_iff_add_le at this,
    replace this := this.trans g'_eval_max.2,
    linarith only [this, h] },
  { have h₁ : Icc (4339 / 10000 : ℝ) 0.75 ⊆ Ici 0,
    { rw Icc_subset_Ici_iff; norm_num1 },
    have h₂ : Ioo (4339 / 10000 : ℝ) 0.75 ⊆ Ioi 0,
    { rintro x ⟨hx, _⟩,
      rw [mem_Ioi],
      linarith only [hx] },
    have hdif : differentiable_on ℝ g' (interior (Icc (4339 / 10000) 0.75)),
    { intros x hx,
      rw [interior_Icc] at hx,
      exact (has_deriv_at_g' (h₂ hx)).differentiable_at.differentiable_within_at },
    have hder : ∀ x ∈ interior (Icc (4339 / 10000 : ℝ) 0.75), deriv g' x ≤ 0.000001,
    { rintro x hx,
      rw [interior_Icc] at hx,
      rw (has_deriv_at_g' (h₂ hx)).deriv,
      refine (strict_anti_on_g'_deriv (by norm_num) (h₂ hx) hx.1).le.trans _,
      exact g_deriv_eval_max.2 },
    have := convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc 0.4339 0.75)
      (continuous_g'.mono h₁) hdif hder 0.4339 (by norm_num) y ⟨h, hy.2⟩ h,
    --   (continuous_g'.mono Icc_subset_Ici_self) hdif hder y ⟨hy.1, h⟩ 0.4339 (by norm_num) h,
    rw sub_le_comm at this,
    replace this := this.trans g'_eval_max.2,
    linarith only [this, hy.2] },
end

lemma claim_a2 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  simple_graph.g x y < 1.9993 :=
begin
  clear hx,
  rw [g_line h],
  exact claim_a2_aux hy
end

lemma claim_a3 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 0.75) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f1 x y < 1.9993 := sorry

lemma claim_a4 {x y : ℝ} (hx : x ∈ Icc (0.75 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 0.75)
  (h : x = 3 / 5 * y + 0.5454) :
  f2 x y < 1.9993 := sorry
