/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.simple_graph.exponential_ramsey.section7

/-!
# Section 8
-/
namespace simple_graph

open_locale big_operators exponential_ramsey

open filter finset nat real asymptotics

variables {V : Type*} [decidable_eq V] [fintype V] {χ : top_edge_labelling V (fin 2)}
variables {k l : ℕ} {ini : book_config χ} {i : ℕ}

/-- force x to live in [a,b], and assume a ≤ b -/
noncomputable def clamp (a b x : ℝ) : ℝ :=
max a $ min b x

lemma clamp_le {a b x : ℝ} (h : a ≤ b) : clamp a b x ≤ b := max_le h (min_le_left _ _)
lemma le_clamp {a b x : ℝ} : a ≤ clamp a b x := le_max_left _ _

lemma clamp_eq {a b x : ℝ} (h : a ≤ b) :
  clamp a b x = min b (max a x) :=
begin
  rw [clamp],
  rcases min_cases b x with (h' | h'),
  { rw [h'.1, max_eq_right h, min_eq_left (le_max_of_le_right h'.2)] },
  rw [h'.1, min_eq_right],
  exact max_le h h'.2.le,
end

lemma yael {a b x : ℝ} (h : a ≤ b) : clamp a b x = a + min b x - min a x :=
begin
  rw [clamp],
  rcases min_cases b x with (h' | h'),
  { rw [h'.1, min_eq_left (h.trans h'.2), max_eq_right h],
    simp },
  rw [h'.1, eq_sub_iff_add_eq', min_add_max],
end

/-- p' in section 8 -/
noncomputable def p' (μ : ℝ) (k l : ℕ) (ini : book_config χ) (i : ℕ) (h : ℕ) : ℝ :=
if h = 1
  then min (q_function k ini.p h) (algorithm μ k l ini i).p
  else clamp (q_function k ini.p (h - 1)) (q_function k ini.p h) (algorithm μ k l ini i).p

lemma p'_le {μ : ℝ} {i h : ℕ} : p' μ k l ini i h ≤ q_function k ini.p h :=
begin
  rw [p'],
  split_ifs,
  { exact min_le_left _ _ },
  exact clamp_le (q_increasing (by simp))
end

lemma le_p' {μ : ℝ} {i h : ℕ} (hh : 1 < h) : q_function k ini.p (h - 1) ≤ p' μ k l ini i h :=
begin
  rw [p', if_neg hh.ne'],
  exact le_clamp
end

lemma min_add_clamp_self {a b x y : ℝ} (h : a ≤ b) :
  (min a x - min a y) + (clamp a b x - clamp a b y) = min b x - min b y :=
by { rw [yael h, yael h], ring }

/-- Δ' in section 8 -/
noncomputable def Δ' (μ : ℝ) (k l : ℕ) (ini : book_config χ) (i : ℕ) (h : ℕ) : ℝ :=
p' μ k l ini (i + 1) h - p' μ k l ini i h

/-- Δ in section 8 -/
noncomputable def Δ (μ : ℝ) (k l : ℕ) (ini : book_config χ) (i : ℕ) : ℝ :=
(algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p

local notation `X_` := λ Ᾰ, by my_X
local notation `p_` := λ Ᾰ, by my_p
local notation `h_` := λ Ᾰ, by my_h
local notation `ℛ` := by my_R
local notation `ℬ` := by my_B
local notation `𝒮` := by my_S
local notation `𝒟` := by my_D
local notation `t` := by my_t
local notation `s` := by my_s
local notation `ε` := by my_ε

lemma prop33_aux {μ : ℝ} {z : ℕ} (h : 1 ≤ z) :
  ∑ h in Icc 1 z, Δ' μ k l ini i h =
    min (q_function k ini.p z) (algorithm μ k l ini (i + 1)).p -
    min (q_function k ini.p z) (algorithm μ k l ini i).p :=
begin
  cases z,
  { simpa using h },
  clear h,
  induction z with z ih,
  { simp [Δ', p'] },
  rw [nat.Icc_succ_left, ←nat.Ico_succ_succ, nat.Ico_succ_right_eq_insert_Ico, sum_insert,
    nat.Ico_succ_right, ih, Δ', p', p', if_neg, if_neg, add_comm, nat.succ_sub_succ_eq_sub,
    nat.sub_zero, min_add_clamp_self],
  { exact q_increasing (nat.lt_succ_self _).le },
  { simp },
  { simp },
  { simp },
  { exact nat.succ_le_succ (by simp) },
end

/-- The maximum value of the height, for the sums in section 8 -/
noncomputable def max_height (k : ℕ) : ℕ :=
⌊2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k⌋₊ + 1

open filter

lemma max_height_large : ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → 1 < max_height k :=
begin
  filter_upwards [top_adjuster height_upper_bound] with l hl k hlk,
  rw [max_height, lt_add_iff_pos_left, nat.floor_pos],
  refine (hl k hlk 0 le_rfl 1 le_rfl).trans' _,
  rw nat.one_le_cast,
  exact one_le_height
end

lemma p_le_q' {k h : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) :
  height k p₀ p < h → p ≤ q_function k p₀ (h - 1) :=
begin
  intros hh,
  refine (q_increasing (nat.le_pred_of_lt hh)).trans' _,
  exact height_spec hk
end

lemma p_le_q :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ) (h : ℕ) (i : ℕ), max_height k ≤ h →
  (algorithm μ k l ini i).p ≤ q_function k ini.p (h - 1) :=
begin
  filter_upwards [top_adjuster height_upper_bound, top_adjuster (eventually_gt_at_top 0)]
    with l hl' hk k hlk μ n χ ini i h hh,
  refine p_le_q' (hk k hlk).ne' (hh.trans_lt' _),
  rw [←@nat.cast_lt ℝ, max_height, nat.cast_add_one],
  exact (hl' _ hlk _ col_density_nonneg _ col_density_le_one).trans_lt (nat.lt_floor_add_one _),
  -- filter_upwards [top_adjuster (one_lt_q_function), max_height_large,
  --   top_adjuster (eventually_gt_at_top 0)] with l hl hl' hk
  --   k hlk n χ ini h hh i,
  -- refine col_density_le_one.trans _,
  -- refine (hl k hlk ini.p col_density_nonneg).trans (q_increasing _),
  -- rwa le_tsub_iff_right,
  -- exact hh.trans' (hl' k hlk).le
end

lemma p'_eq_of_ge' {μ : ℝ} {k h : ℕ} (hk : k ≠ 0) :
  height k ini.p (algorithm μ k l ini i).p < h →
    p' μ k l ini i h = q_function k ini.p (h - 1) :=
begin
  intros hh,
  have h₁ : q_function k ini.p (h - 1) ≤ q_function k ini.p h := q_increasing (nat.sub_le _ _),
  rw [p', clamp_eq h₁, max_eq_left, min_eq_right h₁, if_neg (one_le_height.trans_lt hh).ne'],
  exact p_le_q' hk hh,
end

lemma p'_eq_of_ge :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ) (h i : ℕ), max_height k ≤ h →
  p' μ k l ini i h = q_function k ini.p (h - 1) :=
begin
  filter_upwards [p_le_q, max_height_large] with l hl hl'
    k hlk μ n χ ini h i hh,
  have h₁ : q_function k ini.p (h - 1) ≤ q_function k ini.p h := q_increasing (nat.sub_le _ _),
  rw [p', clamp_eq h₁, max_eq_left (hl k hlk μ n χ ini _ i hh), min_eq_right h₁, if_neg],
  exact ((hl' k hlk).trans_le hh).ne',
end

lemma Δ'_eq_of_ge :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ) (h i : ℕ), max_height k ≤ h →
  Δ' μ k l ini i h = 0 :=
begin
  filter_upwards [p'_eq_of_ge] with l hl k hlk μ n χ ini h i hh,
  rw [Δ', hl _ hlk _ _ _ _ _ _ hh, hl _ hlk _ _ _ _ _ _ hh, sub_self],
end

lemma prop_33 :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ),
  ∀ i, ∑ h in Ico 1 (max_height k), Δ' μ k l ini i h = Δ μ k l ini i :=
begin
  filter_upwards [p_le_q, max_height_large] with l hl hl'
    k hlk μ n χ ini i,
  rw [max_height, nat.Ico_succ_right],
  rw [prop33_aux, Δ, min_eq_right, min_eq_right],
  { refine (hl k hlk _ _ _ _ _ _ le_rfl).trans _,
    exact q_increasing le_rfl },
  { refine (hl k hlk _ _ _ _ _ _ le_rfl).trans _,
    exact q_increasing le_rfl },
  specialize hl' k hlk,
  rw [max_height, lt_add_iff_pos_left] at hl',
  exact hl'
end

lemma p'_le_p'_of_p_le_p {μ : ℝ} {h i j : ℕ}
  (hp : (algorithm μ k l ini i).p ≤ (algorithm μ k l ini j).p) :
  p' μ k l ini i h ≤ p' μ k l ini j h :=
begin
  rw [p', p'],
  split_ifs,
  { exact min_le_min le_rfl hp },
  exact max_le_max le_rfl (min_le_min le_rfl hp),
end

lemma Δ'_nonneg_of_p_le_p {μ : ℝ} {h : ℕ}
  (hp : (algorithm μ k l ini i).p ≤ (algorithm μ k l ini (i + 1)).p) :
  0 ≤ Δ' μ k l ini i h :=
begin
  rw [Δ', sub_nonneg],
  exact p'_le_p'_of_p_le_p hp
end

lemma Δ'_nonpos_of_p_le_p {μ : ℝ} {h : ℕ}
  (hp : (algorithm μ k l ini (i + 1)).p ≤ (algorithm μ k l ini i).p) :
  Δ' μ k l ini i h ≤ 0 :=
begin
  rw [Δ', sub_nonpos],
  exact p'_le_p'_of_p_le_p hp
end

lemma forall_nonneg_iff_nonneg :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ),
  ∀ i, (∀ h, 1 ≤ h → 0 ≤ Δ' μ k l ini i h) ↔ 0 ≤ Δ μ k l ini i :=
begin
  filter_upwards [prop_33] with l hl k hlk μ n χ ini i,
  split,
  { intros hi,
    rw [←hl _ hlk],
    refine sum_nonneg _,
    intros j hj,
    rw [mem_Ico] at hj,
    exact hi _ hj.1 },
  intros hi j hj,
  rw [Δ, sub_nonneg] at hi,
  exact Δ'_nonneg_of_p_le_p hi
end

lemma forall_nonpos_iff_nonpos :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ),
  ∀ i, (∀ h, 1 ≤ h → Δ' μ k l ini i h ≤ 0) ↔ Δ μ k l ini i ≤ 0 :=
begin
  filter_upwards [prop_33] with l hl k hlk μ n χ ini i,
  split,
  { intros hi,
    rw [←hl _ hlk],
    refine sum_nonpos (λ j hj, _),
    rw [mem_Ico] at hj,
    exact hi _ hj.1 },
  intros hi j hj,
  rw [Δ, sub_nonpos] at hi,
  exact Δ'_nonpos_of_p_le_p hi
end

lemma prop_34 :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ),
  ∑ h in Ico 1 (max_height k), ∑ i in range (final_step μ k l ini),
    (Δ' μ k l ini i h) / α_function k h ≤ 2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k :=
begin
  filter_upwards [Δ'_eq_of_ge, top_adjuster (eventually_ge_at_top 1)] with l hl hk
    k hlk μ n χ ini,
  refine (sum_le_card_nsmul _ _ 1 _).trans _,
  { intros h hh,
    rw [←sum_div, div_le_one (α_pos _ _ (hk _ hlk))],
    simp only [Δ'],
    rw sum_range_sub (λ x, p' μ k l ini x h),
    dsimp,
    rw mem_Ico at hh,
    rw [p', p'],
    have : α_function k h = q_function k ini.p h - q_function k ini.p (h - 1),
    { rw [←nat.sub_add_cancel hh.1, α_function_eq_q_diff, nat.add_sub_cancel] },
    rw this,
    refine sub_le_sub _ _,
    { split_ifs,
      { exact min_le_left _ _ },
      exact clamp_le (q_increasing (by simp)) },
    split_ifs,
    { rw [h_1, q_function_zero, algorithm_zero, min_eq_right],
      refine (q_increasing zero_le_one).trans_eq' _,
      rw [q_function_zero] },
    exact le_clamp },
  rw [nat.card_Ico, max_height, nat.add_sub_cancel, nat.smul_one_eq_coe],
  refine nat.floor_le _,
  have : 0 ≤ log k := log_nonneg (nat.one_le_cast.2 (hk k hlk)),
  positivity
end

lemma eight_two (μ₁ p₀ : ℝ) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  (1 - k ^ (- 1 / 8 : ℝ) : ℝ) *
    ∑ i in moderate_steps μ k l ini, (1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i ≤
      ∑ h in Ico 1 (max_height k),
        ∑ i in density_steps μ k l ini, Δ' μ k l ini i h / α_function k h :=
begin
  have tt : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have hh₁ : (0 : ℝ) < 1 / 8, by norm_num,
  have hh₂ : (0 : ℝ) < 2 / 3, by norm_num,
  have hh₃ : (0 : ℝ) < 1 / 16, by norm_num,
  have hh₄ : (0 : ℝ) < 3 / 4, by norm_num,
  have := ((tendsto_rpow_neg_at_top hh₁).comp tt).eventually (eventually_le_nhds hh₂),
  have h' := ((tendsto_rpow_neg_at_top hh₃).comp tt).eventually (eventually_le_nhds hh₄),
  -- have := ((tendsto_rpow_at_top hh₁).comp tt).eventually
  --   (eventually_le_floor (2 / 3) (by norm_num1)),
  filter_upwards [five_three_left μ₁ p₀ hμ₁ hp₀, five_two μ₁ p₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0), prop_33, top_adjuster this,
    top_adjuster h'] with l h₅₃ hl₅₂ hk h33 h₁₈ h₃₄
    k hlk μ hμu n χ ini hini,
  specialize h₅₃ k hlk μ hμu n χ ini hini,
  suffices : ∀ i ∈ moderate_steps μ k l ini,
    (1 - k ^ (- 1 / 8 : ℝ) : ℝ) * (1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i ≤
      ∑ h in Ico 1 (max_height k), Δ' μ k l ini i h / α_function k h,
  { simp only [mul_sum, mul_div_assoc'],
    refine (sum_le_sum this).trans _,
    rw sum_comm,
    refine sum_le_sum (λ i hi, sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _),
    intros j hj hj',
    exact div_nonneg (Δ'_nonneg_of_p_le_p (h₅₃ j hj)) (α_nonneg _ _) },
  intros i hi,
  rw [moderate_steps, mem_filter] at hi,
  have : ∀ h ∈ Ico 1 (max_height k),
    Δ' μ k l ini i h / α_function k (height k ini.p (algorithm μ k l ini (i + 1)).p) ≤
    Δ' μ k l ini i h / α_function k h,
  { intros h hh,
    cases le_or_lt h (height k ini.p (algorithm μ k l ini (i + 1)).p) with hp hp,
    { exact div_le_div_of_le_left (Δ'_nonneg_of_p_le_p (h₅₃ _ hi.1)) (α_pos _ _ (hk k hlk))
        (α_increasing hp) },
    suffices : Δ' μ k l ini i h = 0,
    { simp [this] },
    rw [Δ', p'_eq_of_ge' (hk k hlk).ne' hp, p'_eq_of_ge' (hk k hlk).ne' _, sub_self],
    refine hp.trans_le' _,
    exact height_mono (hk k hlk).ne' (h₅₃ i hi.1) },
  refine (sum_le_sum this).trans' _,
  clear this,
  rw [←sum_div, h33 _ hlk],
  clear h33,
  obtain ⟨hβ, hβ'⟩ := hl₅₂ k hlk μ hμu n χ ini hini i hi.1,
  clear hl₅₂,
  rw [mul_div_assoc, le_div_iff (α_pos _ _ (hk k hlk))],
  refine hβ'.trans' _,
  rw [mul_right_comm, mul_right_comm _ (_ / _)],
  refine mul_le_mul_of_nonneg_right _ _,
  swap,
  { refine div_nonneg _ hβ.le,
    rw sub_nonneg,
    exact blue_X_ratio_le_one },
  dsimp at hi,
  have : α_function k (height k ini.p (algorithm μ k l ini (i + 1)).p) =
    (1 + ε) ^
      (height k ini.p (algorithm μ k l ini (i + 1)).p - height k ini.p (algorithm μ k l ini i).p) *
      α_function k (height k ini.p (algorithm μ k l ini i).p),
  { rw [α_function, α_function, mul_div_assoc', mul_left_comm, ←pow_add, tsub_add_tsub_cancel],
    { exact height_mono (hk k hlk).ne' (h₅₃ _ hi.1) },
    exact one_le_height },
  rw [this, ←mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (α_nonneg _ _),
  rw [←rpow_nat_cast, nat.cast_sub],
  swap,
  exact (height_mono (hk k hlk).ne' (h₅₃ _ hi.1)),
  have hk₈ : (0 : ℝ) ≤ 1 - k ^ (-1 / 8 : ℝ),
  { rw sub_nonneg,
    refine rpow_le_one_of_one_le_of_nonpos _ _,
    { rw [nat.one_le_cast, nat.succ_le_iff],
      exact hk k hlk },
    norm_num1 },
  refine (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le _ hi.2) _).trans _,
  { simp only [le_add_iff_nonneg_right], positivity },
  { exact hk₈ },
  have : (1 : ℝ) - ε = (1 - k ^ (- 1 / 8 : ℝ)) * (1 + k ^ (- 1 / 8 : ℝ)),
  { rw [one_sub_mul, mul_one_add, ←sub_sub, add_sub_cancel, ←rpow_add],
    { norm_num },
    rw [nat.cast_pos],
    exact hk k hlk },
  rw this,
  refine mul_le_mul_of_nonneg_left _ _,
  swap,
  { exact hk₈ },
  rw add_comm,
  refine (rpow_le_rpow _ (add_one_le_exp ε) _).trans _,
  { exact add_nonneg (by positivity) zero_le_one },
  { positivity },
  rw [←exp_one_rpow, ←rpow_mul (exp_pos _).le, exp_one_rpow, ←rpow_add],
  swap,
  { rw nat.cast_pos,
    exact hk k hlk },
  norm_num1,
  rw [←neg_div, ←neg_div, ←le_log_iff_exp_le],
  swap,
  { exact add_pos_of_pos_of_nonneg zero_lt_one (by positivity) },
  have := quick_calculation,
  have : (k : ℝ) ^ (- 1 / 8 : ℝ) ≤ 2 / 3,
  { rw neg_div, exact h₁₈ k hlk },
  refine (log_inequality (by positivity) this).trans' _,
  refine (mul_le_mul_of_nonneg_left quick_calculation (by positivity)).trans' _,
  have : (k : ℝ) ^ (- 3 / 16 : ℝ) = k ^ (- 1 / 8 : ℝ) * k ^ (- (1 / 16) : ℝ),
  { rw [←rpow_add],
    { norm_num },
    rw nat.cast_pos,
    exact hk k hlk },
  rw this,
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  exact h₃₄ k hlk
end

lemma eight_three :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ),
  - (1 + ε : ℝ) ^ 2 * (red_steps μ k l ini).card ≤
      ∑ h in Ico 1 (max_height k), ∑ i in ℛ, Δ' μ k l ini i h / α_function k h :=
begin
  filter_upwards [forall_nonneg_iff_nonneg, forall_nonpos_iff_nonpos, six_five_red,
    top_adjuster (eventually_gt_at_top 0), prop_33] with
    l hl₁ hl₂ hl₃ hk h₃₃
    k hlk μ n χ ini,
  specialize hl₁ k hlk μ n χ ini,
  specialize hl₂ k hlk μ n χ ini,
  specialize hl₃ k hlk μ n χ ini,
  rw [mul_comm, ←nsmul_eq_mul, sum_comm],
  refine card_nsmul_le_sum _ _ _ _,
  intros i hi,
  cases le_or_lt 0 (Δ μ k l ini i) with hΔ hΔ,
  { refine (sum_nonneg _).trans' (neg_nonpos_of_nonneg (by positivity)),
    intros j hj,
    rw mem_Ico at hj,
    exact div_nonneg ((hl₁ i).2 hΔ j hj.1) (α_nonneg _ _) },
  specialize hl₃ i hi,
  have : ∀ h, 1 ≤ h → h < height k ini.p (algorithm μ k l ini i).p - 2 → Δ' μ k l ini i h = 0,
  { intros h hh₁ hh₂,
    have := hh₂.trans_le hl₃,
    rw [Δ'],
    have h₁ : p' μ k l ini (i + 1) h = q_function k ini.p h,
    { have h₁ : q_function k ini.p h ≤ (algorithm μ k l ini (i + 1)).p,
      { refine (q_increasing (nat.le_pred_of_lt (hh₂.trans_le hl₃))).trans (q_height_lt_p _).le,
        exact hh₁.trans_lt this },
      rw [p', clamp, min_eq_left h₁, max_eq_right (q_increasing (nat.sub_le _ _))],
      simp },
    have h₂ : p' μ k l ini i h = q_function k ini.p h,
    { have h₂ : q_function k ini.p h ≤ (algorithm μ k l ini i).p,
      { exact (q_increasing (nat.le_pred_of_lt (hh₂.trans_le (nat.sub_le _ _)))).trans
          (q_height_lt_p (hh₁.trans_lt (hh₂.trans_le (nat.sub_le _ _)))).le },
      rw [p', clamp, min_eq_left h₂, max_eq_right (q_increasing (nat.sub_le _ _))],
      simp },
    rw [h₁, h₂, sub_self] },
  have : ∀ h ∈ Ico 1 (max_height k),
    (1 + ε : ℝ) ^ 2 * Δ' μ k l ini i h / α_function k (height k ini.p (algorithm μ k l ini i).p) ≤
    Δ' μ k l ini i h / α_function k h,
  { intros h hh,
    rw [mem_Ico] at hh,
    cases lt_or_le h (height k ini.p (algorithm μ k l ini i).p - 2) with hp hp,
    { rw [this h hh.1 hp, mul_zero, zero_div, zero_div] },
    rw [div_le_div_iff (α_pos _ _ (hk k hlk)) (α_pos _ _ (hk k hlk)), mul_comm (_ ^ 2 : ℝ),
      mul_assoc],
    refine mul_le_mul_of_nonpos_left _ ((hl₂ _).2 hΔ.le _ hh.1),
    rw tsub_le_iff_right at hp,
    refine (α_increasing hp).trans_eq _,
    rw [α_function, α_function, mul_div_assoc', mul_left_comm, ←pow_add],
    congr' 3,
    rw [add_comm 2, tsub_add_eq_add_tsub hh.1] },
  refine (sum_le_sum this).trans' _,
  rw [←sum_div, ←mul_sum, h₃₃ k hlk, le_div_iff (α_pos _ _ (hk k hlk)), neg_mul, ←mul_neg],
  refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
  rw [Δ, neg_le_sub_iff_le_add, ←sub_le_iff_le_add],
  exact six_four_red hi,
end

lemma eight_four_first_step (μ : ℝ) :
  ∑ h in Ico 1 (max_height k), ∑ i in big_blue_steps μ k l ini,
    (Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h) / α_function k h ≤
  ∑ h in Ico 1 (max_height k), ∑ i in degree_steps μ k l ini ∪ big_blue_steps μ k l ini,
    Δ' μ k l ini i h / α_function k h :=
begin
  refine sum_le_sum _,
  intros h hh,
  rw sum_union ((degree_steps_disjoint_big_blue_steps_union_red_or_density_steps).mono_right _),
  swap,
  { exact subset_union_left _ _ },
  simp only [add_div, sum_add_distrib, add_le_add_iff_right],
  have : big_blue_steps μ k l ini ⊆ (degree_steps μ k l ini).map ⟨_, add_left_injective 1⟩,
  { intros i hi,
    have := big_blue_steps_sub_one_mem_degree hi,
    rw [finset.mem_map, function.embedding.coe_fn_mk],
    exact ⟨i - 1, this.2, nat.sub_add_cancel this.1⟩ },
  refine (sum_le_sum_of_subset_of_nonneg this _).trans _,
  { simp only [finset.mem_map, function.embedding.coe_fn_mk, forall_exists_index,
      forall_apply_eq_imp_iff₂, add_tsub_cancel_right],
    intros i hi hi',
    refine div_nonneg _ (α_nonneg _ _),
    refine Δ'_nonneg_of_p_le_p _,
    exact six_four_degree hi },
  rw [sum_map],
  simp only [function.embedding.coe_fn_mk, add_tsub_cancel_right],
end

lemma eq_39_end :
  ∀ᶠ k : ℕ in at_top, (1 + (k : ℝ) ^ (-1 / 4 : ℝ)) ^ (2 * (k : ℝ) ^ (1 / 8 : ℝ)) ≤ 2 :=
begin
  have h₈ : (0 : ℝ) < 1 / 8 := by norm_num1,
  have h₂ : 0 < log 2 / 2 := div_pos (log_pos (by norm_num1)) (by norm_num1),
  have := (tendsto_rpow_neg_at_top h₈).eventually (eventually_le_nhds h₂),
  have := tendsto_coe_nat_at_top_at_top.eventually this,
  filter_upwards [this] with k hk,
  rw [add_comm],
  refine (rpow_le_rpow _ (add_one_le_exp _) (by positivity)).trans _,
  { positivity },
  rw [←exp_one_rpow, ←rpow_mul (exp_pos _).le, exp_one_rpow, ←le_log_iff_exp_le two_pos,
    mul_left_comm, ←rpow_add' (nat.cast_nonneg _), ←le_div_iff' (zero_lt_two' ℝ)],
  swap, { norm_num1 },
  norm_num1,
  exact hk
end

lemma eq_39 (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ),
  ∀ i ∈ ℬ, Δ μ k l ini (i - 1) + Δ μ k l ini i < 0 →
  (∀ h, Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h ≤ 0) →
  (-2 : ℝ) * k ^ (1 / 8 : ℝ) ≤
    ∑ h in Ico 1 (max_height k), (Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h) / α_function k h :=
begin
  filter_upwards [six_five_blue μ₀ hμ₀, top_adjuster (eventually_gt_at_top 0),
    prop_33, top_adjuster eq_39_end] with l h₆₅ hk h₃₃ hl
    k hlk μ hμl n χ hχ ini i hi hh' hh,
  obtain ⟨hi₁, hi₂⟩ := big_blue_steps_sub_one_mem_degree hi,
  specialize h₆₅ k hlk μ hμl n χ ini i hi,
  specialize h₃₃ k hlk μ n χ ini,
  have : ∀ h : ℕ, 1 ≤ h →
    (h : ℝ) < height k ini.p (algorithm μ k l ini (i - 1)).p - 2 * k ^ (1 / 8 : ℝ) →
    Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h = 0,
  { intros h hh₁ hh₂,
    have := hh₂.trans_le h₆₅,
    rw nat.cast_lt at this,
    rw [Δ', Δ', nat.sub_add_cancel hi₁, sub_add_sub_cancel'],
    have h₁ : p' μ k l ini (i + 1) h = q_function k ini.p h,
    { have h₁ : q_function k ini.p h ≤ (algorithm μ k l ini (i + 1)).p,
      { refine (q_increasing (nat.le_pred_of_lt this)).trans (q_height_lt_p _).le,
        exact hh₁.trans_lt this },
      rw [p', clamp, min_eq_left h₁, max_eq_right (q_increasing (nat.sub_le _ _))],
      simp },
    have h₂ : p' μ k l ini (i - 1) h = q_function k ini.p h,
    { have h₀ : h < height k ini.p (algorithm μ k l ini (i - 1)).p,
      { rw ←@nat.cast_lt ℝ,
        refine hh₂.trans_le _,
        simp only [one_div, sub_le_self_iff, zero_le_mul_left, zero_lt_bit0, zero_lt_one],
        positivity },
      have h₂ : q_function k ini.p h ≤ (algorithm μ k l ini (i - 1)).p,
      { exact (q_increasing (nat.le_pred_of_lt h₀)).trans (q_height_lt_p (hh₁.trans_lt h₀)).le },
      rw [p', clamp, min_eq_left h₂, max_eq_right (q_increasing (nat.sub_le _ _))],
      simp },
    rw [h₁, h₂, sub_self] },
  have : ∀ h ∈ Ico 1 (max_height k),
    (1 + ε : ℝ) ^ (2 * k ^ (1 / 8 : ℝ) : ℝ) * (Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h) /
      α_function k (height k ini.p (algorithm μ k l ini (i - 1)).p) ≤
    (Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h) / α_function k h,
  { intros h hh',
    rw [mem_Ico] at hh',
    cases lt_or_le (h : ℝ) (height k ini.p (algorithm μ k l ini (i - 1)).p - 2 * k ^ (1 / 8 : ℝ))
      with hp hp,
    { rw [this h hh'.1 hp, mul_zero, zero_div, zero_div] },
    rw [div_le_div_iff (α_pos _ _ (hk k hlk)) (α_pos _ _ (hk k hlk)), mul_assoc, mul_left_comm],
    refine mul_le_mul_of_nonpos_left _ (hh _),
    rw [α_function, α_function, mul_div_assoc', mul_left_comm, ←rpow_add_nat, ←rpow_nat_cast],
    swap,
    { positivity },
    refine div_le_div_of_le (nat.cast_nonneg _) _,
    refine mul_le_mul_of_nonneg_left _ (by positivity),
    refine rpow_le_rpow_of_exponent_le _ _,
    { simp only [le_add_iff_nonneg_right],
      positivity },
    rwa [nat.cast_sub hh'.1, nat.cast_sub one_le_height, nat.cast_one, add_sub_assoc',
      sub_le_sub_iff_right, ←sub_le_iff_le_add'] },
  refine (sum_le_sum this).trans' _,
  rw [←sum_div, ←mul_sum, sum_add_distrib, h₃₃, h₃₃, le_div_iff (α_pos _ _ (hk k hlk)), mul_assoc,
    neg_mul, ←mul_neg],
  refine mul_le_mul_of_nonpos_of_nonneg' (hl k hlk) _ two_pos.le hh'.le,
  rw [Δ, Δ, nat.sub_add_cancel hi₁, sub_add_sub_cancel', le_sub_iff_add_le', ←sub_eq_add_neg],
  exact six_four_blue (hμ₀.trans_le hμl) hi
end

lemma eight_four (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ),
  - (2 : ℝ) * k ^ (7 / 8 : ℝ) ≤
      ∑ h in Ico 1 (max_height k), ∑ i in degree_steps μ k l ini ∪ big_blue_steps μ k l ini,
        Δ' μ k l ini i h / α_function k h :=
begin
  filter_upwards [four_three hμ₀, top_adjuster (eventually_gt_at_top 0), eq_39 μ₀ hμ₀] with
    l h₄₃ hk₀ hl
    k hlk μ hμl n χ hχ ini,
  specialize h₄₃ k hlk μ hμl n χ hχ ini,
  specialize hl k hlk μ hμl n χ hχ ini,
  refine (eight_four_first_step _).trans' _,
  rw sum_comm,
  have : - (2 : ℝ) * k ^ (7 / 8 : ℝ) ≤ (big_blue_steps μ k l ini).card • (-2 * k ^ (1 / 8 : ℝ)),
  { rw [neg_mul, neg_mul, smul_neg, neg_le_neg_iff, nsmul_eq_mul],
    have := h₄₃.trans (rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 hlk) (by norm_num1)),
    refine (mul_le_mul_of_nonneg_right this (by positivity)).trans_eq _,
    rw [mul_left_comm, ←rpow_add],
    { norm_num },
    rw nat.cast_pos,
    exact hk₀ k hlk },
  refine this.trans (card_nsmul_le_sum _ _ _ _),
  intros i hi,
  have := big_blue_steps_sub_one_mem_degree hi,
  cases le_or_lt 0 (Δ μ k l ini (i - 1) + Δ μ k l ini i) with hΔ hΔ,
  { have : ∀ h, 0 ≤ (Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h) / α_function k h,
    { intros h,
      refine div_nonneg _ (α_nonneg _ _),
      rw [Δ', Δ', nat.sub_add_cancel this.1, sub_add_sub_cancel', sub_nonneg],
      rw [Δ, Δ, nat.sub_add_cancel this.1, sub_add_sub_cancel', sub_nonneg] at hΔ,
      exact p'_le_p'_of_p_le_p hΔ },
    refine (sum_nonneg (λ i _, this i)).trans' _,
    rw [neg_mul],
    simp only [one_div, right.neg_nonpos_iff, zero_le_mul_left, zero_lt_bit0, zero_lt_one],
    positivity },
  have : ∀ h, Δ' μ k l ini (i - 1) h + Δ' μ k l ini i h ≤ 0,
  { intro h,
    rw [Δ', Δ', nat.sub_add_cancel this.1, sub_add_sub_cancel', sub_nonpos],
    rw [Δ, Δ, nat.sub_add_cancel this.1, sub_add_sub_cancel', sub_neg] at hΔ,
    exact p'_le_p'_of_p_le_p hΔ.le },
  exact hl i hi hΔ this,
end

lemma eq_41 (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  (1 - k ^ (-1 / 8 : ℝ) : ℝ) *
    ∑ i in moderate_steps μ k l ini, (1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i -
    (1 + k ^ (-1 / 4 : ℝ)) ^ 2 * (red_steps μ k l ini).card - 2 * k ^ (7 / 8 : ℝ) ≤
    2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k :=
begin
  filter_upwards [prop_34, eight_two μ₁ p₀ hμ₁ hp₀, eight_three, eight_four μ₀ hμ₀] with
    l h₃₄ h₈₂ h₈₃ h₈₄
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize h₃₄ k hlk μ n χ ini,
  specialize h₈₂ k hlk μ hμu n χ ini hini,
  specialize h₈₃ k hlk μ n χ ini,
  specialize h₈₄ k hlk μ hμl n χ hχ ini,
  refine h₃₄.trans' _,
  rw [sub_eq_add_neg, sub_eq_add_neg, ←neg_mul, ←neg_mul],
  refine (add_le_add_three h₈₂ h₈₃ h₈₄).trans _,
  rw [←sum_add_distrib, ←sum_add_distrib],
  refine sum_le_sum _,
  intros h hh,
  rw [←sum_union red_steps_disjoint_density_steps.symm, union_comm, red_steps_union_density_steps,
    union_comm, ←union_partial_steps, union_assoc, ←sum_union],
  rw disjoint_union_right,
  refine ⟨big_blue_steps_disjoint_red_or_density_steps.symm, _⟩,
  refine degree_steps_disjoint_big_blue_steps_union_red_or_density_steps.symm.mono_left _,
  exact subset_union_right _ _
end

-- k ≥ 1.6
lemma polynomial_ineq_aux : ∀ᶠ k : ℝ in at_top,
  2 * k ^ 4 + 1 + k ^ 6 + 2 * k ^ 5 ≤ 2 * k ^ 7 :=
begin
  filter_upwards [eventually_ge_at_top (1.6 : ℝ)] with k hk,
  have h₄ : 2 * k ^ 4 ≤ 2 * (5 / 8) ^ 3 * k ^ 7,
  { rw mul_assoc,
    refine mul_le_mul_of_nonneg_left _ (by norm_num1),
    rw [←div_le_iff', div_pow, div_div_eq_mul_div, mul_div_assoc, ←div_pow,
      (show 7 = 4 + 3, by norm_num1), pow_add],
    { refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (by norm_num1) hk _) _,
      exact pow_nonneg (by positivity) _ },
    positivity },
  have h₆ : k ^ 6 ≤ (5 / 8) * k ^ 7,
  { rw [←div_le_iff', div_div_eq_mul_div, mul_div_assoc, pow_succ' _ 6],
    { refine mul_le_mul_of_nonneg_left hk _,
      exact pow_nonneg (by positivity) _ },
    positivity },
  have h₅ : 2 * k ^ 5 ≤ 2 * (5 / 8) ^ 2 * k ^ 7,
  { rw mul_assoc,
    refine mul_le_mul_of_nonneg_left _ (by norm_num1),
    rw [←div_le_iff', div_pow, div_div_eq_mul_div, mul_div_assoc, ←div_pow,
      (show 7 = 5 + 2, by norm_num1), pow_add],
    { refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (by norm_num1) hk _) _,
      exact pow_nonneg (by positivity) _ },
    positivity },
  have h₁ : 1 ≤ (27 / 256) * k ^ 7,
  { rw [←div_le_iff', div_div_eq_mul_div, one_mul],
    { exact (pow_le_pow_of_le_left (by norm_num1) hk 7).trans' (by norm_num) },
    { norm_num1 } },
  refine (add_le_add (add_le_add (add_le_add h₄ h₁) h₆) h₅).trans_eq _,
  ring_nf,
end

-- k ≥ 1.6 ^ 16
lemma polynomial_ineq : ∀ᶠ k : ℕ in at_top,
  (0 : ℝ) < 1 - k ^ (- 1 / 8 : ℝ) →
  (1 + k ^ (-1 / 4 : ℝ) : ℝ) ^ 2 / (1 - k ^ (-1 / 8 : ℝ)) ≤ 1 + 2 * k ^ (- 1 / 16 : ℝ) :=
begin
  have h : (0 : ℝ) < 1 / 16 := by norm_num,
  have := (tendsto_rpow_at_top h).comp tendsto_coe_nat_at_top_at_top,
  have := this.eventually polynomial_ineq_aux,
  filter_upwards [this, eventually_gt_at_top 0] with k hk₂ hk₀ hk,
  have hk' : (0 : ℝ) < k,
  { rwa nat.cast_pos },
  rw [div_le_iff hk],
  rw [add_sq, mul_one_sub, one_add_mul, one_pow, ←add_sub, add_assoc, add_le_add_iff_left, mul_one,
    ←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg k), le_sub_iff_add_le, mul_assoc,
    ←add_assoc],
  refine le_of_mul_le_mul_right _ (rpow_pos_of_pos hk' (1 / 2)),
  simp only [add_mul, mul_assoc, ←rpow_add hk'],
  dsimp at hk₂,
  simp only [←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg k)] at hk₂,
  norm_num [rpow_zero],
  norm_num at hk₂,
  exact hk₂
end

-- bound is implicit because of the is_o, but should work for k >= 5/3 ^ 16
lemma log_ineq : ∀ᶠ k : ℕ in at_top,
  (0 : ℝ) < 1 - k ^ (- 1 / 8 : ℝ) →
  (2 / k ^ (-1 / 4 : ℝ) * log k + 2 * k ^ (7 / 8 : ℝ) : ℝ) / (1 - k ^ (-1 / 8 : ℝ)) ≤
    2 * k ^ (15 / 16 : ℝ) :=
begin
  have h₁ : (0 : ℝ) < 1 / 25 := by norm_num,
  have h₂ := (is_o_log_rpow_at_top (by norm_num : (0 : ℝ) < 11 / 16)).bound h₁,
  have tt : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [eventually_gt_at_top 1, tt.eventually h₂,
    tt.eventually_ge_at_top ((5/3) ^ 16)] with k hk₁ hk₂ hk₅ hk,
  have hk' : (0 : ℝ) < k,
  { rw nat.cast_pos,
    exact hk₁.trans_le' zero_le_one },
  have hk₁₆ : (k : ℝ) ^ (-1 / 16 : ℝ) ≤ (3 / 5 : ℝ),
  { rw [neg_div, ←div_neg, one_div, rpow_inv_le_iff_of_neg hk', rpow_neg, ←inv_rpow, inv_div],
    { refine hk₅.trans_eq' _,
      norm_num1 },
    { norm_num1 },
    { norm_num1 },
    { norm_num1 },
    { norm_num1 } },
  rw [div_le_iff hk, neg_div, rpow_neg (nat.cast_nonneg _), div_inv_eq_mul, mul_assoc, ←mul_add,
    mul_assoc, mul_one_sub],
  refine mul_le_mul_of_nonneg_left _ two_pos.le,
  rw [le_sub_iff_add_le],
  have h₁ : (k : ℝ) ^ (1 / 4 : ℝ) * log k ≤ (1 / 25) * k ^ (15 / 16 : ℝ),
  { rw [norm_of_nonneg (log_nonneg (nat.one_le_cast.2 hk₁.le)), norm_of_nonneg
      (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)] at hk₂,
    refine (mul_le_mul_of_nonneg_left hk₂ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)).trans_eq _,
    rw [mul_left_comm, ←rpow_add hk'],
    norm_num1,
    refl },
  have h₂ : (k : ℝ) ^ (7 / 8 : ℝ) ≤ (3 / 5) * k ^ (15 / 16 : ℝ),
  { refine (mul_le_mul_of_nonneg_right hk₁₆ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)).trans' _,
    rw [←rpow_add hk'],
    norm_num1,
    refl },
  have h₃ : (k : ℝ) ^ (15 / 16 : ℝ) * k ^ (- 1 / 8 : ℝ) ≤ (3 / 5) ^ 2 * k ^ (15 / 16 : ℝ),
  { rw [mul_comm],
    refine mul_le_mul_of_nonneg_right _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
    refine (pow_le_pow_of_le_left (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) hk₁₆ _).trans' _,
    rw [←rpow_nat_cast, ←rpow_mul hk'.le],
    norm_num1,
    refl },
  refine (add_le_add_three h₁ h₂ h₃).trans _,
  rw [←add_mul, ←add_mul],
  norm_num,
end

lemma eq_42 (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  ∑ i in moderate_steps μ k l ini, (1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i ≤
    (red_steps μ k l ini).card + 4 * k ^ (15 / 16 : ℝ) :=
begin
  filter_upwards [eq_41 μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 1),
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster polynomial_ineq, top_adjuster log_ineq] with l hl hk hk₀ hk₁ hk₂
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize hl k hlk μ hμl hμu n χ hχ ini hini,
  have : (0 : ℝ) < 1 - k ^ (- 1 / 8 : ℝ),
  { rw [sub_pos],
    refine rpow_lt_one_of_one_lt_of_neg _ _,
    { rw nat.one_lt_cast,
      exact hk k hlk },
    norm_num1 },
  specialize hk₁ k hlk this,
  specialize hk₂ k hlk this,
  rw [sub_le_iff_le_add, sub_le_iff_le_add, ←le_div_iff' this, add_div, ←div_mul_eq_mul_div] at hl,
  refine hl.trans _,
  refine (add_le_add hk₂ (mul_le_mul_of_nonneg_right hk₁ (nat.cast_nonneg _))).trans _,
  rw [add_comm, one_add_mul, add_assoc, add_le_add_iff_left, ←le_sub_iff_add_le, ←sub_mul],
  refine (mul_le_mul_of_nonneg_left (nat.cast_le.2 (four_four_red μ (hk₀ _ hlk).ne'
    (hk₀ _ le_rfl).ne' hχ ini)) (by positivity)).trans _,
  rw [mul_assoc, ←rpow_add_one],
  { norm_num },
  rw nat.cast_ne_zero,
  exact (hk₀ _ hlk).ne'
end

lemma one_div_sq_le_beta (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  (1 : ℝ) / k ^ 2 ≤ beta μ k l ini :=
begin
  filter_upwards [five_three_right μ₁ p₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0),
    eventually_ge_at_top (⌈sqrt (1 / μ₀)⌉₊),
    blue_X_ratio_pos μ₁ p₀ hμ₁ hp₀] with
    l hβ hl hlμ hβ₀
    k hlk μ hμl hμu n χ ini hini,
  specialize hβ k hlk μ hμu n χ ini hini,
  specialize hβ₀ k hlk μ hμu n χ ini hini,
  specialize hl k hlk,
  rw beta,
  split_ifs,
  { refine hμl.trans' _,
    rw [one_div_le, ←sqrt_le_left, ←nat.ceil_le],
    { exact hlμ.trans hlk },
    { exact nat.cast_nonneg _ },
    { positivity },
    { exact hμ₀ } },
  have : (moderate_steps μ k l ini).nonempty,
  { rwa nonempty_iff_ne_empty },
  rw [←div_eq_mul_inv, div_le_div_iff, one_mul],
  rotate,
  { positivity },
  { refine sum_pos _ this,
    intros i hi,
    rw one_div_pos,
    exact hβ₀ i (filter_subset _ _ hi) },
  rw ←nsmul_eq_mul,
  refine sum_le_card_nsmul _ _ _ _,
  intros i hi,
  rw [one_div_le],
  { exact hβ i (filter_subset _ _ hi) },
  { exact hβ₀ i (filter_subset _ _ hi) },
  { positivity }
end

lemma beta_pos (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  0 < beta μ k l ini :=
begin
  filter_upwards [one_div_sq_le_beta μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0)] with l hβ hl
    k hlk μ hμl hμu n χ ini hini,
  specialize hβ k hlk μ hμl hμu n χ ini hini,
  refine hβ.trans_lt' _,
  specialize hl k hlk,
  positivity
end

lemma eight_five (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  ((density_steps μ k l ini).card : ℝ) ≤
    beta μ k l ini / (1 - beta μ k l ini) * (red_steps μ k l ini).card +
      7 / (1 - μ₁) * k ^ (15 / 16 : ℝ) :=
begin
  filter_upwards [eq_42 μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, seven_five μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    blue_X_ratio_pos μ₁ p₀ hμ₁ hp₀, beta_le_μ μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    beta_pos μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with
    l h₄₂ h₇₅ hβ hβ' hβ₀
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize h₄₂ k hlk μ hμl hμu n χ hχ ini hini,
  specialize h₇₅ k hlk μ hμl hμu n χ hχ ini hini,
  specialize hβ k hlk μ hμu n χ ini hini,
  specialize hβ' k hlk μ hμl hμu n χ ini hini,
  specialize hβ₀ k hlk μ hμl hμu n χ ini hini,
  have : ∑ (i : ℕ) in moderate_steps μ k l ini,
    (1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i =
    ∑ i in moderate_steps μ k l ini, 1 / blue_X_ratio μ k l ini i - (moderate_steps μ k l ini).card,
  { simp only [sub_div, sum_sub_distrib, sub_right_inj],
    rw [←nat.smul_one_eq_coe, ←sum_const _],
    refine sum_congr rfl (λ i hi, _),
    rw div_self (hβ i (filter_subset _ _ hi)).ne' },
  rw [this] at h₄₂,
  have : moderate_steps μ k l ini ⊆ density_steps μ k l ini := filter_subset _ _,
  replace h₄₂ := h₄₂.trans' (sub_le_sub_left (nat.cast_le.2 (card_le_of_subset this)) _),
  have hμ' : μ < 1 := hμu.trans_lt hμ₁,
  cases (moderate_steps μ k l ini).eq_empty_or_nonempty with hS hS,
  { rw [hS, sdiff_empty] at h₇₅,
    refine h₇₅.trans (le_add_of_nonneg_of_le _ _),
    { refine mul_nonneg (div_nonneg (beta_nonneg (hμ₀.trans_le hμl)) _) (nat.cast_nonneg _),
      exact sub_nonneg_of_le (hβ'.trans hμ'.le) },
    refine mul_le_mul_of_nonneg_right _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
    refine (le_div_self (by norm_num1) (sub_pos_of_lt hμ₁) _).trans' (by norm_num1),
    rw [sub_le_self_iff],
    linarith only [hμ₀, hμl, hμu] },
  have : (4 * beta μ k l ini + 3) / (1 - beta μ k l ini) ≤ 7 / (1 - μ₁),
  { refine div_le_div (by norm_num1) _ (sub_pos_of_lt hμ₁) _,
    { linarith only [hβ', hμu, hμ₁] },
    exact sub_le_sub_left (hβ'.trans hμu) _ },
  refine (add_le_add_left (mul_le_mul_of_nonneg_right this (by positivity)) _).trans' _,
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div_same, le_div_iff],
  swap,
  { exact sub_pos_of_lt (hβ'.trans_lt (hμu.trans_lt hμ₁)) },
  rw [add_mul, ←add_assoc, mul_assoc, mul_left_comm, ←mul_add],
  refine (add_le_add_left h₇₅ _).trans' _,
  rw [moderate_steps, cast_card_sdiff (filter_subset _ _), ←moderate_steps, mul_one_sub,
    add_sub_assoc', add_comm, add_sub_assoc, sub_eq_add_neg, add_le_add_iff_left,
    le_sub_iff_add_le', ←sub_eq_add_neg],
  refine (mul_le_mul_of_nonneg_left h₄₂ (beta_nonneg (hμ₀.trans_le hμl))).trans' _,
  rw [mul_sub, mul_comm, sub_le_sub_iff_right, ←div_le_iff' hβ₀, div_eq_mul_one_div, beta_prop hS,
    one_div, mul_inv_cancel_left₀],
  rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
end

-- the little-o function is -7 / (1 - μ₁) * k ^ (- 1 / 32)
lemma eight_six (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (1 : ℝ)) ∧
  ∀ μ₀ p₀ : ℝ, 0 < μ₀ → 0 < p₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), p₀ ≤ ini.p →
  (k : ℝ) ^ (31 / 32 : ℝ) ≤ (density_steps μ k l ini).card →
  (1 + f k) *
    ((density_steps μ k l ini).card / ((density_steps μ k l ini).card + (red_steps μ k l ini).card))
    ≤ beta μ k l ini :=
begin
  refine ⟨λ k, (-7 / (1 - μ₁)) * k ^ (- (1 / 32) : ℝ), _, _⟩,
  { refine is_o.const_mul_left _ _,
    have : - (1 / 32 : ℝ) < 0 := by norm_num,
    refine ((is_o_rpow_rpow this).comp_tendsto tendsto_coe_nat_at_top_at_top).congr_right _,
    simp },
  intros μ₀ p₀ hμ₀ hp₀,
  filter_upwards [eight_five μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, beta_pos μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    beta_le_μ μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0)] with l hl hβ hβμ hk₀
    k hlk μ hμl hμu n χ hχ ini hini hs,
  specialize hl k hlk μ hμl hμu n χ hχ ini hini,
  specialize hβ k hlk μ hμl hμu n χ ini hini,
  specialize hβμ k hlk μ hμl hμu n χ ini hini,
  specialize hk₀ k hlk,
  have hk₀' : (0 : ℝ) < k := nat.cast_pos.2 hk₀,
  rw [div_mul_eq_mul_div, ←sub_le_iff_le_add, le_div_iff, mul_one_sub] at hl,
  swap,
  { rw sub_pos,
    exact hβμ.trans_lt (hμu.trans_lt hμ₁) },
  have h₁ : (1 + (-7 / (1 - μ₁)) * k ^ (- (1 / 32) : ℝ)) * (density_steps μ k l ini).card ≤
    ((density_steps μ k l ini).card : ℝ) - 7 / (1 - μ₁) * k ^ (15 / 16 : ℝ),
  { rw [neg_div, neg_mul, ←sub_eq_add_neg, one_sub_mul, sub_le_sub_iff_left],
    refine (mul_le_mul_of_nonneg_left hs _).trans' _,
    { refine mul_nonneg (div_nonneg (by norm_num1) (sub_nonneg_of_le hμ₁.le)) _,
      exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
    rw [mul_assoc, ←rpow_add hk₀'],
    norm_num },
  have h₂ : ((density_steps μ k l ini).card - 7 / (1 - μ₁) * k ^ (15 / 16 : ℝ) : ℝ) *
    beta μ k l ini ≤ (density_steps μ k l ini).card * beta μ k l ini,
  { refine mul_le_mul_of_nonneg_right _ (beta_nonneg (hμ₀.trans_le hμl)),
    rw sub_le_self_iff,
    refine mul_nonneg (div_nonneg (by norm_num1) (sub_nonneg_of_le hμ₁.le)) _,
    exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
  replace hl := (sub_le_sub h₁ h₂).trans hl,
  rw [sub_le_iff_le_add', mul_comm _ (beta μ k l ini), ←mul_add] at hl,
  rw mul_div_assoc',
  exact div_le_of_nonneg_of_le_mul (by positivity) (beta_nonneg (hμ₀.trans_le hμl)) hl,
end

end simple_graph
