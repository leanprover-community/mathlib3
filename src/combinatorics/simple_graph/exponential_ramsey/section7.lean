/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.simple_graph.exponential_ramsey.section6

/-!
# Section 7
-/
namespace simple_graph

open_locale big_operators exponential_ramsey

open filter finset nat real asymptotics

lemma pow_sum {α M : Type*} [comm_monoid M] {s : finset α} {f : α → ℕ} {b : M} :
  b ^ (∑ a in s, f a) = ∏ a in s, b ^ f a :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { rw [prod_empty, sum_empty, pow_zero] },
  rw [prod_cons, ←ih, sum_cons, pow_add],
end

variables {V : Type*} [decidable_eq V] [fintype V] {χ : top_edge_labelling V (fin 2)}
variables {k l : ℕ} {ini : book_config χ} {i : ℕ}

/-- delete -/
meta def my_X : tactic unit := tactic.to_expr ```((algorithm μ k l ini Ᾰ).X) >>= tactic.exact
/-- all -/
meta def my_t : tactic unit := tactic.to_expr ```((red_steps μ k l ini).card) >>= tactic.exact
/-- of -/
meta def my_s : tactic unit := tactic.to_expr ```((density_steps μ k l ini).card) >>= tactic.exact
/-- these -/
meta def my_h : tactic unit := tactic.to_expr ```(height k ini.p Ᾰ) >>= tactic.exact

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

lemma seven_two_single (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  ∀ i ∈ ℛ, 2 ^ (-2 * (1 / ((1 - μ) * k))) * (1 - μ) ≤ (X_ (i + 1)).card / (X_ i).card :=
begin
  have h34 : (0 : ℝ) < 3 / 4, { norm_num1 },
  have tt : tendsto (coe : ℕ → ℝ) _ _ := tendsto_coe_nat_at_top_at_top,
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_at_top h34)).comp tt,
  filter_upwards [top_adjuster (tt.eventually_gt_at_top 0),
    top_adjuster (tt.eventually_ge_at_top (2 * (1 / (1 - μ₁)))),
    this.eventually_ge_at_top 2] with l hk₀ hk₁ hk₂
    k hlk μ hμu n χ hχ ini i hi,
  have hi' : i < final_step μ k l ini,
  { have := red_steps_subset_red_or_density_steps hi,
    rw [red_or_density_steps, mem_filter, mem_range] at this,
    exact this.1 },
  rw [le_div_iff],
  swap,
  { rw [nat.cast_pos, card_pos],
    exact X_nonempty hi' },
  rw [red_applied hi, book_config.red_step_basic_X, card_red_neighbors_inter],
  have : (1 - μ) * (algorithm μ k l ini i).X.card - 1 ≤
    (1 - blue_X_ratio μ k l ini i) * (algorithm μ k l ini i).X.card - 1,
  { rw [sub_le_sub_iff_right],
    refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
    rw [sub_le_sub_iff_left],
    exact blue_X_ratio_le_mu (red_steps_subset_red_or_density_steps hi) },
  refine this.trans' _,
  have : (2 : ℝ) ^ (-2 * (1 / ((1 - μ) * k))) ≤ 1 - 1 / ((1 - μ) * k),
  { refine two_approx _ _,
    { rw one_div_nonneg,
      exact mul_nonneg (sub_nonneg_of_le (hμu.trans hμ₁.le)) (nat.cast_nonneg _) },
    rw [←div_div, le_div_iff', mul_div_assoc', div_le_iff, one_mul],
    { refine (hk₁ k hlk).trans' _,
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (sub_pos_of_lt hμ₁)
        (sub_le_sub_left hμu _)) zero_lt_two.le },
    { exact hk₀ k hlk },
    { exact two_pos } },
  rw [mul_assoc],
  refine (mul_le_mul_of_nonneg_right this _).trans _,
  { exact mul_nonneg (sub_nonneg_of_le (hμu.trans hμ₁.le)) (nat.cast_nonneg _) },
  rw [one_sub_mul, sub_le_sub_iff_left, mul_comm, mul_one_div, mul_div_mul_left, one_le_div,
    nat.cast_le],
  { refine (ramsey_number_lt_of_lt_final_step hi').le.trans' _,
    refine (ramsey_number.mono_two le_rfl hk₂).trans_eq' _,
    rw ramsey_number_two_right },
  { exact hk₀ k hlk },
  exact ne_of_gt (sub_pos_of_lt (hμu.trans_lt hμ₁)),
end

lemma seven_two (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  2 ^ f k * (1 - μ) ^ (red_steps μ k l ini).card ≤
    ∏ i in red_steps μ k l ini,
      ((algorithm μ k l ini (i + 1)).X).card / ((algorithm μ k l ini i).X).card :=
begin
  refine ⟨λ k, (-2 / (1 - μ₁)) * 1, _, _⟩,
  { refine is_o.const_mul_left _ _,
    suffices : (λ k : ℝ, (1 : ℝ)) =o[at_top] (λ x : ℝ, x),
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    simpa only [rpow_one] using is_o_one_rpow zero_lt_one },
  filter_upwards [seven_two_single μ₁ hμ₁,
    top_adjuster (eventually_gt_at_top 0)] with l hl hk₀
    k hlk μ hμu n χ hχ ini,
  refine (finset.prod_le_prod _ (hl k hlk μ hμu n χ hχ ini)).trans' _,
  { intros i hi,
    exact mul_nonneg (rpow_nonneg_of_nonneg (by norm_num1) _)
      (sub_nonneg_of_le (hμu.trans hμ₁.le)) },
  rw [prod_const, mul_pow],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (sub_pos_of_lt (hμu.trans_lt hμ₁)).le _),
  rw [←rpow_nat_cast, ←rpow_mul],
  swap, { norm_num1 },
  refine rpow_le_rpow_of_exponent_le (by norm_num1) _,
  rw [←one_div_mul_one_div, ←mul_assoc, mul_right_comm, mul_one_div, mul_one_div, mul_div_assoc],
  refine mul_le_mul_of_nonpos_of_nonneg _ (div_le_one_of_le _ (nat.cast_nonneg _)) _ zero_le_one,
  { rw [neg_div, neg_div, neg_le_neg_iff],
    exact div_le_div_of_le_left (by norm_num1) (sub_pos_of_lt hμ₁) (sub_le_sub_left hμu _) },
  { rw nat.cast_le,
    exact four_four_red μ hχ ini },
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_pos_of_lt (hμu.trans_lt hμ₁)).le,
end

lemma seven_three_aux_one {μ : ℝ} {m : ℕ} (hm : m ≤ final_step μ k l ini) :
  ∑ i in (ℬ ∩ range m), (book_config.get_book χ μ (algorithm μ k l ini i).X).1.card +
    (density_steps μ k l ini ∩ range m).card ≤ (algorithm μ k l ini m).B.card :=
begin
  induction m with m ih,
  { simp },
  rw [range_succ],
  rw nat.succ_le_iff at hm,
  rcases cases_of_lt_final_step hm with hir | hib | his | hid,
  { rw [inter_insert_of_not_mem, inter_insert_of_not_mem, red_applied hir,
      book_config.red_step_basic_B],
    { exact ih hm.le },
    { exact finset.disjoint_left.1 red_steps_disjoint_density_steps hir },
    refine finset.disjoint_right.1 big_blue_steps_disjoint_red_or_density_steps _,
    exact red_steps_subset_red_or_density_steps hir },
  { rw [inter_insert_of_mem hib, inter_insert_of_not_mem, big_blue_applied hib, sum_insert,
      add_assoc, book_config.big_blue_step_B, card_union_eq, add_comm, add_le_add_iff_right],
    { exact ih hm.le },
    { exact (algorithm μ k l ini m).hXB.symm.mono_right book_config.get_book_fst_subset },
    { simp },
    { intro h,
      refine finset.disjoint_right.1 big_blue_steps_disjoint_red_or_density_steps _ hib,
      exact density_steps_subset_red_or_density_steps h } },
  { rw [inter_insert_of_not_mem, inter_insert_of_mem his, card_insert_of_not_mem,
      density_applied his, book_config.density_boost_step_basic_B, card_insert_of_not_mem,
      ←add_assoc, add_le_add_iff_right],
    { exact ih hm.le },
    { refine finset.disjoint_left.1 (algorithm μ k l ini m).hXB _,
      exact book_config.get_central_vertex_mem_X _ _ _ },
    { simp },
    refine finset.disjoint_right.1 big_blue_steps_disjoint_red_or_density_steps _,
    exact density_steps_subset_red_or_density_steps his },
  { have := finset.disjoint_left.1
      degree_steps_disjoint_big_blue_steps_union_red_or_density_steps hid,
    rw [mem_union, not_or_distrib] at this,
    rw [inter_insert_of_not_mem this.1, inter_insert_of_not_mem, degree_regularisation_applied hid,
      book_config.degree_regularisation_step_B],
    { exact ih hm.le },
    intro h,
    exact this.2 (density_steps_subset_red_or_density_steps h) },
end

lemma seven_three_aux_two {μ : ℝ} :
  ∑ i in ℬ, (book_config.get_book χ μ (X_ i)).1.card + s ≤ (end_state μ k l ini).B.card :=
begin
  refine (seven_three_aux_one le_rfl).trans' _,
  rw [(inter_eq_left_iff_subset _ _).2, (inter_eq_left_iff_subset _ _).2],
  { exact density_steps_subset_red_or_density_steps.trans (filter_subset _ _) },
  { exact filter_subset _ _ },
end

lemma seven_three_aux_three {μ : ℝ}
  (hχ : ¬ (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card)) :
  ∑ i in big_blue_steps μ k l ini, (book_config.get_book χ μ (X_ i)).1.card + s < l :=
begin
  refine seven_three_aux_two.trans_lt _,
  by_contra' hl,
  refine hχ ⟨_, _, (end_state μ k l ini).blue_B, _⟩,
  simpa using hl,
end

lemma s_lt_l {μ : ℝ}
  (hχ : ¬ (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card)) :
  (density_steps μ k l ini).card < l :=
(seven_three_aux_three hχ).trans_le' le_add_self

lemma seven_three :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ μ₁ : ℝ, 0 < μ₀ → μ₁ < 1 →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  2 ^ f k * μ ^ (l - (density_steps μ k l ini).card) ≤
    ∏ i in big_blue_steps μ k l ini,
      ((algorithm μ k l ini (i + 1)).X).card / ((algorithm μ k l ini i).X).card :=
begin
  have tt : tendsto (coe : ℕ → ℝ) _ _ := tendsto_coe_nat_at_top_at_top,
  refine ⟨λ k, - k ^ (3 / 4 : ℝ), _, _⟩,
  { suffices : (λ k : ℝ, - (k ^ (3 / 4 : ℝ))) =o[at_top] (λ x : ℝ, x),
    { exact this.comp_tendsto tt },
    refine is_o.neg_left _,
    simpa only [rpow_one] using is_o_rpow_rpow (show (3 / 4 : ℝ) < 1, by norm_num) },
  intros μ₀ μ₁ hμ₀ hμ₁,
  filter_upwards [four_three hμ₀] with l hl
    k hlk μ hμl hμu n χ hχ ini,
  have : ∀ i ∈ big_blue_steps μ k l ini,
    μ ^ (book_config.get_book χ μ (algorithm μ k l ini i).X).1.card / 2 ≤
    (algorithm μ k l ini (i + 1)).X.card / (algorithm μ k l ini i).X.card,
  { intros i hi,
    rw [big_blue_applied hi, book_config.big_blue_step_X, le_div_iff, div_mul_eq_mul_div],
    { exact book_config.get_book_relative_card },
    rw [nat.cast_pos, card_pos],
    refine X_nonempty _,
    rw [big_blue_steps, mem_filter, mem_range] at hi,
    exact hi.1 },
  refine (prod_le_prod _ this).trans' _,
  { intros i hi,
    exact div_nonneg (pow_nonneg (hμ₀.le.trans hμl) _) two_pos.le },
  rw [prod_div_distrib, ←pow_sum, prod_const, div_eq_mul_inv (_ ^ _), ←rpow_nat_cast 2,
    ←rpow_neg two_pos.le, mul_comm],
  refine mul_le_mul (pow_le_pow_of_le_one (hμ₀.le.trans hμl) (hμu.trans hμ₁.le) _)
    (rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg ((hl k hlk μ hμl n χ hχ ini).trans
    (rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 hlk) (by norm_num1)))))
    (rpow_nonneg_of_nonneg two_pos.le _) (pow_nonneg (hμ₀.le.trans hμl) _),
  exact le_tsub_of_add_le_right (seven_three_aux_three hχ).le
end

lemma height_p_zero {p₀ : ℝ} : height k p₀ p₀ = 1 := height_eq_one le_rfl

/-- The set of moderate steps, S* -/
noncomputable def moderate_steps (μ) (k l) (ini : book_config χ) : finset ℕ :=
(density_steps μ k l ini).filter $
  λ i, (height k ini.p (p_ (i + 1)) : ℝ) - height k ini.p (p_ i) ≤ k ^ (1 / 16 : ℝ)

/-- ugh -/
meta def my_S_star : tactic unit := tactic.to_expr ```(moderate_steps μ k l ini) >>= tactic.exact

local notation `𝒮⁺` := by my_S_star

lemma range_filter_odd_eq_union {μ : ℝ} :
  (range (final_step μ k l ini)).filter odd =
    red_steps μ k l ini ∪ big_blue_steps μ k l ini ∪ density_steps μ k l ini :=
begin
  ext i,
  split,
  { rw [mem_filter, mem_range, and_comm, and_imp],
    exact mem_union_of_odd },
  rw [union_right_comm, red_steps_union_density_steps, red_or_density_steps, big_blue_steps,
    ←filter_or, mem_filter, ←and_or_distrib_left, mem_filter, ←nat.odd_iff_not_even, ←and_assoc],
  exact and.left
end

lemma sum_range_odd_telescope' {k : ℕ} (f : ℕ → ℝ) {c : ℝ} (hc' : ∀ i, f i - f 0 ≤ c) :
  ∑ i in (range k).filter odd, (f (i + 1) - f (i - 1)) ≤ c :=
begin
  have : (range k).filter odd = (range (k / 2)).map ⟨bit1, λ i i', nat.bit1_inj⟩,
  { ext i,
    simp only [mem_filter, mem_range, finset.mem_map, odd_iff_exists_bit1,
      function.embedding.coe_fn_mk, exists_prop],
    split,
    { rintro ⟨hi, i, rfl⟩,
      refine ⟨i, _, rfl⟩,
      rw ←bit1_lt_bit1,
      refine hi.trans_le _,
      rw [bit1, bit0_eq_two_mul],
      cases nat.even_or_odd k,
      { rw nat.two_mul_div_two_of_even h,
        simp },
      rw nat.two_mul_div_two_add_one_of_odd h },
    rintro ⟨i, hi, rfl⟩,
    refine ⟨_, i, rfl⟩,
    rw [←nat.add_one_le_iff, bit1, add_assoc, ←bit0, ←bit0_add],
    rw [←nat.add_one_le_iff, ←bit0_le_bit0] at hi,
    refine hi.trans _,
    rw bit0_eq_two_mul,
    exact nat.mul_div_le _ _ },
  rw [this, sum_map],
  simp only [function.embedding.coe_fn_mk],
  have : ∀ x, f (bit1 x + 1) - f (bit1 x - 1) = f (2 * (x + 1)) - f (2 * x),
  { intro x,
    rw [bit1, add_assoc, ←bit0, nat.add_sub_cancel, ←bit0_add, ←bit0_eq_two_mul,
      ←bit0_eq_two_mul] },
  simp only [this],
  rw sum_range_sub (λ x, f (2 * x)),
  dsimp,
  rw mul_zero,
  exact hc' _
end

lemma sum_range_odd_telescope {k : ℕ} (f : ℕ → ℝ) {c : ℝ} (hc' : ∀ i, f i ≤ c)
  (hc : 0 ≤ f 0) :
  ∑ i in (range k).filter odd, (f (i + 1) - f (i - 1)) ≤ c :=
begin
  refine sum_range_odd_telescope' _ _,
  intros i,
  exact (sub_le_self _ hc).trans (hc' _)
end

-- a merge of eqs 25 and 26
lemma eqn_25_26 :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
  ∑ i in (range (final_step μ k l ini)).filter odd, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) ≤
    2 / ε * log k :=
begin
  filter_upwards [top_adjuster height_upper_bound] with l hl
    k hlk μ n χ ini,
  refine sum_range_odd_telescope (λ i, h_ (algorithm μ k l ini i).p) _ _,
  { intro i,
    exact hl k hlk _ col_density_nonneg _ col_density_le_one },
  exact nat.cast_nonneg _
end

lemma eqn_25_26' :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
  ∑ i in (range (final_step μ k l ini)).filter odd, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) ≤
    f k :=
begin
  refine ⟨λ k, 2 / ε * log k, _, eqn_25_26⟩,
  simp only [div_mul_eq_mul_div, mul_div_assoc, neg_div],
  refine is_o.const_mul_left _ _,
  simp only [rpow_neg (nat.cast_nonneg _), div_inv_eq_mul],
  suffices : (λ k : ℝ, log k * k ^ (1 / 4 : ℝ)) =o[at_top] (λ x : ℝ, x),
  { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
  refine ((is_o_log_rpow_at_top (show (0 : ℝ) < 3 / 4, by norm_num)).mul_is_O
    (is_O_refl _ _)).congr' (eventually_eq.rfl) _,
  filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
  rw [←rpow_add hx],
  norm_num
end

-- (28)
lemma height_diff_blue :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ : ℝ, 0 < μ₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  f k ≤ ∑ i in ℬ, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) :=
begin
  refine ⟨λ k, (-2 * k ^ (1 / 8 : ℝ)) * k ^ (3 / 4 : ℝ), _, _⟩,
  { simp only [mul_assoc],
    refine is_o.const_mul_left _ _,
    suffices : (λ k : ℝ, k ^ (1 / 8 : ℝ) * k ^ (3 / 4 : ℝ)) =o[at_top] (λ x : ℝ, x),
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    refine is_o.congr' (is_o_rpow_rpow (show (7 / 8 : ℝ) < 1, by norm_num)) _ _,
    { filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
      rw [←rpow_add hx],
      norm_num },
    simp only [rpow_one] },
  intros μ₀ hμ₀,
  filter_upwards [four_three hμ₀, six_five_blue μ₀ hμ₀] with l hl₄₃ hl₆₅
    k hlk μ hμl n χ hχ ini,
  replace hl₄₃ : ((big_blue_steps μ k l ini).card : ℝ) ≤ k ^ (3 / 4 : ℝ),
  { refine (hl₄₃ k hlk μ hμl n χ hχ ini).trans _,
    exact rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 hlk) (by norm_num1) },
  replace hl₆₅ : ∀ i ∈ ℬ, ((-2 : ℝ) * (k ^ (1 / 8 : ℝ))) ≤ h_ (p_ (i + 1)) - h_ (p_ (i - 1)),
  { intros i hi,
    rw [neg_mul, neg_le, neg_sub, sub_le_comm],
    exact hl₆₅ k hlk μ hμl n χ ini i hi },
  refine (card_nsmul_le_sum _ _ _ hl₆₅).trans' _,
  rw [nsmul_eq_mul, mul_comm],
  refine mul_le_mul_of_nonpos_right hl₄₃ _,
  rw [neg_mul, right.neg_nonpos_iff],
  positivity
end

lemma red_or_density_height_diff :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ : ℝ, 0 < μ₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  ∑ i in ℛ ∪ 𝒮, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) ≤ f k :=
begin
  obtain ⟨f₁, hf₁, h'f₁⟩ := eqn_25_26',
  obtain ⟨f₂, hf₂, h'f₂⟩ := height_diff_blue,
  refine ⟨λ k, f₁ k - f₂ k, hf₁.sub hf₂, _⟩,
  intros μ₀ hμ₀,
  filter_upwards [h'f₁, h'f₂ μ₀ hμ₀] with l h₁ h₂
    k hlk μ hμl n χ hχ ini,
  clear h'f₁ h'f₂,
  specialize h₁ k hlk μ n χ ini,
  specialize h₂ k hlk μ hμl n χ hχ ini,
  rw [range_filter_odd_eq_union, union_right_comm, red_steps_union_density_steps,
    sum_union big_blue_steps_disjoint_red_or_density_steps.symm, ←red_steps_union_density_steps,
    ←le_sub_iff_add_le] at h₁,
  exact h₁.trans (sub_le_sub_left h₂ _),
end

lemma red_height_diff :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ : ℝ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  (-2 : ℝ) * k ≤ ∑ i in ℛ, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) :=
begin
  filter_upwards [top_adjuster (eventually_gt_at_top 0),
    six_five_red, six_five_degree] with l hl₀ hk hk'
    k hlk μ n χ hχ ini,
  have := four_four_red μ hχ ini,
  rw ←@nat.cast_le ℝ at this,
  refine (mul_le_mul_of_nonpos_left this (by norm_num1)).trans _,
  rw [mul_comm, ←nsmul_eq_mul],
  refine card_nsmul_le_sum _ _ _ _,
  intros i hi,
  obtain ⟨hi', hid⟩ := red_steps_sub_one_mem_degree hi,
  rw [le_sub_iff_add_le', ←sub_eq_add_neg, ←nat.cast_two],
  refine nat.cast_sub_le.trans _,
  rw nat.cast_le,
  refine (hk k hlk μ n χ ini i hi).trans' _,
  refine nat.sub_le_sub_right _ _,
  refine (hk' k hlk μ n χ ini (i - 1) hid).trans_eq _,
  rw nat.sub_add_cancel hi'
end

lemma density_height_diff (μ₁ p₀ : ℝ) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ((𝒮 \ 𝒮⁺).card : ℝ) * k ^ (1 / 16 : ℝ) ≤
    ∑ i in 𝒮, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) :=
begin
  filter_upwards [six_five_density μ₁ p₀ hμ₁ hp₀, six_five_degree] with l hl hl'
    k hlk μ hμu n χ hχ ini hini,
  have : moderate_steps μ k l ini ⊆ density_steps μ k l ini := filter_subset _ _,
  rw [←sum_sdiff this, ←nsmul_eq_mul],
  have : (0 : ℝ) ≤ ∑ i in moderate_steps μ k l ini,
    ((height k ini.p (algorithm μ k l ini (i + 1)).p) -
     (height k ini.p (algorithm μ k l ini (i - 1)).p)),
  { refine sum_nonneg _,
    intros i hi,
    rw [sub_nonneg, nat.cast_le],
    refine (hl k hlk μ hμu n χ ini hini i (this hi)).trans' _,
    obtain ⟨hi', hid⟩ := density_steps_sub_one_mem_degree (this hi),
    refine (hl' k hlk μ n χ ini _ hid).trans _,
    rw nat.sub_add_cancel hi' },
  refine (le_add_of_nonneg_right this).trans' _,
  refine card_nsmul_le_sum _ _ _ _,
  intros x hx,
  rw [moderate_steps, ←filter_not, mem_filter, not_le] at hx,
  refine hx.2.le.trans (sub_le_sub_left _ _),
  obtain ⟨hi', hid⟩ := density_steps_sub_one_mem_degree hx.1,
  rw nat.cast_le,
  refine (hl' k hlk μ n χ ini _ hid).trans _,
  rw nat.sub_add_cancel hi'
end

lemma seven_five (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ((𝒮 \ 𝒮⁺).card : ℝ) ≤ 3 * k ^ (15 / 16 : ℝ) :=
begin
  obtain ⟨f, hf', hf⟩ := red_or_density_height_diff,
  filter_upwards [red_height_diff, density_height_diff μ₁ p₀ hμ₁ hp₀,
    top_adjuster (hf'.bound zero_lt_one), hf μ₀ hμ₀,
    top_adjuster (eventually_gt_at_top 0)] with l hr hb hf'' hrb hk'
    k hlk μ hμl hμu n χ hχ ini hini,
  clear hf hf',
  specialize hr k hlk μ n χ hχ ini,
  specialize hb k hlk μ hμu n χ hχ ini hini,
  specialize hrb k hlk μ hμl n χ hχ ini,
  specialize hf'' k hlk,
  rw [one_mul, norm_coe_nat, norm_eq_abs] at hf'',
  replace hf'' := le_of_abs_le hf'',
  rw [sum_union red_steps_disjoint_density_steps] at hrb,
  have := ((add_le_add hr hb).trans hrb).trans hf'',
  rw [←le_sub_iff_add_le', neg_mul, sub_neg_eq_add, ←one_add_mul, add_comm, ←bit1,
    ←le_div_iff, mul_div_assoc, div_eq_mul_inv, ←rpow_neg (nat.cast_nonneg k), mul_comm (k : ℝ),
    ←rpow_add_one] at this,
  { refine this.trans_eq _,
    norm_num },
  { rw nat.cast_ne_zero,
    exact (hk' k hlk).ne' },
  refine rpow_pos_of_pos _ _,
  rw nat.cast_pos,
  exact hk' k hlk
end

/-- The parameter `β` of the algorithm. -/
noncomputable def beta (μ : ℝ) (k l : ℕ) (ini : book_config χ) : ℝ :=
if 𝒮⁺ = ∅ then μ
  else (moderate_steps μ k l ini).card * (∑ i in 𝒮⁺, 1 / blue_X_ratio μ k l ini i)⁻¹

lemma beta_prop {μ : ℝ} (hS : finset.nonempty 𝒮⁺) :
  1 / beta μ k l ini = 1 / (moderate_steps μ k l ini).card *
    ∑ i in 𝒮⁺, 1 / blue_X_ratio μ k l ini i :=
begin
  rw nonempty_iff_ne_empty at hS,
  rw [beta, if_neg hS, ←one_div_mul_one_div, one_div, one_div, inv_inv],
end

lemma beta_nonneg {μ : ℝ} (hμ₀ : 0 < μ) : 0 ≤ beta μ k l ini :=
begin
  rw beta,
  split_ifs,
  { exact hμ₀.le },
  refine mul_nonneg (nat.cast_nonneg _) (inv_nonneg_of_nonneg (sum_nonneg _)),
  intros i hi,
  rw one_div,
  refine inv_nonneg_of_nonneg _,
  exact blue_X_ratio_nonneg
end

lemma beta_le_μ (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p → beta μ k l ini ≤ μ :=
begin
  filter_upwards [blue_X_ratio_pos μ₁ p₀ hμ₁ hp₀] with l hβ k hlk μ hμl hμu n χ ini hini,
  rw beta,
  split_ifs,
  { refl },
  rw [←div_eq_mul_inv],
  refine div_le_of_nonneg_of_le_mul (sum_nonneg _) (hμ₀.le.trans hμl) _,
  { intros i hi,
    rw one_div,
    refine inv_nonneg_of_nonneg _,
    exact blue_X_ratio_nonneg },
  rw [←div_le_iff' (hμ₀.trans_le hμl), div_eq_mul_one_div, ←nsmul_eq_mul],
  refine card_nsmul_le_sum _ _ _ _,
  intros i hi,
  refine one_div_le_one_div_of_le _ _,
  { exact hβ k hlk μ hμu n χ ini hini _ (filter_subset _ _ hi) },
  refine blue_X_ratio_le_mu _,
  refine density_steps_subset_red_or_density_steps _,
  exact (filter_subset _ _ hi)
end

lemma beta_le_one (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p → beta μ k l ini < 1 :=
begin
  filter_upwards [beta_le_μ μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl k hlk μ hμl hμu n χ ini hini,
  exact (hl k hlk μ hμl hμu n χ ini hini).trans_lt (hμ₁.trans_le' hμu)
end

lemma prod_rpow {α : Type*} {y : finset α} {f : α → ℝ} {r : ℝ}
  (hf : ∀ i ∈ y, 0 ≤ f i) :
  (∏ i in y, f i) ^ r = ∏ i in y, (f i ^ r) :=
begin
  induction y using finset.cons_induction_on with a y has ih,
  { simp },
  simp only [mem_cons, forall_eq_or_imp] at hf,
  rw [prod_cons, prod_cons, mul_rpow hf.1 (prod_nonneg hf.2), ih hf.2],
end

lemma my_ineq {α : Type*} {y : finset α} (hy : y.nonempty) {f : α → ℝ}
  (hf : ∀ i ∈ y, 0 < f i) :
  ((y.card : ℝ) * (∑ i in y, 1 / f i)⁻¹) ^ y.card ≤ ∏ i in y, f i :=
begin
  have hy' : 0 < y.card, { rwa card_pos },
  simp only [one_div],
  rw [←inv_le_inv, ←prod_inv_distrib, ←rpow_nat_cast, ←inv_rpow, mul_inv, inv_inv,
    ←rpow_le_rpow_iff, ←rpow_mul, mul_inv_cancel, rpow_one, mul_sum, prod_rpow],
  refine geom_mean_le_arith_mean_weighted _ _ _ _ _ _,
  { intros, positivity },
  { simp only [sum_const, nsmul_eq_mul],
    rw mul_inv_cancel,
    positivity },
  { intros i hi,
    have := hf i hi,
    positivity },
  { intros i hi,
    have := hf i hi,
    positivity },
  { positivity },
  { refine mul_nonneg (by positivity) (sum_nonneg (λ i hi, _)),
    have := hf i hi,
    positivity },
  { refine prod_nonneg (λ i hi, _),
    have := hf i hi,
    positivity },
  { refine rpow_nonneg_of_nonneg (mul_nonneg (by positivity) (sum_nonneg (λ i hi, _))) _,
    have := hf i hi,
    positivity },
  { positivity },
  { refine mul_nonneg (by positivity) (inv_nonneg_of_nonneg (sum_nonneg (λ i hi, _))),
    have := hf i hi,
    positivity },
  { refine prod_pos hf },
  { refine pow_pos (mul_pos (by positivity) (inv_pos.2 (sum_pos (λ i hi, _) hy))) _,
    have := hf i hi,
    positivity },
end

lemma seven_four :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ μ₁ p₀ : ℝ, 0 < μ₀ → μ₁ < 1 → 0 < p₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  2 ^ f k * (beta μ k l ini) ^ s ≤
    ∏ i in 𝒮, ((algorithm μ k l ini (i + 1)).X).card / ((algorithm μ k l ini i).X).card :=
begin
  refine ⟨λ k, (log 2)⁻¹ * (log k * (-2) * (3 * k ^ (15 / 16 : ℝ))), _, _⟩,
  { refine is_o.const_mul_left _ _,
    simp only [mul_left_comm],
    refine is_o.const_mul_left _ _,
    simp only [mul_comm _ (-2 : ℝ), mul_assoc],
    refine is_o.const_mul_left _ _,
    suffices : (λ k : ℝ, log k * k ^ (15 / 16 : ℝ)) =o[at_top] (λ x : ℝ, x),
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    refine ((is_o_log_rpow_at_top (show (0 : ℝ) < 1 / 16, by norm_num)).mul_is_O
      (is_O_refl _ _)).congr' (eventually_eq.rfl) _,
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
    rw [←rpow_add hx],
    norm_num },
  intros μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
  filter_upwards [seven_five μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0),
    five_three_right μ₁ p₀ hμ₁ hp₀,
    beta_le_one μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    blue_X_ratio_pos μ₁ p₀ hμ₁ hp₀] with l hl hk₀ h₅₃ hβ hβ'
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize hl k hlk μ hμl hμu n χ hχ ini hini,
  specialize h₅₃ k hlk μ hμu n χ ini hini,
  rw [rpow_def_of_pos two_pos, mul_inv_cancel_left₀, mul_assoc, ←rpow_def_of_pos],
  rotate,
  { rw nat.cast_pos,
    exact hk₀ k hlk },
  { exact (log_pos one_lt_two).ne' },
  have : ∀ i ∈ density_steps μ k l ini,
    (((algorithm μ k l ini (i + 1)).X).card : ℝ) / ((algorithm μ k l ini i).X).card =
      blue_X_ratio μ k l ini i,
  { intros i hi,
    rw [density_applied hi, book_config.density_boost_step_basic_X, blue_X_ratio_eq] },
  rw [prod_congr rfl this, rpow_mul (nat.cast_nonneg k), rpow_neg (nat.cast_nonneg k),
    rpow_two, ←one_div],
  have : moderate_steps μ k l ini ⊆ density_steps μ k l ini := filter_subset _ _,
  rw [←prod_sdiff this],
  have : ((1 : ℝ) / k ^ 2) ^ (3 * (k : ℝ) ^ (15 / 16 : ℝ)) ≤
    ∏ i in density_steps μ k l ini \ moderate_steps μ k l ini,
      blue_X_ratio μ k l ini i,
  { refine (finset.prod_le_prod _ (λ i hi, h₅₃ i _)).trans' _,
    { intros i hi,
      rw one_div_nonneg,
      exact pow_nonneg (nat.cast_nonneg _) _ },
    { exact sdiff_subset _ _ hi },
    rw [prod_const, ←rpow_nat_cast (_ / _)],
    refine rpow_le_rpow_of_exponent_ge' _ _ (nat.cast_nonneg _) hl,
    { rw one_div_nonneg,
      exact pow_nonneg (nat.cast_nonneg _) _ },
    rw one_div,
    refine inv_le_one _,
    rw [one_le_sq_iff_one_le_abs, nat.abs_cast, nat.one_le_cast, nat.succ_le_iff],
    exact hk₀ k hlk },
  refine mul_le_mul this _ (pow_nonneg (beta_nonneg (hμ₀.trans_le hμl)) _)
    (prod_nonneg (λ i _, blue_X_ratio_nonneg)),
  have : beta μ k l ini ^ (density_steps μ k l ini).card ≤
    beta μ k l ini ^ (moderate_steps μ k l ini).card,
  { refine pow_le_pow_of_le_one (beta_nonneg (hμ₀.trans_le hμl)) _
      (card_le_of_subset (filter_subset _ _)),
    exact (hβ _ hlk μ hμl hμu n χ ini hini).le },
  refine this.trans _,
  rw [beta],
  split_ifs,
  { rw [h, prod_empty, card_empty, pow_zero] },
  refine my_ineq (nonempty_iff_ne_empty.2 h) _,
  intros i hi,
  exact hβ' k hlk μ hμu n χ ini hini i (filter_subset _ _ hi),
end

lemma seven_seven_aux {α : Type*} [fintype α] [decidable_eq α] {χ : top_edge_labelling α (fin 2)}
  {p q : ℝ} {X0 X1 Y0 Y1 : finset α} (hY : Y0 = Y1) (hp : p = col_density χ 0 X0 Y0)
  (hY' : Y0.nonempty) (h : X1 = X0.filter (λ x, (p - q) * Y0.card ≤ (red_neighbors χ x ∩ Y0).card))
  (hX1 : X1.nonempty) :
  ((X0 \ X1).card / X1.card : ℝ) * q ≤ col_density χ 0 X1 Y1 - col_density χ 0 X0 Y0 :=
begin
  cases hY,
  have hX : X1 ⊆ X0,
  { rw h,
    exact filter_subset _ _ },
  have : X0.nonempty,
  { refine nonempty.mono hX hX1 },
  cases finset.eq_empty_or_nonempty (X0 \ X1) with h_1 hX01,
  { have : X0 = X1,
    { rw sdiff_eq_empty_iff_subset at h_1,
      rw [finset.subset.antisymm_iff, and_iff_right h_1],
      exact hX },
    rw [h_1, card_empty, nat.cast_zero, zero_div, zero_mul, this, sub_self] },
  have e : red_density χ X0 Y0 * X0.card =
    red_density χ (X0 \ X1) Y0 * (X0 \ X1).card + red_density χ X1 Y0 * X1.card,
  { rw [col_density_eq_average, col_density_eq_average, col_density_eq_average,
      div_mul_cancel, div_mul_cancel, div_mul_cancel, sum_sdiff hX],
    { rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos] },
    { rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos] },
    { rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos] } },
  have : col_density χ 0 (X0 \ X1) Y0 ≤ (p - q),
  { rw [col_density_eq_average, div_le_iff', ←nsmul_eq_mul],
    rotate,
    { rwa [nat.cast_pos, card_pos] },
    refine sum_le_card_nsmul _ _ _ _,
    intro x,
    rw [h, ←filter_not, mem_filter, not_le],
    rintro ⟨_, h'⟩,
    rw div_le_iff,
    { exact h'.le },
    rwa [nat.cast_pos, card_pos] },
  have := (add_le_add_right (mul_le_mul_of_nonneg_right this (nat.cast_nonneg _)) _).trans_eq' e,
  rw [div_mul_eq_mul_div, div_le_iff, cast_card_sdiff hX, sub_mul, sub_mul, ←hp],
  swap,
  { rwa [nat.cast_pos, card_pos] },
  rw [←hp, cast_card_sdiff hX, sub_mul, mul_sub, mul_sub] at this,
  linarith only [this]
end

lemma seven_seven' {μ : ℝ} (hi : i ∈ degree_steps μ k l ini) (h : (X_ (i + 1)).nonempty)
  (h' : (algorithm μ k l ini i).Y.nonempty) :
  ((X_ i \ X_ (i + 1)).card / (X_ (i + 1)).card : ℝ) * (k ^ (1 / 8 : ℝ) * α_function k (h_ (p_ i)))
    ≤ p_ (i + 1) - p_ i :=
begin
  dsimp,
  refine seven_seven_aux _ rfl h' _ h,
  { rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_Y] },
  { rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_X],
    refl },
end

lemma one_div_k_lt_p (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i, i ≤ final_step μ k l ini → 1 / (k : ℝ) < p_ i :=
begin
  have h : tendsto (λ k : ℕ, (1 : ℝ) / k + 3 * k ^ (- 1 / 4 : ℝ)) at_top (nhds (0 + 3 * 0)),
  { refine tendsto.add _ _,
    { refine tendsto_const_div_at_top_nhds_0_nat _ },
    refine tendsto.const_mul _ _,
    rw neg_div,
    refine (tendsto_rpow_neg_at_top _).comp tendsto_coe_nat_at_top_at_top,
    norm_num },
  have : (0 : ℝ) + 3 * 0 < p₀,
  { rwa [zero_add, mul_zero] },
  filter_upwards [six_two μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (h.eventually (eventually_lt_nhds this))] with l hl hl'
    k hlk μ hμl hμu n χ hχ ini hini i hi,
  refine (hl k hlk μ hμl hμu n χ hχ ini hini i hi).trans_lt' _,
  rw lt_sub_iff_add_lt,
  refine hini.trans_lt' _,
  exact hl' k hlk
end

lemma X_Y_nonempty (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i, i ≤ final_step μ k l ini →
  (algorithm μ k l ini i).X.nonempty ∧ (algorithm μ k l ini i).Y.nonempty :=
begin
  filter_upwards [one_div_k_lt_p μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl
    k hlk μ hμl hμu n χ hχ ini hini i hi,
  have : (0 : ℝ) ≤ 1 / k,
  { simp },
  replace hl : 0 < col_density _ _ _ _ := (hl k hlk μ hμl hμu n χ hχ ini hini i hi).trans_le' this,
  split,
  { refine nonempty_of_ne_empty _,
    intro h,
    rw [h, col_density_empty_left] at hl,
    simpa using hl },
  { refine nonempty_of_ne_empty _,
    intro h,
    rw [h, col_density_empty_right] at hl,
    simpa using hl },
end

lemma seven_seven (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i, i ∈ 𝒟 →
  ((X_ i \ X_ (i + 1)).card / (X_ (i + 1)).card : ℝ) * (k ^ (1 / 8 : ℝ) * α_function k (h_ (p_ i)))
    ≤ p_ (i + 1) - p_ i  :=
begin
  filter_upwards [X_Y_nonempty μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl
    k hlk μ hμl hμu n χ hχ ini hini i hi,
  refine seven_seven' hi _ _,
  { refine (hl k hlk μ hμl hμu n χ hχ ini hini _ _).1,
    rw [nat.add_one_le_iff, ←mem_range],
    exact filter_subset _ _ hi },
  refine Y_nonempty _,
  rw [←mem_range],
  exact filter_subset _ _ hi
end

lemma seven_eight (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ 𝒟 → ((X_ i).card : ℝ) / k ^ 2 ≤ (X_ (i + 1)).card :=
begin
  have tt : tendsto (coe : ℕ → ℝ ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h : (0 : ℝ) < 1 / 8 + ((-1) / 4 + 1) := by norm_num,
  filter_upwards [seven_seven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0),
    top_adjuster (((tendsto_rpow_at_top h).comp tt).eventually_ge_at_top 2),
    X_Y_nonempty μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (((tendsto_pow_at_top two_ne_zero).comp tt).eventually_ge_at_top 2)]
    with l hl hk₀ hk₂ hX hk₂'
    k hlk μ hμl hμu n χ hχ ini hini i hi,
  specialize hk₀ k hlk,
  specialize hl k hlk μ hμl hμu n χ hχ ini hini i hi,
  specialize hX k hlk μ hμl hμu n χ hχ ini hini,
  have h' : (2 : ℝ) / k ^ 2 ≤ k ^ (1 / 8 : ℝ) *
    α_function k (height k ini.p (algorithm μ k l ini i).p),
  { refine (mul_le_mul_of_nonneg_left five_seven_left (rpow_nonneg_of_nonneg (nat.cast_nonneg _)
      _)).trans' _,
    rw [div_le_iff, mul_assoc, div_mul_eq_mul_div, sq, ←mul_assoc, mul_div_cancel, ←rpow_add_one,
      ←rpow_add' (nat.cast_nonneg _)],
    { exact hk₂ k hlk },
    { norm_num1 },
    { rwa [nat.cast_ne_zero, ←pos_iff_ne_zero] },
    { rwa [nat.cast_ne_zero, ←pos_iff_ne_zero] },
    { refine pow_pos _ _,
      rwa nat.cast_pos } },
  have : (algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p ≤ 1,
  { exact (sub_le_self _ col_density_nonneg).trans col_density_le_one },
  have := (mul_le_mul_of_nonneg_left h' (by positivity)).trans (hl.trans this),
  rw [div_mul_eq_mul_div, div_le_iff, one_mul] at this,
  swap,
  { rwa [nat.cast_pos, card_pos],
    refine (hX _ _).1,
    rw [nat.add_one_le_iff, ←mem_range],
    exact filter_subset _ _ hi },
  rw [cast_card_sdiff (X_subset _), sub_mul, sub_le_iff_le_add, mul_div_assoc', mul_comm,
    mul_div_assoc] at this,
  swap,
  { rw ←mem_range,
    exact filter_subset _ _ hi },
  refine le_of_mul_le_mul_left (this.trans _) two_pos,
  rw [two_mul, add_le_add_iff_left],
  refine mul_le_of_le_one_right (nat.cast_nonneg _) _,
  refine div_le_one_of_le _ (by positivity),
  exact hk₂' k hlk,
end

lemma log_inequality {x a : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) :
  x * (log (1 + a) / a) ≤ log (1 + x) :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp [hxa.antisymm hx] },
  set u := x * (log (1 + a) / a) with hu',
  have ha' : 0 < a := lt_of_le_of_ne' (hx.trans hxa) ha,
  have ha'' : 0 < log (1 + a),
  { refine log_pos _,
    simpa using ha' },
  have hu : 0 ≤ u :=
    mul_nonneg hx (div_nonneg ha''.le ha'.le),
  have : x * (log (1 + a) / a) ≤ log (1 + a),
  { rw [mul_div_assoc', div_le_iff' ha'],
    refine mul_le_mul_of_nonneg_right hxa ha''.le },
  rw le_log_iff_exp_le,
  swap,
  { exact add_pos_of_pos_of_nonneg one_pos hx },
  refine (general_convex_thing hu this ha''.ne').trans_eq _,
  rw [add_right_inj, exp_log, add_sub_cancel', hu', mul_div_assoc', mul_div_cancel' _ ha'.ne',
    mul_div_cancel _ ha''.ne'],
  exact add_pos_of_pos_of_nonneg one_pos ha'.le,
end

lemma first_ineq : 3 / 4 ≤ log (1 + 1 / 2) / (1 / 2) :=
begin
  rw [div_le_iff, div_mul_eq_mul_div, mul_div_assoc, mul_comm, ←log_rpow, le_log_iff_exp_le,
    ←exp_one_rpow],
  refine (rpow_le_rpow (exp_pos _).le exp_one_lt_d9.le (by norm_num1)).trans _,
  all_goals {norm_num}
end

lemma q_height_le_p {k : ℕ} {p₀ p : ℝ} (h' : p₀ ≤ p) :
  q_function k p₀ (height k p₀ p - 1) ≤ p :=
begin
  cases lt_or_eq_of_le (@one_le_height k p₀ p),
  { exact (q_height_lt_p h).le },
  rwa [h, nat.sub_self, q_function_zero],
end

lemma seven_nine_asymp : ∀ᶠ y : ℝ in nhds 0, 0 < y → (1 + y ^ 4) ^ (3 / 2 * y⁻¹) ≤ 1 + 2 * y ^ 3 :=
begin
  have := eventually_le_nhds (show (0 : ℝ) ^ 3 < 1 / 2 / 2, by norm_num),
  filter_upwards [(tendsto.pow tendsto_id 3).eventually this] with y hy' hy,
  have h₀ : 1 + y ^ 4 ≤ exp (y ^ 4),
  { rw add_comm,
    exact add_one_le_exp _ },
  have h₂ : 0 < 1 + y ^ 4,
  { positivity },
  refine (rpow_le_rpow h₂.le h₀ (by positivity)).trans _,
  have h₁ : 0 < 1 + 2 * y ^ 3,
  { positivity },
  rw [←exp_one_rpow, ←rpow_mul (exp_pos _).le, exp_one_rpow, ←le_log_iff_exp_le h₁, mul_comm,
    mul_assoc, pow_succ, inv_mul_cancel_left₀ hy.ne'],
  have : 2 * y ^ 3 ≤ 1 / 2,
  { rw ←le_div_iff',
    { exact hy' },
    { exact two_pos } },
  refine (log_inequality (by positivity) this).trans' _,
  refine (mul_le_mul_of_nonneg_left first_ineq (by positivity)).trans_eq' _,
  linarith only,
end

lemma seven_nine_inner :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ : ℝ, ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  ∀ i : ℕ, i ∈ 𝒟 →
    ini.p ≤ p_ i → (h_ (p_ (i + 1)) : ℝ) ≤ h_ (p_ i) + k ^ (1 / 16 : ℝ) →
    p_ (i + 1) - p_ i ≤ 2 * k ^ (1 / 16 : ℝ) * α_function k (h_ (p_ i)) :=
begin
  have tt : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h16 : (0 : ℝ) < 1 / 16 := by norm_num,
  filter_upwards [top_adjuster (eventually_gt_at_top 0), six_five_degree,
    top_adjuster (((tendsto_rpow_at_top h16).comp tt).eventually_ge_at_top 2),
    top_adjuster (((tendsto_rpow_neg_at_top h16).comp tt).eventually seven_nine_asymp)]
    with l hk₀ hd hk16 hε
    k hlk μ n χ hχ ini i hi hp₁ hp₂,
  specialize hk₀ k hlk,
  have h₁ : p_ (i + 1) ≤ q_function k ini.p (h_ (p_ (i + 1))) :=
    height_spec hk₀.ne',
  have h₂ : q_function k ini.p (h_ (p_ i) - 1) ≤ p_ i := q_height_le_p hp₁,
  refine (sub_le_sub h₁ h₂).trans _,
  dsimp,
  have : height k ini.p (algorithm μ k l ini i).p ≤ height k ini.p (algorithm μ k l ini (i + 1)).p,
  { exact hd k hlk μ n χ ini i hi },
  have : q_function k ini.p (height k ini.p (algorithm μ k l ini (i + 1)).p) -
    q_function k ini.p (height k ini.p (algorithm μ k l ini i).p - 1) =
    ((1 + k ^ (-1 / 4 : ℝ)) ^ (h_ (p_ (i + 1)) - h_ (p_ i) + 1) - 1) / k ^ (- 1 / 4 : ℝ) *
    α_function k (h_ (p_ i)),
  { dsimp,
    rw [α_function, div_mul_div_comm, mul_left_comm, mul_div_mul_left, q_function, q_function,
      add_sub_add_left_eq_sub, ←sub_div, sub_sub_sub_cancel_right, sub_one_mul, ←pow_add,
      add_right_comm, ←add_tsub_assoc_of_le one_le_height, tsub_add_cancel_of_le this,
      tsub_add_cancel_of_le one_le_height],
    refine (rpow_pos_of_pos _ _).ne',
    rw nat.cast_pos,
    exact hk₀ },
  rw this,
  refine mul_le_mul_of_nonneg_right _ (α_nonneg _ _),
  clear this h₁ h₂,
  dsimp,
  have : (1 + (k : ℝ) ^ (- 1 / 4 : ℝ)) ^ (h_ (p_ (i + 1)) - h_ (p_ i) + 1) ≤
    (1 + (k : ℝ) ^ (- 1 / 4 : ℝ)) ^ (3 / 2 * (k : ℝ) ^ (1 / 16 : ℝ)),
  { rw ←rpow_nat_cast,
    refine rpow_le_rpow_of_exponent_le _ _,
    { simp only [le_add_iff_nonneg_right],
      positivity },
    rw [nat.cast_add_one, nat.cast_sub this],
    rw ←sub_le_iff_le_add' at hp₂,
    refine (add_le_add_right hp₂ _).trans _,
    suffices : 2 ≤ (k : ℝ) ^ (1 / 16 : ℝ),
    { linarith },
    exact hk16 k hlk },
  refine (div_le_div_of_le (by positivity) (sub_le_sub_right this _)).trans _,
  rw [div_le_iff, sub_le_iff_le_add', mul_assoc, ←rpow_add],
  rotate,
  { positivity },
  { positivity },
  set y : ℝ := k ^ (- (1 / 16) : ℝ) with hy,
  convert_to (1 + y ^ 4) ^ (3 / 2 * y⁻¹) ≤ 1 + 2 * y ^ 3 using 3,
  { rw [hy, ←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg _)],
    norm_num },
  { rw [hy, rpow_neg (nat.cast_nonneg _), inv_inv] },
  { rw [hy, ←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg _)],
    norm_num },
  refine hε k hlk _,
  dsimp,
  positivity
end

lemma seven_nine (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ 𝒟 →
    ini.p ≤ p_ i → (h_ (p_ (i + 1)) : ℝ) ≤ h_ (p_ i) + k ^ (1 / 16 : ℝ) →
    (1 - 2 * k ^ (- 1 / 16 : ℝ) : ℝ) * (X_ i).card ≤ (X_ (i + 1)).card :=
begin
  filter_upwards [seven_nine_inner,
    seven_seven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0),
    X_Y_nonempty μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl hl' hk₀ hX
    k hlk μ hμl hμu n χ hχ ini hini i hi h₁ h₂,
  specialize hl k hlk μ n χ hχ ini i hi h₁ h₂,
  specialize hl' k hlk μ hμl hμu n χ hχ ini hini i hi,
  have hk₀' : 0 < k := hk₀ k hlk,
  have : 0 < α_function k (height k ini.p (algorithm μ k l ini i).p),
  { refine five_seven_left.trans_lt' _,
    positivity },
  dsimp at this,
  rw [←mul_assoc] at hl',
  have := le_of_mul_le_mul_right (hl'.trans hl) this,
  have hi' : i < final_step μ k l ini,
  { rw ←mem_range,
    exact filter_subset _ _ hi },
  rw [div_mul_eq_mul_div, div_le_iff, ←le_div_iff, ←div_mul_eq_mul_div,
    cast_card_sdiff (X_subset hi')] at this,
  rotate,
  { positivity },
  { rw [nat.cast_pos, card_pos],
    exact (hX k hlk μ hμl hμu n χ hχ ini hini (i + 1) hi').1 },
  have z : (2 : ℝ) * k ^ (1 / 16 : ℝ) / k ^ (1 / 8 : ℝ) * (algorithm μ k l ini (i + 1)).X.card ≤
    (2 : ℝ) * k ^ (- 1 / 16 : ℝ) * (algorithm μ k l ini i).X.card,
  { rw [mul_div_assoc, ←rpow_sub],
    swap,
    { rwa nat.cast_pos },
    norm_num1,
    refine mul_le_mul_of_nonneg_left _ (by positivity),
    rw nat.cast_le,
    exact card_le_of_subset (X_subset hi') },
  replace this := this.trans z,
  rw [sub_le_comm, ←one_sub_mul] at this,
  exact this
end

lemma seven_ten (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (((red_or_density_steps μ k l ini).filter
    (λ i, (h_ (p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) ≤ h_ (p_ i))).card : ℝ) ≤
    3 * k ^ (15 / 16 : ℝ) :=
begin
  obtain ⟨f, hf', hf⟩ := red_or_density_height_diff,
  filter_upwards [hf μ₀ hμ₀, top_adjuster (hf'.bound zero_lt_one),
    six_five_red, six_five_degree, six_five_density μ₁ p₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0)] with l hl hf'' hr hd hs hl₀
    k hlk μ hμl hμu n χ hχ ini hini,
  clear hf,
  specialize hf'' k hlk,
  specialize hr k hlk μ n χ ini,
  specialize hd k hlk μ n χ ini,
  specialize hs k hlk μ hμu n χ ini hini,
  rw [one_mul, norm_coe_nat, norm_eq_abs] at hf'',
  replace hf'' := le_of_abs_le hf'',
  replace hl := (hl k hlk μ hμl n χ hχ ini).trans hf'',
  set q : ℕ → Prop := λ i, (height k ini.p (algorithm μ k l ini (i - 1)).p : ℝ) + k ^ (1 / 16 : ℝ) ≤
    height k ini.p (algorithm μ k l ini i).p,
  change (((red_or_density_steps μ k l ini).filter q).card : ℝ) ≤ _,
  have h₁ : (-2 : ℝ) * k ≤ ∑ i in red_or_density_steps μ k l ini,
    ((height k ini.p (algorithm μ k l ini (i + 1)).p : ℝ) -
      height k ini.p (algorithm μ k l ini i).p),
  { have := four_four_red μ hχ ini,
    rw ←@nat.cast_le ℝ at this,
    refine (mul_le_mul_of_nonpos_left this (by norm_num1)).trans _,
    rw [mul_comm, ←nsmul_eq_mul, ←red_steps_union_density_steps,
      sum_union red_steps_disjoint_density_steps],
    refine (le_add_of_nonneg_right _).trans' _,
    { refine sum_nonneg _,
      intros i hi,
      rw [sub_nonneg, nat.cast_le],
      exact hs i hi },
    refine card_nsmul_le_sum _ _ _ _,
    intros i hi,
    obtain ⟨hi', hid⟩ := red_steps_sub_one_mem_degree hi,
    rw [le_sub_iff_add_le', ←sub_eq_add_neg, ←nat.cast_two],
    refine nat.cast_sub_le.trans _,
    rw nat.cast_le,
    exact hr _ hi },
  have h₂ : ((red_or_density_steps μ k l ini).filter q).card • (k : ℝ) ^ (1 / 16 : ℝ) ≤
    ∑ i in red_or_density_steps μ k l ini,
    ((height k ini.p (algorithm μ k l ini i).p : ℝ) -
      height k ini.p (algorithm μ k l ini (i - 1)).p),
  { rw [←sum_filter_add_sum_filter_not _ q],
    refine (le_add_of_nonneg_right _).trans' _,
    { refine sum_nonneg _,
      intros i hi,
      rw [sub_nonneg, nat.cast_le],
      obtain ⟨hi', hid⟩ := red_or_density_steps_sub_one_mem_degree (filter_subset _ _ hi),
      refine (hd _ hid).trans_eq _,
      rw nat.sub_add_cancel hi' },
    refine card_nsmul_le_sum _ _ _ _,
    intros i hi,
    rw [mem_filter] at hi,
    rw le_sub_iff_add_le',
    exact hi.2 },
  rw red_steps_union_density_steps at hl,
  have := add_le_add h₁ h₂,
  simp only [←sum_add_distrib, sub_add_sub_cancel] at this,
  replace this := this.trans hl,
  rw [←le_sub_iff_add_le', neg_mul, sub_neg_eq_add, ←one_add_mul, add_comm, ←bit1, nsmul_eq_mul,
    ←le_div_iff, mul_div_assoc, div_eq_mul_inv (k : ℝ), ←rpow_neg (nat.cast_nonneg k),
    mul_comm (k : ℝ), ←rpow_add_one] at this,
  refine this.trans_eq _,
  { norm_num },
  { rw nat.cast_ne_zero,
    exact (hl₀ k hlk).ne' },
  refine rpow_pos_of_pos _ _,
  rw nat.cast_pos,
  exact hl₀ k hlk
end

/-- `q*` -/
noncomputable def q_star (k : ℕ) (p₀ : ℝ) : ℝ := p₀ + k ^ (1 / 16 : ℝ) * α_function k 1
lemma q_star_eq (k : ℕ) (p₀ : ℝ) : q_star k p₀ = p₀ + k ^ (-19 / 16 : ℝ) :=
begin
  rcases k.eq_zero_or_pos with rfl | hk,
  { norm_num [q_star] },
  have hk' : 0 < (k : ℝ),
  { positivity },
  rw [q_star, add_right_inj, α_one, mul_div_assoc', ←rpow_add hk', ←rpow_sub_one hk'.ne'],
  norm_num,
end

lemma q_star_le_one : ∀ᶠ k : ℕ in at_top, ∀ inip, inip ≤ 1 → q_star k inip < 2 :=
begin
  filter_upwards [eventually_gt_at_top 1] with k hk inip hinip,
  rw [q_star_eq],
  refine (add_lt_add_of_le_of_lt hinip (rpow_lt_one_of_one_lt_of_neg (nat.one_lt_cast.2 hk)
    (by norm_num1))).trans_eq (by norm_num),
end

-- (1 + y ^ 4) ^ (3 / 2 * y⁻¹) ≤ 1 + 2 * y ^ 3


-- lemma general_convex_thing {a x : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) :
--   exp x ≤ 1 + (exp a - 1) * x / a :=

-- log_inequality

-- lemma log_inequality {x a : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) (ha : a ≠ 0) :
--   x * (log (1 + a) / a) ≤ log (1 + x) :=

lemma quick_calculation : 3 / 4 ≤ log (1 + 2 / 3) / (2 / 3) :=
begin
  rw [le_div_iff, le_log_iff_exp_le, ←exp_one_rpow],
  norm_num1,
  rw [←sqrt_eq_rpow, sqrt_le_left],
  refine exp_one_lt_d9.le.trans _,
  all_goals {norm_num1},
end

lemma height_q_star_le :
  ∀ᶠ k : ℕ in at_top, ∀ inip,
  (height k inip (q_star k inip) : ℝ) ≤ 2 * k ^ (1 / 16 : ℝ) :=
begin
  have tt : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have hh₁ : (0 : ℝ) < 1 / 16, by norm_num,
  have hh₂ : (0 : ℝ) < 1 / 4, by norm_num,
  have hh₃ : (0 : ℝ) < 2 / 3, by norm_num,
  have := (((tendsto_rpow_at_top hh₁).const_mul_at_top (zero_lt_two' ℝ)).comp tt).eventually
    (eventually_le_floor (2 / 3) (by norm_num1)),
  filter_upwards [
    ((tendsto_rpow_at_top hh₁).comp tt).eventually_ge_at_top (1 / 2 : ℝ),
    eventually_ne_at_top 0, this,
    ((tendsto_rpow_neg_at_top hh₂).comp tt).eventually (eventually_le_nhds hh₃),
    q_star_le_one] with k hk hk₀ hk₂ hk₃ hq inip,
  have hk' : (0 : ℝ) < k, by positivity,
  dsimp at hk₂,
  rw [←mul_assoc, div_mul_eq_mul_div, ←bit0_eq_two_mul] at hk₂,
  rw ←nat.le_floor_iff,
  swap,
  { positivity },
  refine height_min _ _ _,
  { exact hk₀ },
  { rw [ne.def, nat.floor_eq_zero, not_lt, ←div_le_iff' (zero_lt_two' ℝ)],
    exact hk },
  rw [q_function, q_star, add_le_add_iff_left, α_one, mul_div_assoc'],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  rw [le_sub_iff_add_le, ←rpow_nat_cast],
  refine (rpow_le_rpow_of_exponent_le _ hk₂).trans' _,
  { simp only [le_add_iff_nonneg_right],
    exact (rpow_pos_of_pos hk' _).le },
  refine (add_one_le_exp _).trans _,
  rw [mul_comm, ←exp_one_rpow, rpow_mul, exp_one_rpow, rpow_mul],
  rotate,
  { positivity },
  { exact (exp_pos _).le },
  refine rpow_le_rpow (exp_pos _).le _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  rw [←le_log_iff_exp_le, log_rpow],
  rotate,
  { positivity },
  { positivity },
  rw [←div_le_iff', div_div_eq_mul_div, mul_div_assoc],
  swap,
  { norm_num },
  have : (k : ℝ) ^ (-1 / 4 : ℝ) ≤ 2 / 3,
  { rwa [neg_div] },
  refine (log_inequality (by positivity) this).trans' (mul_le_mul_of_nonneg_left _ (by positivity)),
  exact quick_calculation
end

-- t ≤ k
-- - α_ (h(q*) + 2) * t ≥ - 2 α₁ * k
-- α_ (h(q*) + 2) * t ≤ 2 α₁ * k
-- α_ (h(q*) + 2) ≤ 2 α₁
-- (1 + ε) ^ (h(q*) + 1)  ≤ 2
-- (1 + ε) ^ (2 * ε^(-1/4) + 1) ≤ 2
-- exp (ε * (2 * ε^(-1/4) + 1)) ≤ 2


lemma min_simpler {x y z w : ℝ} (h : y - w ≤ x) (hw : 0 ≤ w) : - w ≤ min x z - min y z :=
begin
  rcases min_cases x z with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩);
  rcases min_cases y z with (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩);
  linarith,
end

lemma seven_eleven_red_termwise :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  ∀ i ∈ ℛ,
  - α_function k (height k ini.p (q_star k ini.p) + 2) ≤
    min (p_ (i + 1)) (q_star k ini.p) - min (p_ i) (q_star k ini.p) :=
begin
  filter_upwards [six_five_red,
    top_adjuster (eventually_ne_at_top 0)] with l h₁ h₀
    k hlk μ n χ hχ ini i hi,
  cases le_or_lt (height k ini.p (p_ i)) (height k ini.p (q_star k ini.p) + 2),
  { refine (min_simpler (six_four_red hi) (α_nonneg _ _)).trans' _,
    exact neg_le_neg (α_increasing h) },
  dsimp at h,
  have := h₁ k hlk μ n χ ini i hi,
  rw ←lt_tsub_iff_right at h,
  have h₁ : q_star k ini.p ≤ p_ (i + 1),
  { by_contra' h',
    exact (h.trans_le this).not_le (height_mono (h₀ k hlk) h'.le) },
  have h₂ : q_star k ini.p ≤ p_ i,
  { by_contra' h',
    exact (h.trans_le (nat.sub_le _ _)).not_le (height_mono (h₀ k hlk) h'.le) },
  rw [min_eq_right h₁, min_eq_right h₂, sub_self, right.neg_nonpos_iff],
  exact α_nonneg _ _
end

lemma seven_eleven_red :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  - 2 * α_function k 1 * k ≤
    ∑ i in ℛ, (min (p_ (i + 1)) (q_star k ini.p) - min (p_ i) (q_star k ini.p)) :=
begin
  have h : tendsto (λ k : ℝ, 2 * k ^ (-1 / 4 + 1 / 16 : ℝ) + k ^ (-1 / 4 : ℝ)) at_top
    (nhds (2 * 0 + 0)),
  { refine (tendsto.const_mul _ _).add _,
    { norm_num1,
      refine tendsto_rpow_neg_at_top _,
      norm_num },
    { norm_num1,
      refine tendsto_rpow_neg_at_top _,
      norm_num } },
  rw [mul_zero, add_zero] at h,
  filter_upwards [top_adjuster height_q_star_le,
    seven_eleven_red_termwise,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster
      ((h.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_le_nhds (log_pos one_lt_two)))]
    with l hq hr h₀ h₁
    k hlk μ n χ hχ ini,
  refine (card_nsmul_le_sum _ _ _ (hr k hlk μ n χ hχ ini)).trans' _,
  rw [nsmul_eq_mul', neg_mul, neg_mul, neg_mul, neg_le_neg_iff],
  refine mul_le_mul _ (nat.cast_le.2 (four_four_red μ hχ ini))
    (nat.cast_nonneg _) (mul_nonneg zero_lt_two.le (α_nonneg _ _)),
  rw [α_one, α_function, mul_div_assoc', mul_comm, nat.add_succ_sub_one],
  refine div_le_div_of_le (nat.cast_nonneg _) (mul_le_mul_of_nonneg_right _ (by positivity)),
  rw add_comm,
  refine (pow_le_pow_of_le_left (by positivity) (add_one_le_exp _) _).trans _,
  rw [←exp_one_rpow, ←rpow_nat_cast, ←rpow_mul (exp_pos _).le, nat.cast_add_one, exp_one_rpow,
    ←le_log_iff_exp_le zero_lt_two],
  refine (mul_le_mul_of_nonneg_left (add_le_add_right (hq _ hlk _) _) (by positivity)).trans _,
  rw [mul_add_one, mul_left_comm, ←rpow_add],
  swap,
  { exact nat.cast_pos.2 (h₀ k hlk) },
  exact h₁ k hlk
end

lemma seven_eleven_red_or_density (μ₁ p₀ : ℝ) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  - 2 * α_function k 1 * k ≤
    ∑ i in ℛ ∪ 𝒮, (min (p_ (i + 1)) (q_star k ini.p) - min (p_ i) (q_star k ini.p)) :=
begin
  filter_upwards [seven_eleven_red,
    six_four_density μ₁ p₀ hμ₁ hp₀] with l h₁ h₂
    k hlk μ hμu n χ hχ ini hini,
  rw sum_union red_steps_disjoint_density_steps,
  refine (h₁ k hlk μ n χ hχ ini).trans _,
  rw [le_add_iff_nonneg_right, sum_sub_distrib, sub_nonneg],
  refine sum_le_sum _,
  intros i hi,
  refine min_le_min _ le_rfl,
  exact h₂ k hlk μ hμu n χ ini hini i hi,
end

lemma seven_eleven_blue_termwise (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  ∀ i ∈ ℬ,
  - (k : ℝ) ^ (1 / 8 : ℝ) *
    α_function k (height k ini.p (q_star k ini.p) + ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊) ≤
    min (p_ (i + 1)) (q_star k ini.p) - min (p_ (i - 1)) (q_star k ini.p) :=
begin
  filter_upwards [six_five_blue μ₀ hμ₀,
    top_adjuster (eventually_gt_at_top 0)] with l h₁ h₀
    k hlk μ hμl n χ hχ ini i hi,
  have : (0 : ℝ) ≤ k ^ (1 / 8 : ℝ),
  { positivity },
  cases le_or_lt (height k ini.p (p_ (i - 1)))
    (height k ini.p (q_star k ini.p) + ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊),
  { refine (min_simpler (six_four_blue (hμ₀.trans_le hμl) hi) _).trans' _,
    { exact mul_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (α_nonneg _ _) },
    rw [neg_mul, neg_le_neg_iff],
    exact mul_le_mul_of_nonneg_left (α_increasing h) (by positivity) },
  dsimp at h,
  have := h₁ k hlk μ hμl n χ ini i hi,
  rw [add_comm, ←nat.floor_add_nat, nat.floor_lt, ←lt_sub_iff_add_lt'] at h,
  rotate,
  { positivity },
  { positivity },
  have h₁ : q_star k ini.p ≤ p_ (i + 1),
  { by_contra' h',
    refine (h.trans_le this).not_le _,
    rw nat.cast_le,
    exact height_mono (h₀ k hlk).ne' h'.le },
  have h₂ : q_star k ini.p ≤ p_ (i - 1),
  { by_contra' h',
    refine (h.trans_le (sub_le_self _ _)).not_le _,
    { positivity },
    rw nat.cast_le,
    exact height_mono (h₀ k hlk).ne' h'.le },
  rw [min_eq_right h₁, min_eq_right h₂, sub_self, neg_mul, right.neg_nonpos_iff],
  exact mul_nonneg (by positivity) (α_nonneg _ _),
end

lemma seven_eleven_blue (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  - α_function k 1 * k ≤
    ∑ i in ℬ, (min (p_ (i + 1)) (q_star k ini.p) - min (p_ (i - 1)) (q_star k ini.p)) :=
begin
  have h : tendsto (λ k : ℝ, (2 * k ^ (1 / 16 + -1 / 4 : ℝ) + 2 * k ^ (1 / 8 + -1 / 4 : ℝ)) -
    k ^ (-1 / 4 : ℝ)) at_top (nhds ((2 * 0 + 2 * 0) - 0)),
  { refine ((tendsto.const_mul _ _).add (tendsto.const_mul _ _)).sub _,
    { norm_num1,
      refine tendsto_rpow_neg_at_top _,
      norm_num },
    { norm_num1,
      refine tendsto_rpow_neg_at_top _,
      norm_num },
    { norm_num1,
      refine tendsto_rpow_neg_at_top _,
      norm_num } },
  rw [mul_zero, add_zero, sub_zero] at h,
  filter_upwards [top_adjuster height_q_star_le,
    seven_eleven_blue_termwise μ₀ hμ₀,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster (eventually_ge_at_top (2 ^ 8)),
    four_three hμ₀,
    top_adjuster
      ((h.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_le_nhds (log_pos one_lt_two)))
      ]
    with l hq hr h₀ hk2 hb h₁
    k hlk μ hμl n χ hχ ini,
  refine (card_nsmul_le_sum _ _ _ (hr k hlk μ hμl n χ hχ ini)).trans' _,
  rw [nsmul_eq_mul', neg_mul, neg_mul, neg_mul, neg_le_neg_iff, mul_right_comm, mul_comm _ (k : ℝ)],
  refine le_of_mul_le_mul_left _ two_pos,
  rw [←mul_assoc, mul_left_comm _ _ (α_function k 1), ←mul_assoc],
  have h' : (0 : ℝ) < k,
  { rw nat.cast_pos,
    exact h₀ k hlk },
  have : 2 * (k : ℝ) ^ (1 / 8 : ℝ) * ((big_blue_steps μ k l ini).card) ≤ k,
  { have := (hb k hlk μ hμl n χ hχ ini).trans
      (rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 hlk) (by norm_num1)),
    refine (mul_le_mul_of_nonneg_left this _).trans _,
    { positivity },
    have : (2 : ℝ) ≤ k ^ (1 / 8 : ℝ),
    { refine (rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 (hk2 k hlk)) _).trans' _,
      { norm_num1 },
      rw [nat.cast_pow, ←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg 2)],
      norm_num1 },
    rw [mul_assoc, ←rpow_add h'],
    refine (mul_le_mul_of_nonneg_right this _).trans_eq _,
    { exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
    rw [←rpow_add h'],
    norm_num },
  refine mul_le_mul this _ (α_nonneg _ _) (nat.cast_nonneg _),
  rw [α_one, α_function, mul_div_assoc', mul_comm],
  refine div_le_div_of_le _ (mul_le_mul_of_nonneg_right _ (by positivity)),
  { exact nat.cast_nonneg _ },
  rw add_comm,
  refine (pow_le_pow_of_le_left (by positivity) (add_one_le_exp _) _).trans _,
  rw [←exp_one_rpow, ←rpow_nat_cast, ←rpow_mul (exp_pos _).le, exp_one_rpow,
    ←le_log_iff_exp_le zero_lt_two, nat.cast_sub, nat.cast_add, nat.cast_one],
  swap,
  { exact one_le_height.trans (nat.le_add_right _ _) },
  refine (mul_le_mul_of_nonneg_left (sub_le_sub_right (add_le_add (hq k hlk ini.p)
    (nat.floor_le _)) _) _).trans _,
  { exact mul_nonneg two_pos.le (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
  { exact (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
  rw [mul_comm, sub_one_mul, add_mul, mul_assoc, mul_assoc, ←rpow_add h', ←rpow_add h'],
  exact h₁ k hlk
end

lemma seven_eleven_red_or_density_other :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ,
  (k : ℝ) ^ (1 / 16 : ℝ) * α_function k 1 *
    (((red_or_density_steps μ k l ini).filter
      (λ i, ((p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) * α_function k 1 ≤ p_ i ∧
            p_ (i - 1) ≤ ini.p)).card : ℝ) ≤
    ∑ i in ℛ ∪ 𝒮, (min (p_ i) (q_star k ini.p) - min (p_ (i - 1)) (q_star k ini.p)) :=
begin
  filter_upwards [] with l
    k hlk μ n χ hχ ini,
  rw red_steps_union_density_steps,
  have : (k : ℝ) ^ (1 / 16 : ℝ) * α_function k 1 * (((red_or_density_steps μ k l ini).filter
      (λ i, ((p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) * α_function k 1 ≤ p_ i ∧
            p_ (i - 1) ≤ ini.p)).card : ℝ) ≤
    ∑ i in ((red_or_density_steps μ k l ini).filter
      (λ i, ((p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) * α_function k 1 ≤ p_ i ∧
            p_ (i - 1) ≤ ini.p)),
            (min (p_ i) (q_star k ini.p) - min (p_ (i - 1)) (q_star k ini.p)),
  { rw [mul_comm, ←nsmul_eq_mul],
    refine card_nsmul_le_sum _ _ _ _,
    intros i hi,
    simp only [mem_filter] at hi,
    have : p_ (i - 1) ≤ q_star k ini.p,
    { rw [q_star_eq],
      refine hi.2.2.trans _,
      rw le_add_iff_nonneg_right,
      exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
    rw [min_eq_left this, le_sub_iff_add_le', le_min_iff, q_star, add_le_add_iff_right],
    exact hi.2 },
  refine this.trans _,
  refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _,
  intros i hi hi',
  rw sub_nonneg,
  refine min_le_min _ le_rfl,
  have := red_or_density_steps_sub_one_mem_degree hi,
  refine (six_four_degree this.2).trans _,
  rw nat.sub_add_cancel this.1
end

lemma seven_eleven (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (((red_or_density_steps μ k l ini).filter
    (λ i, ((p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) * α_function k 1 ≤ p_ i ∧
      p_ (i - 1) ≤ ini.p)).card : ℝ) ≤ 4 * k ^ (15 / 16 : ℝ) :=
begin
  filter_upwards [top_adjuster (eventually_gt_at_top 0),
    seven_eleven_blue μ₀ hμ₀,
    seven_eleven_red_or_density μ₁ p₀ hμ₁ hp₀,
    seven_eleven_red_or_density_other] with l h₀ hb hr hd
    k hlk μ hμl hμu n χ hχ ini hini,
  set X := ((red_or_density_steps μ k l ini).filter
    (λ i, ((p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) * α_function k 1 ≤ p_ i ∧
      p_ (i - 1) ≤ ini.p)),
  specialize hb k hlk μ hμl n χ hχ ini,
  specialize hr k hlk μ hμu n χ hχ ini hini,
  specialize hd k hlk μ n χ hχ ini,
  change _ * (X.card : ℝ) ≤ _ at hd,
  change (X.card : ℝ) ≤ _,
  have h₁ : α_function k 1 * ((k : ℝ) ^ (1 / 16 : ℝ) * X.card - 3 * k) ≤
    ∑ i in (range (final_step μ k l ini)).filter odd,
      (min (p_ (i + 1)) (q_star k ini.p) - min (p_ (i - 1)) (q_star k ini.p)),
  { rw [range_filter_odd_eq_union, union_right_comm, sum_union],
    swap,
    { rw red_steps_union_density_steps,
      exact big_blue_steps_disjoint_red_or_density_steps.symm },
    refine ((add_le_add_three hr hd hb).trans_eq' _).trans_eq _,
    { ring },
    rw [add_left_inj, ←sum_add_distrib],
    refine sum_congr rfl (λ x hx, _),
    rw sub_add_sub_cancel },
  have h₂ : ∑ i in (range (final_step μ k l ini)).filter odd,
      (min (p_ (i + 1)) (q_star k ini.p) - min (p_ (i - 1)) (q_star k ini.p)) ≤
      k ^ (1 / 16 : ℝ) * α_function k 1,
  { refine sum_range_odd_telescope' (λ i, min (p_ i) (q_star k ini.p)) _,
    { intros i,
      dsimp,
      rw [algorithm_zero, q_star, sub_le_iff_le_add'],
      have : min ini.p (ini.p + k ^ (1 / 16 : ℝ) * α_function k 1) = ini.p,
      { rw [min_eq_left_iff, le_add_iff_nonneg_right],
        exact mul_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (α_nonneg _ _) },
      rw this,
      exact min_le_right _ _ } },
  specialize h₀ k hlk,
  have h₃ : (k : ℝ) ^ (1 / 16 : ℝ) * α_function k 1 ≤ α_function k 1 * k ^ (1 : ℝ),
  { rw mul_comm,
    refine mul_le_mul_of_nonneg_left _ (α_nonneg _ _),
    refine rpow_le_rpow_of_exponent_le _ _,
    { rw [nat.one_le_cast, nat.succ_le_iff],
      exact h₀ },
    norm_num1 },
  rw rpow_one at h₃,
  have := le_of_mul_le_mul_left ((h₁.trans h₂).trans h₃) _,
  swap,
  { rw α_one,
    positivity },
  clear h₁ h₂ h₃ hb hr hd,
  rw [sub_le_iff_le_add', ←add_one_mul, ←le_div_iff' (rpow_pos_of_pos _ _), mul_div_assoc,
    div_eq_mul_inv (k : ℝ), ←rpow_neg (nat.cast_nonneg k), mul_comm (k : ℝ), ←rpow_add_one] at this,
  { refine this.trans_eq _,
    norm_num },
  { positivity },
  { positivity },
end

lemma seven_twelve (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (((red_or_density_steps μ k l ini).filter
    (λ i, ((X_ i).card : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) * (X_ (i - 1)).card)).card : ℝ) ≤
    7 * k ^ (15 / 16 : ℝ) :=
begin
  filter_upwards [seven_nine μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    seven_ten μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    seven_eleven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    seven_seven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0)] with l h9 h10 h11 h7 hk₀
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize h7 k hlk μ hμl hμu n χ hχ ini hini,
  specialize h9 k hlk μ hμl hμu n χ hχ ini hini,
  specialize h10 k hlk μ hμl hμu n χ hχ ini hini,
  specialize h11 k hlk μ hμl hμu n χ hχ ini hini,
  let f : ℕ → Prop := λ i, ((X_ i).card : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) * (X_ (i - 1)).card,
  change (((red_or_density_steps μ k l ini).filter f).card : ℝ) ≤ _,
  have : (4 : ℝ) * k ^ (15 / 16 : ℝ) + 3 * k ^ (15 / 16 : ℝ) = 7 * k ^ (15 / 16 : ℝ),
  { rw ←add_mul,
    norm_num },
  rw [←filter_union_filter_neg_eq (λ i, p_ (i - 1) ≤ ini.p)
    ((red_or_density_steps μ k l ini).filter f), card_union_eq (disjoint_filter_filter_neg _ _ _),
    filter_filter, filter_filter, nat.cast_add, ←this],
  have hk₀' : 0 < (k : ℝ),
  { rw nat.cast_pos,
    exact hk₀ k hlk },
  refine add_le_add (h11.trans' _) (h10.trans' _),
  { clear h9 h10 this,
    rw nat.cast_le,
    refine card_le_of_subset _,
    intros i,
    simp only [f, mem_filter, and_imp, and_true, true_and] {contextual := tt},
    intros hi₁ hi₂ hi₃,
    rw ←le_sub_iff_add_le',
    have hi₁' := red_or_density_steps_sub_one_mem_degree hi₁,
    have := h7 (i - 1) hi₁'.2,
    rw [nat.sub_add_cancel hi₁'.1] at this,
    refine this.trans' _,
    rw ←mul_assoc,
    refine mul_le_mul _ (α_increasing one_le_height) (α_nonneg _ _) (mul_nonneg (div_nonneg
      (nat.cast_nonneg _) (nat.cast_nonneg _)) (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)),
    rw [←div_le_iff (rpow_pos_of_pos hk₀' _), ←rpow_sub hk₀'],
    have hi₄ : i - 1 < final_step μ k l ini,
    { rw [degree_steps, mem_filter, mem_range] at hi₁',
      exact hi₁'.2.1 },
    have hi₅ : i < final_step μ k l ini,
    { rw [red_or_density_steps, mem_filter, mem_range] at hi₁,
      exact hi₁.1 },
    have := X_subset hi₄,
    rw nat.sub_add_cancel hi₁'.1 at this,
    rw [le_div_iff, cast_card_sdiff this],
    swap,
    { rw [nat.cast_pos, card_pos],
      exact X_nonempty hi₅ },
    norm_num1,
    rw neg_div at hi₂,
    have h₆ : ((X_ i).card : ℝ) ≤ (X_ (i - 1)).card,
    { rw nat.cast_le,
      refine card_le_of_subset this },
    have h₅ : (0 : ℝ) ≤ (X_ i).card := nat.cast_nonneg _,
    dsimp at h₆ h₅,
    have h₇ : (0 : ℝ) ≤ (k : ℝ) ^ (- (1 / 16) : ℝ),
    { exact rpow_nonneg_of_nonneg hk₀'.le _ },
    nlinarith only [hi₂, h₆, h₅, h₇] },
  { clear h10 h11,
    rw nat.cast_le,
    refine card_le_of_subset _,
    intros i,
    simp only [f, mem_filter, and_imp, and_true, true_and, not_le] {contextual := tt},
    intros hi₁ hi₂ hi₃,
    have hi₁' := red_or_density_steps_sub_one_mem_degree hi₁,
    by_contra',
    refine (h9 (i - 1) hi₁'.2 hi₃.le _).not_lt _,
    { rw nat.sub_add_cancel hi₁'.1,
      exact this.le },
    rw nat.sub_add_cancel hi₁'.1,
    exact hi₂ },
end

-- lemma num_degree_steps_le_add :
--   (degree_steps μ k l ini).card ≤ (red_steps μ k l ini).card +
--     (big_blue_steps μ k l ini).card + (density_steps μ k l ini).card + 1 :=
-- begin
--   have : big_blue_steps μ k l ini ∪ red_or_density_steps μ k l ini =
--     (range (final_step μ k l ini)).filter (λ i, ¬ even i),
--   { rw [big_blue_steps, red_or_density_steps, ←filter_or],
--     refine filter_congr _,
--     intros i hi,
--     rw [←and_or_distrib_left, ←not_le, and_iff_left],
--     exact em _ },
--   rw [add_right_comm _ _ (finset.card _), ←card_disjoint_union red_steps_disjoint_density_steps,
--     red_steps_union_density_steps, add_comm _ (finset.card _),
--     ←card_disjoint_union big_blue_steps_disjoint_red_or_density_steps, this, degree_steps],
--   apply filter_even_thing
-- end

lemma seven_six_large_jump_bound (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (((degree_steps μ k l ini).filter
    (λ i, ((X_ (i + 1)).card : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) * (X_ i).card)).card : ℝ) ≤
    7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1 :=
begin
  filter_upwards [seven_twelve μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    four_three hμ₀] with l h712 h43
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize h712 k hlk μ hμl hμu n χ hχ ini hini,
  specialize h43 k hlk μ hμl n χ hχ ini,
  rw [degree_steps],
  have : ((range (final_step μ k l ini)).filter even).image nat.succ ⊆
    (range (final_step μ k l ini + 1)).filter (λ i, ¬ even i),
  { simp only [finset.subset_iff, mem_filter, mem_image, and_imp, exists_prop, and_assoc,
      mem_range, forall_exists_index, nat.succ_eq_add_one],
    rintro _ y hy hy' rfl,
    simp [hy, hy'] with parity_simps },
  rw ←finset.card_image_of_injective _ nat.succ_injective,
  have : (((range (final_step μ k l ini)).filter even).filter (λ i,
    ((algorithm μ k l ini (i + 1)).X.card : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) *
    (algorithm μ k l ini i).X.card)).image nat.succ =
    (((range (final_step μ k l ini)).filter even).image nat.succ).filter (λ i,
    ((algorithm μ k l ini i).X.card : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) *
    (algorithm μ k l ini (i - 1)).X.card),
  { rw image_filter,
    refl },
  rw this,
  clear this,
  refine (nat.cast_le.2 (card_le_of_subset (filter_subset_filter _ this))).trans _,
  set f : ℕ → Prop := λ i, ((algorithm μ k l ini i).X.card : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) *
    (algorithm μ k l ini (i - 1)).X.card,
  simp only [←nat.odd_iff_not_even],
  have : ((((range (final_step μ k l ini + 1)).filter odd).filter f).card : ℝ) ≤
    (((range (final_step μ k l ini)).filter odd).filter f).card + 1,
  { norm_cast,
    rw [filter_filter, filter_filter, range_succ, filter_insert],
    split_ifs,
    { exact card_insert_le _ _ },
    exact nat.le_succ _ },
  refine this.trans (add_le_add_right _ _),
  rw [range_filter_odd_eq_union, union_right_comm, red_steps_union_density_steps, filter_union],
  refine (nat.cast_le.2 (card_union_le _ _)).trans _,
  rw nat.cast_add,
  refine add_le_add h712 _,
  refine (rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 hlk) (by norm_num1)).trans' _,
  refine h43.trans' _,
  rw nat.cast_le,
  exact card_le_of_subset (filter_subset _ _),
end

lemma seven_six_o :
   (λ (k : ℕ), (-(2 / log 2 * ((7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) * log k))) +
    (-(4 * (k ^ (- 1 / 16 : ℝ) * (3 * k))))) =o[at_top] (λ i, (i : ℝ)) :=
begin
  suffices : (λ (k : ℝ), (-(2 / log 2 * ((7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) * log k))) +
    (-(4 * (k ^ (- 1 / 16 : ℝ) * (3 * k))))) =o[at_top] (λ x : ℝ, x),
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
  refine is_o.add _ _,
  { refine is_o.neg_left _,
    refine is_o.const_mul_left _ _,
    have : (λ k : ℝ, 7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) =O[at_top]
      (λ k, k ^ (15 / 16 : ℝ)),
    { refine is_O.add (is_O.add _ _) _,
      { exact (is_O_refl _ _).const_mul_left _ },
      { refine (is_o_rpow_rpow _).is_O,
        norm_num1 },
      { refine (is_o_one_rpow _).is_O,
        norm_num1 } },
    refine (this.mul_is_o (is_o_log_rpow_at_top (show (0 : ℝ) < 1 / 16, by norm_num1))).congr'
      eventually_eq.rfl _,
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk,
    rw [←rpow_add hk],
    norm_num },
  { refine is_o.neg_left _,
    refine is_o.const_mul_left _ _,
    simp only [mul_left_comm],
    refine is_o.const_mul_left _ _,
    refine (is_o_rpow_rpow (show (15 / 16 : ℝ) < 1, by norm_num1)).congr' _ _,
    { filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk,
      rw [←rpow_add_one hk.ne'],
      norm_num },
    { simp only [rpow_one] } },
end

-- uses k ≥ 4 ^ 16, but this can be weakened a lot by putting an extra factor of 2 in f
lemma seven_six :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ μ₁ p₀ : ℝ, 0 < μ₀ → μ₁ < 1 → 0 < p₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (2 : ℝ) ^ f k ≤
    ∏ i in degree_steps μ k l ini,
      ((algorithm μ k l ini (i + 1)).X).card / ((algorithm μ k l ini i).X).card :=
begin
  have tt : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  refine ⟨λ k, (-(2 / log 2 * ((7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) * log k))) +
    (-(4 * (k ^ (- 1 / 16 : ℝ) * (3 * k)))),
    seven_six_o, _⟩,
  have h16 : (0 : ℝ) < 1 / 16,
  { norm_num1 },
  have h : (0 : ℝ) < 1 / (2 * 2) := by norm_num1,
  intros μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
  filter_upwards [seven_eight μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    seven_six_large_jump_bound μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster (((tendsto_rpow_neg_at_top h16).comp tt).eventually (eventually_le_nhds h))]
    with l h78 h₁ hk0 h'
    k hlk μ hμl hμu n χ hχ ini hini,
  -- specialize h712 k hlk n χ hχ ini hini hini',
  specialize h₁ k hlk μ hμl hμu n χ hχ ini hini,
  rw [←filter_union_filter_neg_eq (λ i, ((algorithm μ k l ini (i + 1)).X.card : ℝ) <
    (1 - 2 * k ^ (- 1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card) (degree_steps μ k l ini),
    prod_union (disjoint_filter_filter_neg _ _ _), rpow_add two_pos],
  have hk₀ : (0 : ℝ) < k,
  { rw nat.cast_pos,
    exact hk0 k hlk },
  refine mul_le_mul _ _ (rpow_nonneg_of_nonneg two_pos.le _) (prod_nonneg (λ i hi, div_nonneg
    (nat.cast_nonneg _) (nat.cast_nonneg _))),
  { have : ∀ i : ℕ, i ∈ (degree_steps μ k l ini).filter (λ i, ((algorithm μ k l ini (i + 1)).X.card
      : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card) → ((1 : ℝ) / k ^ 2) ≤
      (algorithm μ k l ini (i + 1)).X.card / (algorithm μ k l ini i).X.card,
    { intros i hi,
      rw [mem_filter] at hi,
      rw [le_div_iff', mul_one_div],
      { refine h78 k hlk μ hμl hμu n χ hχ ini hini i _,
        exact hi.1 },
      rw [nat.cast_pos, card_pos],
      rw [degree_steps, mem_filter, mem_range] at hi,
      exact X_nonempty hi.1.1 },
    refine (finset.prod_le_prod _ this).trans' _,
    { intros i hi,
      positivity },
    rw [prod_const, ←rpow_nat_cast, one_div, inv_rpow (sq_nonneg _), ←rpow_two,
      ←rpow_mul (nat.cast_nonneg _), ←rpow_neg (nat.cast_nonneg _),
      ←log_le_log (rpow_pos_of_pos two_pos _) (rpow_pos_of_pos hk₀ _), log_rpow two_pos,
      log_rpow hk₀, ←le_div_iff (log_pos one_lt_two), neg_mul, neg_div, neg_le_neg_iff,
      mul_assoc, ←div_mul_eq_mul_div],
    refine mul_le_mul_of_nonneg_left _ (div_nonneg (zero_lt_two' ℝ).le (log_nonneg one_le_two)),
    refine mul_le_mul_of_nonneg_right h₁ (log_nonneg _),
    rw [nat.one_le_cast, nat.succ_le_iff],
    exact hk0 k hlk },
  have h₁ : (2 : ℝ) ^ ((- 2 : ℝ) * (2 * k ^ (- 1 / 16 : ℝ))) ≤ 1 - 2 * k ^ (- 1 / 16 : ℝ),
  { refine two_approx _ _,
    { positivity },
    rw [←le_div_iff' (zero_lt_two' ℝ), div_div, neg_div],
    exact h' k hlk },
  have : ∀ i : ℕ, i ∈ (degree_steps μ k l ini).filter (λ i, ¬ ((algorithm μ k l ini (i + 1)).X.card
    : ℝ) < (1 - 2 * k ^ (- 1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card) →
    (2 : ℝ) ^ ((- 2 : ℝ) * (2 * k ^ (- 1 / 16 : ℝ))) ≤
      (algorithm μ k l ini (i + 1)).X.card / (algorithm μ k l ini i).X.card,
  { intros i hi,
    rw [mem_filter, not_lt] at hi,
    refine h₁.trans _,
    rw [le_div_iff],
    { exact hi.2 },
    rw [nat.cast_pos, card_pos],
    refine X_nonempty _,
    rw [degree_steps, mem_filter, mem_range] at hi,
    exact hi.1.1 },
  refine (finset.prod_le_prod _ this).trans' _,
  { intros i hi,
    exact rpow_nonneg_of_nonneg two_pos.le _ },
  rw [prod_const, ←rpow_nat_cast, ←rpow_mul two_pos.le],
  refine rpow_le_rpow_of_exponent_le one_le_two _,
  rw [neg_mul, neg_mul, neg_le_neg_iff, ←mul_assoc, ←mul_assoc, ←bit0_eq_two_mul],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  norm_cast,

  -- rw [←nat.cast_two, ←nat.cast_mul, nat.cast_two, ←nat.cast_add_one, nat.cast_le],
  refine (card_le_of_subset (filter_subset _ _)).trans _,
  refine (four_four_degree μ (hk0 k hlk).ne' (hk0 l le_rfl).ne' hχ ini).trans _,
  have : 1 ≤ k,
  { rw nat.succ_le_iff,
    exact hk0 k hlk },
  linarith only [this, hlk],
end.

lemma telescope_X_card (μ : ℝ) (h : ini.X.nonempty) :
  -- (hp₀ : 0 < p₀) (h : p₀ ≤ ini.p) :
  ((end_state μ k l ini).X.card : ℝ) / ini.X.card =
    ∏ i in range (final_step μ k l ini),
      ((algorithm μ k l ini (i + 1)).X.card / (algorithm μ k l ini i).X.card) :=
begin
  suffices : ∀ j ≤ final_step μ k l ini,
    ((algorithm μ k l ini j).X.card : ℝ) / ini.X.card =
    ∏ i in range j, ((algorithm μ k l ini (i + 1)).X.card / (algorithm μ k l ini i).X.card),
  { exact this _ le_rfl },
  intros j hj,
  induction j with j ih,
  { rw [prod_range_zero, algorithm_zero, div_self],
    rw [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
    exact h },
  rw nat.succ_le_iff at hj,
  rw [prod_range_succ, ←ih hj.le, mul_comm, div_mul_div_cancel],
  rw [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
  exact X_nonempty hj
end

lemma seven_one_calc {frk fbk fsk fdk μ β : ℝ} {s_ t_ : ℕ} :
  2 ^ frk * 2 ^ fbk * 2 ^ fsk * 2 ^ fdk * μ ^ l * (1 - μ) ^ t_ *
    (β ^ s_ * (μ ^ s_)⁻¹) =
  2 ^ fbk *
    (μ ^ l * (μ ^ s_)⁻¹) * (2 ^ frk * (1 - μ) ^ t_) *
      (2 ^ fsk * β ^ s_) * 2 ^ fdk :=
by ring_nf

lemma seven_one (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ p₀ : ℝ, 0 < μ₀ → 0 < p₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (2 : ℝ) ^ f k * μ ^ l * (1 - μ) ^ t * (beta μ k l ini / μ) ^ s * ini.X.card ≤
    (end_state μ k l ini).X.card :=
begin
  obtain ⟨fr, hfr, hr'⟩ := seven_two μ₁ hμ₁,
  obtain ⟨fb, hfb, hb'⟩ := seven_three,
  obtain ⟨fs, hfs, hs'⟩ := seven_four,
  obtain ⟨fd, hfd, hd'⟩ := seven_six,
  refine ⟨λ i, fr i + fb i + fs i + fd i, ((hfr.add hfb).add hfs).add hfd, _⟩,
  intros μ₀ p₀ hμ₀ hp₀,
  filter_upwards [hr', hb' μ₀ μ₁ hμ₀ hμ₁, hs' μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, hd' μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0)] with l hr hb hs hd hk₀
    k hlk μ hμl hμu n χ hχ ini hini,
  clear hr' hb' hs' hd',
  specialize hr k hlk μ hμu n χ hχ ini,
  specialize hb k hlk μ hμl hμu n χ hχ ini,
  specialize hs k hlk μ hμl hμu n χ hχ ini hini,
  specialize hd k hlk μ hμl hμu n χ hχ ini hini,
  have : ini.X.nonempty,
  { rw nonempty_iff_ne_empty,
    intro h',
    rw [book_config.p, h', col_density_empty_left] at hini,
    exact hp₀.not_le hini },
  rw ←le_div_iff,
  swap,
  { rwa [nat.cast_pos, card_pos] },
  rw [telescope_X_card μ this, ←union_partial_steps, union_comm (red_or_density_steps μ k l ini),
    prod_union degree_steps_disjoint_big_blue_steps_union_red_or_density_steps.symm,
    prod_union big_blue_steps_disjoint_red_or_density_steps, ←red_steps_union_density_steps,
    prod_union red_steps_disjoint_density_steps, ←mul_assoc],
  have : (density_steps μ k l ini).card ≤ l,
  { refine (four_four_blue_density μ (hk₀ k hlk).ne' (hk₀ l le_rfl).ne' hχ ini).trans' _,
    exact nat.le_add_left _ _ },
  have : (2 : ℝ) ^ (fr k + fb k + fs k + fd k) * μ ^ l * (1 - μ) ^ t * (beta μ k l ini / μ) ^ s =
    (2 ^ fb k * μ ^ (l - s)) * (2 ^ fr k * (1 - μ) ^ t) * (2 ^ fs k * beta μ k l ini ^ s) *
    (2 ^ fd k),
  { rw [pow_sub₀ _ (hμ₀.trans_le hμl).ne' this, div_pow, div_eq_mul_inv, rpow_add two_pos,
      rpow_add two_pos, rpow_add two_pos],
    exact seven_one_calc },
  rw this,
  have : (0 : ℝ) ≤ ∏ i in ℛ,
    ((algorithm μ k l ini (i + 1)).X.card : ℝ) / ((algorithm μ k l ini i).X.card : ℝ),
  { refine prod_nonneg _,
    intros i hi,
    positivity },
  have : (0 : ℝ) ≤ ∏ i in ℬ,
    ((algorithm μ k l ini (i + 1)).X.card : ℝ) / ((algorithm μ k l ini i).X.card : ℝ),
  { refine prod_nonneg _,
    intros i hi,
    positivity },
  have : (0 : ℝ) ≤ ∏ i in 𝒮,
    ((algorithm μ k l ini (i + 1)).X.card : ℝ) / ((algorithm μ k l ini i).X.card : ℝ),
  { refine prod_nonneg _,
    intros i hi,
    positivity },
  refine mul_le_mul _ hd (rpow_nonneg_of_nonneg two_pos.le _) _,
  refine mul_le_mul _ hs (mul_nonneg (rpow_nonneg_of_nonneg two_pos.le _) (pow_nonneg (beta_nonneg
    (hμ₀.trans_le hμl)) _)) _,
  refine mul_le_mul hb hr (mul_nonneg (rpow_nonneg_of_nonneg two_pos.le _) (pow_nonneg
    (sub_nonneg_of_le (hμu.trans hμ₁.le)) _)) _,
  all_goals { positivity },
end

end simple_graph
