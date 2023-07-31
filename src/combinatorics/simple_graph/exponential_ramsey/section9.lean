import combinatorics.simple_graph.exponential_ramsey.section8

namespace simple_graph

open_locale big_operators exponential_ramsey nat real

open filter finset nat real asymptotics

-- fails at n = 0 because rhs is 0 and lhs is 1
lemma little_o_stirling :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (1 : ℝ)) ∧
  ∀ n : ℕ, n ≠ 0 → (n! : ℝ) = (1 + f n) * sqrt (2 * π * n) * (n / exp 1) ^ n :=
begin
  refine ⟨λ n, stirling.stirling_seq n / sqrt π - 1, _, _⟩,
  { rw is_o_one_iff,
    convert (stirling.tendsto_stirling_seq_sqrt_pi.div_const _).sub_const _ using 1,
    rw [nhds_eq_nhds_iff, div_self, sub_self],
    rw sqrt_ne_zero',
    exact pi_pos },
  intros n hn,
  rw [add_sub_cancel'_right, div_mul_eq_mul_div, mul_div_assoc, ←sqrt_div' _ pi_pos.le,
    ←div_mul_eq_mul_div, mul_div_cancel _ pi_pos.ne', stirling.stirling_seq, mul_assoc,
    div_mul_cancel],
  positivity
end

-- giving explicit bounds here requires an explicit version of stirling
lemma weak_little_o_stirling :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ n : ℕ in at_top, (n! : ℝ) = 2 ^ f n * (n / exp 1) ^ n :=
begin
  obtain ⟨f, hf, hf'⟩ := little_o_stirling,
  rw is_o_one_iff at hf,
  refine ⟨λ n, (log 2)⁻¹ * (log (1 + f n) + (1 / 2 * log (2 * π) + 1 / 2 * log n)), _, _⟩,
  { refine is_o.const_mul_left _ _,
    refine is_o.add _ _,
    { refine is_O.trans_is_o _
        ((is_o_const_id_at_top (1 : ℝ)).comp_tendsto tendsto_coe_nat_at_top_at_top),
      -- show log (1 + o(1)) is O(1) (it's actually o(1) but O(1) is easier for now)
      rw is_O_iff,
      refine ⟨log 2, _⟩,
      have h₁ : (-1 / 2 : ℝ) < 0 := by norm_num,
      filter_upwards [eventually_gt_at_top 0, hf.eventually (eventually_ge_nhds h₁),
        hf.eventually (eventually_le_nhds zero_lt_one)] with n hn1 hneg h1,
      have : 0 < 1 + f n := by linarith only [hneg],
      simp only [norm_eq_abs, pi.const_one, pi.one_apply, norm_one, mul_one],
      rw [abs_le, ←log_inv, ←one_div],
      refine ⟨log_le_log_of_le (by norm_num1) _, log_le_log_of_le this (by linarith only [h1])⟩,
      linarith only [hneg] },
    suffices : (λ n : ℝ, 1 / 2 * log (2 * π) + 1 / 2 * log n) =o[at_top] id,
    { exact is_o.comp_tendsto this tendsto_coe_nat_at_top_at_top },
    exact is_o.add (is_o_const_id_at_top _) (is_o_log_id_at_top.const_mul_left _) },
  have h₁ : (-1 : ℝ) < 0 := by norm_num,
  have := pi_pos,
  filter_upwards [eventually_gt_at_top 0, hf.eventually (eventually_gt_nhds h₁),
    hf.eventually (eventually_le_nhds zero_lt_one)] with n hn1 hneg h1,
  have : 0 < 1 + f n := by linarith only [hneg],
  rw [hf' n hn1.ne', rpow_def_of_pos, mul_inv_cancel_left₀ (log_pos one_lt_two).ne',
    ←mul_add, ←log_mul, ←log_rpow, ←sqrt_eq_rpow, ←log_mul, exp_log],
  all_goals {positivity},
end

lemma nine_four_log_aux :
  ∃ g : ℕ → ℝ, g =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k →
  g k ≤ log (k + l) - log k - log l :=
begin
  refine ⟨λ k, log 2 - log k, _, _⟩,
  { suffices : (λ k : ℝ, log 2 - log k) =o[at_top] id,
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    exact is_o.sub (is_o_const_id_at_top _) is_o_log_id_at_top },
  filter_upwards [eventually_gt_at_top 0] with l hl₀ k hlk,
  rw [sub_sub, add_comm (log _), ←sub_sub, sub_le_sub_iff_right, ←log_div],
  { refine log_le_log_of_le zero_lt_two _,
    rwa [le_div_iff, two_mul, add_le_add_iff_right, nat.cast_le],
    rwa nat.cast_pos },
  { positivity },
  { positivity },
end

lemma nine_four_aux_aux {f : ℕ → ℝ} (hf : f =o[at_top] (λ i, (1 : ℝ))) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k →
    2 ^ (- 3 : ℝ) ≤ (1 + f (k + l)) / ((1 + f k) * (1 + f l)) :=
begin
  rw is_o_one_iff at hf,
  have h₁ : (-1 / 2 : ℝ) < 0 := by norm_num,
  filter_upwards [eventually_gt_at_top 0, top_adjuster (hf.eventually (eventually_ge_nhds h₁)),
    top_adjuster (hf.eventually (eventually_le_nhds zero_lt_one))] with l hn1 hneg h1 k hlk,
  have h₂ : ∀ k, l ≤ k → 1 / 2 ≤ 1 + f k,
  { intros k hlk,
    linarith only [hneg k hlk] },
  have h₃ : ∀ k, l ≤ k → 1 + f k ≤ 2,
  { intros k hlk,
    linarith only [h1 k hlk] },
  have h₄ : ∀ k, l ≤ k → 0 < 1 + f k,
  { intros k hlk,
    linarith only [h₂ k hlk] },
  refine (div_le_div (h₄ _ le_add_self).le (h₂ _ le_add_self) (mul_pos (h₄ _ hlk) (h₄ _ le_rfl))
    (mul_le_mul (h₃ _ hlk) (h₃ _ le_rfl) (h₄ _ le_rfl).le zero_lt_two.le)).trans' _,
  norm_num
end

lemma nine_four_aux :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k →
  (2 : ℝ) ^ f k * ((k + l) ^ (k + l) / (k ^ k * l ^ l)) ≤ ((k + l).choose l : ℝ) :=
begin
  obtain ⟨f, hf, hf'⟩ := little_o_stirling,
  obtain ⟨g, hg, hg'⟩ := nine_four_log_aux,
  refine ⟨λ k, -3 + (2 * log 2)⁻¹ * (g k - log (2 * π)), _, _⟩,
  { refine is_o.add (is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_coe_nat_at_top_at_top) _,
    refine is_o.const_mul_left _ _,
    exact is_o.sub hg (is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_coe_nat_at_top_at_top) },
  filter_upwards [top_adjuster (eventually_gt_at_top 0), nine_four_aux_aux hf, hg'] with l hk₀ h₈
    hg'' k hlk,
  have := pi_pos,
  have hl₀' := hk₀ l le_rfl,
  have hk₀' := hk₀ k hlk,
  rw [←nat.choose_symm_add, nat.cast_add_choose, hf', hf' _ hk₀'.ne',
    hf' _ (hk₀ l le_rfl).ne', mul_mul_mul_comm, ←div_mul_div_comm, mul_mul_mul_comm,
    ←div_mul_div_comm, div_pow, div_pow, div_pow, div_mul_div_comm _ (exp 1 ^ k), ←pow_add,
    div_div_div_cancel_right (_ : ℝ) (pow_ne_zero _ (exp_pos _).ne'), nat.cast_add, ←sqrt_mul,
    ←sqrt_div, rpow_add two_pos, mul_assoc (2 * π), mul_div_mul_left],
  rotate,
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  refine mul_le_mul_of_nonneg_right _ (by positivity),
  refine mul_le_mul (h₈ k hlk) _ (rpow_nonneg_of_nonneg two_pos.le _) ((h₈ k hlk).trans'
    (by norm_num1)),
  rw [←le_logb_iff_rpow_le one_lt_two, logb, log_sqrt, log_div, @log_mul k, @log_mul _ l, div_div,
    add_left_comm, add_comm (log _), ←sub_sub, ←sub_sub, div_eq_mul_inv, mul_comm],
  { exact div_le_div_of_le_of_nonneg (sub_le_sub_right (hg'' _ hlk) _)
      (mul_nonneg two_pos.le (log_nonneg one_le_two)) },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
end

lemma nine_four :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ γ : ℝ, γ = l / (k + l) →
  (2 : ℝ) ^ f k * γ ^ (- l : ℤ) * (1 - γ) ^ (- k : ℤ) ≤ ((k + l).choose l : ℝ) :=
begin
  obtain ⟨f, hf, hf'⟩ := nine_four_aux,
  refine ⟨f, hf, _⟩,
  filter_upwards [top_adjuster (eventually_gt_at_top 0), hf'] with l hk₀ hf₁
    k hlk γ hγ,
  refine (hf₁ k hlk).trans_eq' _,
  rw [mul_assoc, hγ, one_sub_div, add_sub_cancel, zpow_neg, zpow_neg, ←inv_zpow, ←inv_zpow, inv_div,
    inv_div, zpow_coe_nat, zpow_coe_nat, mul_comm (_ ^ l), div_pow, div_pow, div_mul_div_comm,
    ←pow_add],
  have := hk₀ k hlk,
  positivity
end

-- condition_fails_at_end

-- lemma one_div_k_lt_p (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
--   ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
--   ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
--   ∀ ini : book_config χ, p₀ ≤ ini.p →
--   ∀ i, i ≤ final_step μ k l ini → 1 / (k : ℝ) < p_ i :=

lemma end_ramsey_number (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (end_state μ k l ini).X.card ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
  filter_upwards [one_div_k_lt_p μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_at_top 0)] with
    l hl hl₀ k hlk μ hμl hμu n χ hχ ini hini,
  refine (condition_fails_at_end (hl₀ k hlk).ne' (hl₀ l le_rfl).ne').resolve_right _,
  rw not_le,
  exact hl k hlk μ hμl hμu n χ hχ ini hini _ le_rfl,
end

lemma end_ramsey_number_pow_is_o :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ μ₀ μ₁ p₀ : ℝ, 0 < μ₀ → μ₁ < 1 → 0 < p₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ₀ ≤ μ → μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ((end_state μ k l ini).X.card : ℝ) ≤ 2 ^ f k :=
begin
  refine ⟨λ k, (log 2)⁻¹ * (2 * (log k * k ^ (3 / 4 : ℝ))), _, _⟩,
  { refine is_o.const_mul_left _ _,
    refine is_o.const_mul_left _ _,
    suffices : (λ k, (log k * k ^ (3 / 4 : ℝ))) =o[at_top] id,
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    refine (is_o.mul_is_O (is_o_log_rpow_at_top (by norm_num : (0 : ℝ) < 1 / 4))
      (is_O_refl _ _)).congr' eventually_eq.rfl _,
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk,
    rw [←rpow_add hk],
    norm_num1,
    rw [rpow_one, id.def] },
  intros μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
  filter_upwards [end_ramsey_number μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, eventually_ge_at_top 1] with l hl hl₁
    k hlk μ hμl hμu n χ hχ ini hini,
  specialize hl k hlk μ hμl hμu n χ hχ ini hini,
  rw [rpow_def_of_pos two_pos, mul_inv_cancel_left₀ (log_pos one_lt_two).ne', mul_left_comm,
    ←rpow_def_of_pos (nat.cast_pos.2 _)],
  swap,
  { exact hl₁.trans hlk },
  rw ramsey_number_pair_swap at hl,
  refine (nat.cast_le.2 (hl.trans ramsey_number_le_right_pow_left')).trans _,
  rw [nat.cast_pow, ←rpow_nat_cast],
  refine rpow_le_rpow_of_exponent_le (nat.one_le_cast.2 (hl₁.trans hlk)) _,
  refine (ceil_le_two_mul _).trans (mul_le_mul_of_nonneg_left (rpow_le_rpow (nat.cast_nonneg _)
    (nat.cast_le.2 hlk) (by norm_num1)) two_pos.le),
  exact (one_le_rpow (nat.one_le_cast.2 hl₁) (by norm_num1)).trans' (by norm_num1),
end

-- lemma nine_three_part_one (γ δ p₁ : ℝ) (hγ₀ : 0 < γ) (hγ : γ ≤ 1 / 5) (hp₁ : p₁ < 1) :
--   ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
--   ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, γ = l / (k + l) →
--   l ≤ k → -- redundant
--   ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
--   ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
--   ∀ (ini : book_config χ), 1 / 4 ≤ ini.p → ini.p ≤ p₁ →
--   exp (- δ * k) * (k + l).choose l ≤ n →
--   exp (- δ * k) * (1 - γ) ^ (- k + (red_steps γ k l ini).card : ℤ) *
--     (beta γ k l ini / γ) ^ (density_steps γ k l ini).card
--     ≤ 2 ^ f k :=
-- begin
--   have hγ₁ : γ < 1 := hγ.trans_lt (by norm_num1),
--   obtain ⟨f, hf, hf'⟩ := end_ramsey_number_pow_is_o γ (1 / 4) hγ₀ hγ₁ (by norm_num1),
--   obtain ⟨g, hg, hg'⟩ := seven_one γ (1 / 4) p₁ hγ₀ hγ₁ (by norm_num1) hp₁,
--   refine ⟨sorry, sorry, _⟩,
--   filter_upwards [hf', hg'] with
--     l hf'' hg'' k hγ' hlk n χ hχ ini hini hini' hn,
--   clear hf' hg',
--   specialize hf'' k hlk n χ hχ ini hini,
--   specialize hg'' k hlk n χ hχ ini hini hini',
--   have := hg''.trans hf'',
-- end

-- #exit

-- lemma nine_three (γ δ : ℝ) (hγ : γ ≤ 1 / 5) (hδ : δ = min (1 / 200) (γ / 20)) :
--   ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, γ = l / (k + l) →
--   ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
--   ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
--   ∀ (ini : book_config χ), 1 / 4 ≤ ini.p →
--   exp (- δ * k) * (k + l).choose l ≤ n →
--   2 * k / 3 ≤ (red_steps μ k l ini).card :=
-- begin
--   filter_upwards [top_adjuster (eventually_gt_at_top 0)] with
--     l hk₀ k hγ' n χ hχ ini hini hn,
--   have hl₀ : 0 < l := hk₀ l le_rfl,
--   have hl4k : 4 * l ≤ k,
--   { rw [hγ', div_le_div_iff, one_mul, ←sub_le_iff_le_add, ←mul_sub_one, mul_comm, bit1,
--       add_sub_cancel] at hγ,
--     { rwa [←@nat.cast_le ℝ, nat.cast_mul, nat.cast_bit0, nat.cast_two] },
--     { exact lt_add_of_le_of_pos (nat.cast_nonneg k) (nat.cast_pos.2 hl₀) },
--     { norm_num1 } },
--   have hlk : l ≤ k := hl4k.trans' (nat.le_mul_of_pos_left (by norm_num1)),
--   have : 0 < k := hk₀ k hlk,

-- end

end simple_graph
