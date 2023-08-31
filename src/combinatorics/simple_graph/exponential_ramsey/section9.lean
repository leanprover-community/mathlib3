import combinatorics.simple_graph.exponential_ramsey.section8
import analysis.special_functions.log.base

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

-- g is log 2 - log k
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

-- f is -3 + (log 2 - log k - log (2 π)) / (2 log 2)
--    = -3 - (log k + log π) / (2 log 2)
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

-- f is -3 + (log 2 - log k - log (2 π)) / (2 log 2)
lemma nine_four :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ γ : ℝ, γ = l / (k + l) →
  (2 : ℝ) ^ f k * γ ^ (- l : ℝ) * (1 - γ) ^ (- k : ℝ) ≤ ((k + l).choose l : ℝ) :=
begin
  obtain ⟨f, hf, hf'⟩ := nine_four_aux,
  refine ⟨f, hf, _⟩,
  filter_upwards [top_adjuster (eventually_gt_at_top 0), hf'] with l hk₀ hf₁
    k hlk γ hγ,
  have := hk₀ k hlk,
  refine (hf₁ k hlk).trans_eq' _,
  rw [mul_assoc, hγ, one_sub_div, add_sub_cancel, rpow_neg, rpow_neg, ←inv_rpow, ←inv_rpow, inv_div,
    inv_div, rpow_nat_cast, rpow_nat_cast, mul_comm (_ ^ l), div_pow, div_pow, div_mul_div_comm,
    ←pow_add],
  all_goals {positivity}
end

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

lemma desc_factorial_eq_prod {n k : ℕ} : n.desc_factorial k = ∏ i in range k, (n - i) :=
begin
  induction k,
  { simp },
  rw [nat.desc_factorial_succ, k_ih, finset.prod_range_succ, mul_comm],
end

lemma cast_desc_factorial_eq_prod {n k : ℕ} :
  (n.desc_factorial k : ℝ) = ∏ i in range k, (n - i : ℝ) :=
by rw [desc_factorial_eq_prod, prod_range_cast_nat_sub]

lemma pow_div_le_choose {n k : ℕ} (h : k ≤ n) : (n / k : ℝ) ^ k ≤ n.choose k :=
begin
  rw [nat.choose_eq_desc_factorial_div_factorial, nat.cast_div, ←prod_range_add_one_eq_factorial,
    nat.cast_prod, ←prod_range_reflect, cast_desc_factorial_eq_prod, ←prod_div_distrib],
  { suffices : ∀ x ∈ range k, (n / k : ℝ) ≤ (n - x : ℝ) / ((k - 1 - x) + 1 : ℕ),
    { refine (finset.prod_le_prod _ this).trans_eq' _,
      { intros,
        positivity },
      simp },
    intros x hx,
    rw mem_range at hx,
    have : 0 < k - x,
    { exact nat.sub_pos_of_lt hx },
    rw [nat.sub_sub, add_comm 1, ←nat.sub_sub, nat.sub_add_cancel, div_le_div_iff,
      nat.cast_sub hx.le, mul_sub, sub_mul, sub_le_sub_iff_left, mul_comm, ←nat.cast_mul,
      ←nat.cast_mul, nat.cast_le],
    { exact nat.mul_le_mul_right _ h },
    { rw nat.cast_pos,
      exact pos_of_gt hx },
    { rwa nat.cast_pos },
    { exact this } },
  { exact nat.factorial_dvd_desc_factorial _ _ },
  { positivity }
end

lemma exp_le_one_sub_inv {x : ℝ} (hx : x < 1) : exp x ≤ (1 - x)⁻¹ :=
begin
  rw [le_inv (exp_pos _) (sub_pos_of_lt hx), ←real.exp_neg, ←neg_add_eq_sub],
  exact add_one_le_exp _
end

lemma le_of_gamma_le_half {l k : ℕ} {γ : ℝ} (h : γ = l / (k + l)) (hl : 0 < l) (hγ : γ ≤ 1 / 2) :
  l ≤ k :=
begin
  rwa [h, div_le_div_iff, one_mul, mul_comm, two_mul, add_le_add_iff_right, nat.cast_le] at hγ,
  { exact lt_add_of_le_of_pos (nat.cast_nonneg k) (nat.cast_pos.2 hl) },
  { exact two_pos },
end

lemma nine_three_lower_n (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ < 1 →
  l ≤ k →
  ∀ δ : ℝ, δ ≤ γ / 20 →
  ∀ n : ℕ,
  exp (- δ * k) * (k + l).choose l ≤ n →
  2 ≤ n :=
begin
  filter_upwards [eventually_gt_at_top 0, eventually_ge_at_top ⌈log 2 / (γ₀ * (19 / 20))⌉₊] with
    l hl hk
    k γ hγ hγl hγ₁ hlk δ hδ n hn,
  have : (1 - γ)⁻¹ ^ (k : ℕ) ≤ (k + l).choose l,
  { rw [add_comm, nat.choose_symm_add],
    refine (pow_div_le_choose (by simp)).trans_eq' _,
    rw [hγ, one_sub_div, add_sub_cancel, inv_div, add_comm, nat.cast_add],
    positivity },
  have : exp γ ^ k ≤ (k + l).choose l,
  { refine this.trans' (pow_le_pow_of_le_left (exp_pos _).le _ _),
    exact exp_le_one_sub_inv hγ₁ },
  rw [←@nat.cast_le ℝ, nat.cast_two],
  refine hn.trans' ((mul_le_mul_of_nonneg_left this (exp_pos _).le).trans' _),
  rw [mul_comm (- δ), ←exp_nat_mul, ←real.exp_add, ←mul_add, neg_add_eq_sub,
    ←log_le_iff_le_exp two_pos],
  have : γ₀ * (19 / 20) ≤ γ - δ,
  { linarith },
  refine (mul_le_mul_of_nonneg_left this (nat.cast_nonneg _)).trans' _,
  rw [←div_le_iff, ←nat.ceil_le],
  { exact hk.trans hlk },
  positivity
end

lemma ge_floor {n : ℝ} (h : 1 ≤ n) : (n / 2 : ℝ) ≤ ⌊(n : ℝ)⌋₊ :=
begin
  cases lt_or_le n 2 with h₂ h₂,
  { have : (1 : ℝ) ≤ ⌊n⌋₊,
    { rwa [nat.one_le_cast, nat.one_le_floor_iff] },
    refine this.trans' _,
    linarith },
  refine (nat.sub_one_lt_floor n).le.trans' _,
  linarith
end

lemma nine_three_part_one :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ γ₀ : ℝ, 0 < γ₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 5 →
  l ≤ k →
  ∀ δ : ℝ, δ = min (1 / 200) (γ / 20) →
  ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), 1 / 4 ≤ ini.p →
  ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
  exp (- δ * k) * (k + l).choose l ≤ n →
  exp (- δ * k) * (1 - γ) ^ (- k + (red_steps γ k l ini).card : ℝ) *
    (beta γ k l ini / γ) ^ (density_steps γ k l ini).card
    ≤ 2 ^ f k :=
begin
  have hμ₁ : (1 / 5 : ℝ) < 1 := by norm_num1,
  have hp₀ : (0 : ℝ) < 1 / 4 := by norm_num1,
  obtain ⟨f₁, hf₁, hf₁'⟩ := end_ramsey_number_pow_is_o,
  obtain ⟨f₂, hf₂, hf₂'⟩ := seven_one (1 / 5) hμ₁,
  obtain ⟨f₃, hf₃, hf₃'⟩ := nine_four,
  refine ⟨λ k, f₁ k - f₂ k - f₃ k + 2, _, _⟩,
  { refine is_o.add ((hf₁.sub hf₂).sub hf₃) _,
    exact (is_o_const_id_at_top _).comp_tendsto tendsto_coe_nat_at_top_at_top },
  intros γ₀ hγ₀,
  specialize hf₁' γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀,
  specialize hf₂' γ₀ (1 / 4) hγ₀ hp₀,
  filter_upwards [hf₁', hf₂', hf₃', nine_three_lower_n γ₀ hγ₀,
    beta_pos γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀] with l hfk hgk hc hn'' hβ
    k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn,
  clear hf₁' hf₂' hf₃',
  have hδ' : δ ≤ γ / 20,
  { rw hδ,
    exact min_le_right _ _ },
  specialize hfk k hlk γ hγl hγu n χ hχ ini hini,
  specialize hgk k hlk γ hγl hγu n χ hχ ini hini,
  specialize hc k hlk γ hγ,
  specialize hn'' k γ hγ hγl (hγu.trans_lt (by norm_num1)) hlk δ hδ' n hn,
  specialize hβ k hlk γ hγl hγu n χ ini hini,
  have hγ₁ : γ < 1 := by linarith only [hγu],
  have hγ₁' : 0 < 1 - γ := sub_pos_of_lt hγ₁,
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl,
  have : 2 ^ (-2 : ℝ) * (n : ℝ) ≤ ini.X.card,
  { refine (nat.cast_le.2 hn').trans' ((ge_floor _).trans_eq' _),
    { rw one_le_div (zero_lt_two' ℝ),
      exact_mod_cast hn'' },
    rw [div_div, div_eq_mul_inv, mul_comm],
    norm_num },
  have h₅ : 0 < 2 ^ f₂ k * γ ^ l * (1 - γ) ^ (red_steps γ k l ini).card *
    (beta γ k l ini / γ) ^ (density_steps γ k l ini).card := by positivity,
  replace hn := hn.trans' (mul_le_mul_of_nonneg_left hc (exp_pos _).le),
  replace hgk := (mul_le_mul_of_nonneg_left this h₅.le).trans hgk,
  rw [←mul_assoc] at hgk,
  replace hgk := (mul_le_mul_of_nonneg_left hn (mul_nonneg h₅.le (by norm_num1))).trans hgk,
  replace hgk := hgk.trans hfk,
  rw [sub_add, sub_sub, sub_eq_add_neg (f₁ k), rpow_add two_pos],
  refine (mul_le_mul_of_nonneg_right hgk (rpow_pos_of_pos two_pos _).le).trans' _,
  simp only [mul_assoc, mul_left_comm _ (exp (-δ * k))],
  refine mul_le_mul_of_nonneg_left _ (exp_pos _).le,
  simp only [mul_left_comm _ ((_ / γ) ^ _)],
  rw mul_comm,
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  simp only [mul_left_comm _ ((1 - γ) ^ (_ : ℝ))],
  rw rpow_add hγ₁',
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  simp only [mul_left_comm _ (γ ^ (_ : ℝ))],
  simp only [mul_left_comm _ (γ ^ (_ : ℕ))],
  rw [rpow_neg hγ₀'.le, rpow_nat_cast, rpow_nat_cast, mul_inv_cancel_left₀ (pow_pos hγ₀' _).ne',
    mul_left_comm],
  refine le_mul_of_one_le_right (pow_nonneg hγ₁'.le _) _,
  rw [←rpow_add two_pos, ←rpow_add two_pos, ←rpow_add two_pos],
  simp only [←add_assoc, neg_add, neg_sub],
  ring_nf,
  rw rpow_zero
end

lemma nine_three_part_two :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ γ₀ : ℝ, 0 < γ₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, ∀ γ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 5 → l ≤ k →
  ∀ δ : ℝ, δ = min (1 / 200) (γ / 20) → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), 1 / 4 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
  exp (- δ * k) * (k + l).choose l ≤ n →
  γ * (k - (red_steps γ k l ini).card) ≤
    (beta γ k l ini * (red_steps γ k l ini).card / (1 - γ)) * log (γ / beta γ k l ini) +
      δ * k + f k :=
begin
  have hμ₁ : (1 / 5 : ℝ) < 1 := by norm_num1,
  have hp₀ : (0 : ℝ) < 1 / 4 := by norm_num1,
  obtain ⟨f, hf, hf'⟩ := nine_three_part_one,
  refine ⟨λ k, log 2 * f k + 7 / (1 - 1 / 5) * (k ^ (15 / 16 : ℝ) * (3 * log k)),
    _, _⟩,
  { clear hf',
    refine is_o.add (is_o.const_mul_left hf _) _,
    refine is_o.const_mul_left _ _,
    suffices : (λ k : ℝ, k ^ (15 / 16 : ℝ) * (3 * log k)) =o[at_top] id,
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    simp only [mul_left_comm _ (3 : ℝ)],
    refine is_o.const_mul_left _ _,
    simp only [mul_comm _ (log _)],
    refine ((is_o_log_rpow_at_top (by norm_num : (0 : ℝ) < 1 / 16)).mul_is_O
      (is_O_refl _ _)).congr' eventually_eq.rfl _,
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk,
    rw [←rpow_add hk],
    norm_num },
  intros γ₀ hγ₀,
  filter_upwards [hf' γ₀ hγ₀, eight_five γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0), beta_le_μ γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀,
    beta_pos γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀, one_div_sq_le_beta γ₀ (1 / 5) (1 / 4) hγ₀ hμ₁ hp₀] with
    l h₁ h₈₅ hk₀ hβμ hβ₀ hβk
    k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn,
  clear hf',
  specialize h₁ k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn,
  specialize h₈₅ k hlk γ hγl hγu n χ hχ ini hini,
  specialize hβμ k hlk γ hγl hγu n χ ini hini,
  specialize hβ₀ k hlk γ hγl hγu n χ ini hini,
  specialize hβk k hlk γ hγl hγu n χ ini hini,
  have hγ₁ : γ < 1 := by linarith only [hγu],
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl,
  have : exp (γ * (k - (red_steps γ k l ini).card)) ≤
    (1 - γ) ^ (- k + (red_steps γ k l ini).card : ℝ),
  { rw [exp_mul, neg_add_eq_sub, ←neg_sub (k : ℝ), rpow_neg (sub_nonneg_of_le hγ₁.le),
      ←inv_rpow (sub_nonneg_of_le hγ₁.le)],
    refine rpow_le_rpow (exp_pos _).le (exp_le_one_sub_inv hγ₁) (sub_nonneg_of_le _),
    rw nat.cast_le,
    exact four_four_red _ (hk₀ _ hlk).ne' (hk₀ _ le_rfl).ne' hχ _ },
  rw mul_right_comm at h₁,
  clear hn hδ hχ hini hn' hγ,
  replace h₁ := (mul_le_mul_of_nonneg_left this (by positivity)).trans h₁,
  rw [neg_mul, real.exp_neg, ←inv_div, inv_pow, ←mul_inv, inv_mul_eq_div, div_le_iff,
    ←le_log_iff_exp_le, log_mul, log_mul, log_exp, log_pow, log_rpow two_pos, mul_comm (f k)] at h₁,
  rotate,
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  refine h₁.trans _,
  rw [add_rotate, add_left_comm, add_assoc, add_assoc, add_le_add_iff_left, add_le_add_iff_left],
  have : 0 ≤ log (γ / beta γ k l ini),
  { refine log_nonneg _,
    rwa one_le_div hβ₀ },
  refine (mul_le_mul_of_nonneg_right h₈₅ this).trans _,
  rw [add_comm, add_mul, div_mul_eq_mul_div _ (1 - γ), mul_assoc (beta γ k l ini / _),
    div_mul_eq_mul_div (beta γ k l ini), ←mul_assoc, ←mul_assoc],
  refine add_le_add _ _,
  swap,
  { refine div_le_div_of_le_left (mul_nonneg (by positivity) this) (sub_pos_of_lt hγ₁) _,
    exact sub_le_sub_left hβμ _ },
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw [log_div hγ₀'.ne' hβ₀.ne', bit1, add_comm, one_add_mul, sub_eq_add_neg],
  refine add_le_add (log_le_log_of_le hγ₀' _) _,
  { refine hγ₁.le.trans _,
    rw nat.one_le_cast,
    exact hk₀ k hlk },
  rw [←nat.cast_two, ←log_pow, neg_le, ←log_inv, ←one_div],
  refine log_le_log_of_le _ hβk,
  specialize hk₀ k hlk,
  positivity
end

lemma mul_log_ineq {x : ℝ} (hx : 0 < x) :
  - x * log x ≤ exp (-1) :=
begin
  have := add_one_le_exp (-log x - 1),
  rwa [sub_add_cancel, sub_eq_add_neg, real.exp_add, real.exp_neg, exp_log hx, inv_mul_eq_div,
    le_div_iff hx, mul_comm, mul_neg, ←neg_mul] at this,
end

lemma mul_log_ineq_special {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
  x * log (c / x) ≤ c / exp 1 :=
begin
  have := mul_log_ineq (div_pos hx hc),
  rwa [neg_mul, ←mul_neg, ←log_inv, inv_div, div_mul_eq_mul_div, div_le_iff hc, real.exp_neg,
    inv_mul_eq_div] at this,
end

lemma nine_three_part_three (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, ∀ γ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 5 → l ≤ k →
  ∀ δ : ℝ, δ = min (1 / 200) (γ / 20) → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), 1 / 4 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
  exp (- δ * k) * (k + l).choose l ≤ n →
  (k : ℝ) * (1 - δ / γ) * (1 + (1 / (exp 1 * (1 - γ))))⁻¹ + f k ≤ (red_steps γ k l ini).card :=
begin
  have hμ₁ : (1 / 5 : ℝ) < 1 := by norm_num1,
  have hp₀ : (0 : ℝ) < 1 / 4 := by norm_num1,
  obtain ⟨f, hf, hf'⟩ := nine_three_part_two,
  refine ⟨λ k, -((1 / γ₀) * |f k|), _, _⟩,
  { rw is_o_neg_left,
    refine is_o.const_mul_left _ _,
    exact hf.abs_left },
  filter_upwards [hf' γ₀ hγ₀, beta_pos γ₀ _ _ hγ₀ hμ₁ hp₀] with l hl hβ
    k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn,
  clear hf',
  specialize hl k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn,
  specialize hβ k hlk γ hγl hγu n χ ini hini,
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl,
  have hγ₁' : γ < 1 := hγu.trans_lt (by norm_num),
  rw [mul_div_assoc, mul_right_comm, add_assoc, ←sub_le_iff_le_add] at hl,
  replace hl := hl.trans (mul_le_mul_of_nonneg_right (mul_log_ineq_special hγ₀' hβ)
    (div_nonneg (nat.cast_nonneg _) (sub_pos_of_lt hγ₁').le)),
  have : 0 ≤ 1 / (exp 1 * (1 - γ)),
  { rw one_div,
    exact inv_nonneg_of_nonneg (mul_nonneg (exp_pos _).le (sub_pos_of_lt hγ₁').le) },
  rw [mul_div_assoc', ←div_mul_eq_mul_div, div_div, mul_sub, sub_sub, add_comm, ←sub_sub,
    sub_le_iff_le_add, ←add_mul, div_eq_mul_inv, ←mul_add_one, ←one_div, add_comm _ (1 : ℝ),
    ←div_le_iff', ←div_div, sub_div, div_eq_mul_inv, mul_div_cancel_left, add_div, mul_comm δ,
    mul_div_assoc, ←sub_sub, ←mul_one_sub, sub_mul, div_mul_eq_mul_div, mul_div_assoc] at hl,
  { refine hl.trans' (sub_le_sub_left _ _),
    rw [mul_comm (1 / γ₀)],
    refine mul_le_mul (le_abs_self _) (div_le_div zero_le_one _ hγ₀ hγl) _ (abs_nonneg _),
    { exact inv_le_one (le_add_of_nonneg_right this) },
    refine div_nonneg _ hγ₀'.le,
    positivity },
  { exact hγ₀'.ne' },
  { positivity },
end

lemma it_keeps_showing_up {γ : ℝ} (hγ : γ ≤ 1) :
  0 < 1 + 1 / (exp 1 * (1 - γ)) :=
add_pos_of_pos_of_nonneg zero_lt_one
  (one_div_nonneg.2 (mul_nonneg (exp_pos _).le (sub_nonneg_of_le hγ)))

lemma rearranging_more {c γ : ℝ} (hγl : 0.1 ≤ γ) (hγu : γ ≤ 0.2) (hc : 0 < c) (hc' : c < 0.95) :
  c < (1 - 1 / (200 * γ)) * (1 + (1 / (exp 1 * (1 - γ))))⁻¹ ↔
    1 / ((1 - 1 / (200 * γ)) / c - 1) / (1 - γ) < exp 1 :=
begin
  have hγ₀ : 0 < γ := hγl.trans_lt' (by norm_num1),
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1),
  rw [←div_eq_mul_inv, lt_div_iff (it_keeps_showing_up hγ₁.le), ←lt_div_iff' hc,
    ←lt_sub_iff_add_lt', one_div_lt, ←div_lt_iff (sub_pos_of_lt hγ₁)],
  { exact mul_pos (exp_pos _) (sub_pos_of_lt hγ₁) },
  rw [sub_pos, lt_div_iff hc, one_mul],
  refine hc'.trans_le _,
  rw [le_sub_comm, ←div_div, div_le_iff hγ₀, ←div_le_iff'],
  { exact hγl.trans' (by norm_num1) },
  norm_num1
end

lemma numerics_one_middle_aux {γ : ℝ} (hγu : γ = 1 / 10) :
  0.67435 < (1 - 1 / 20) * (1 + (1 / (exp 1 * (1 - γ))))⁻¹ :=
begin
  subst hγu,
  rw [←div_lt_iff', lt_inv _ (it_keeps_showing_up _), ←lt_sub_iff_add_lt', one_div_lt, ←div_lt_iff],
  { refine exp_one_gt_d9.trans_le' _,
    norm_num1 },
  { norm_num1 },
  { exact mul_pos (exp_pos _) (by norm_num1) },
  all_goals { norm_num1 },
end

lemma numerics_one_left {γ δ : ℝ} (hγl : 0 < γ) (hγu : γ ≤ 1 / 10)
  (hδ : δ = γ / 20) :
  0.67435 < (1 - δ / γ) * (1 + (1 / (exp 1 * (1 - γ))))⁻¹ :=
begin
  rw [hδ, div_div, mul_comm (20 : ℝ), ←div_div, div_self hγl.ne'],
  refine (numerics_one_middle_aux rfl).trans_le _,
  refine mul_le_mul_of_nonneg_left _ (by norm_num1),
  refine inv_le_inv_of_le (it_keeps_showing_up (by linarith only [hγu])) _,
  refine add_le_add_left (one_div_le_one_div_of_le (mul_pos (exp_pos _) (by norm_num1)) _) _,
  refine mul_le_mul_of_nonneg_left _ (exp_pos _).le,
  linarith only [hγu]
end

lemma concave_on.mul {f g : ℝ → ℝ} {s : set ℝ} (hf : concave_on ℝ s f) (hg : concave_on ℝ s g)
  (hf' : monotone_on f s) (hg' : antitone_on g s)
  (hf'' : ∀ x ∈ s, 0 ≤ f x) (hg'' : ∀ x ∈ s, 0 ≤ g x) : concave_on ℝ s (λ x, f x * g x) :=
begin
  refine linear_order.concave_on_of_lt hf.1 _,
  intros x hx y hy hxy a b ha hb hab,
  replace hg := hg.2 hx hy ha.le hb.le hab,
  refine (mul_le_mul (hf.2 hx hy ha.le hb.le hab) hg (add_nonneg (smul_nonneg ha.le (hg'' _ hx))
    (smul_nonneg hb.le (hg'' _ hy))) (hf'' _ (hf.1 hx hy ha.le hb.le hab))).trans' _,
  have : b = 1 - a, { rwa eq_sub_iff_add_eq' },
  subst this,
  simp only [smul_eq_mul],
  suffices : 0 ≤ a * (1 - a) * (g x - g y) * (f y - f x),
  { nlinarith only [this] },
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg_of_le (hg' hx hy hxy.le)))
    (sub_nonneg_of_le (hf' hx hy hxy.le)),
end

-- lemma convex_on_sub_const {s : set ℝ} {c : ℝ} (hs : convex ℝ s) : concave_on ℝ s (λ x, x - c) :=
-- (convex_on_id hs).sub (concave_on_const _ hs)

lemma convex_on.const_mul {c : ℝ} {s : set ℝ} {f : ℝ → ℝ} (hf : convex_on ℝ s f) (hc : 0 ≤ c) :
  convex_on ℝ s (λ x, c * f x) :=
⟨hf.1, λ x hx y hy a b ha hb hab, (mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc).trans_eq
  (by simp only [smul_eq_mul]; ring_nf)⟩

lemma concave_on.const_mul {c : ℝ} {s : set ℝ} {f : ℝ → ℝ} (hf : concave_on ℝ s f) (hc : 0 ≤ c) :
  concave_on ℝ s (λ x, c * f x) :=
⟨hf.1, λ x hx y hy a b ha hb hab, (mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc).trans_eq'
  (by simp only [smul_eq_mul]; ring_nf)⟩

lemma strict_convex_on.const_mul_neg {c : ℝ} {s : set ℝ} {f : ℝ → ℝ} (hf : strict_convex_on ℝ s f)
  (hc : c < 0) :
  strict_concave_on ℝ s (λ x, c * f x) :=
⟨hf.1, λ x hx y hy hxy a b ha hb hab, (mul_lt_mul_of_neg_left (hf.2 hx hy hxy ha hb hab)
  hc).trans_eq' (by simp only [smul_eq_mul]; ring_nf)⟩

lemma strict_convex_on.const_mul {c : ℝ} {s : set ℝ} {f : ℝ → ℝ} (hf : strict_convex_on ℝ s f)
  (hc : 0 < c) :
  strict_convex_on ℝ s (λ x, c * f x) :=
⟨hf.1, λ x hx y hy hxy a b ha hb hab, (mul_lt_mul_of_pos_left (hf.2 hx hy hxy ha hb hab)
  hc).trans_eq (by simp only [smul_eq_mul]; ring_nf)⟩

lemma convex_on_inv : convex_on ℝ (set.Ioi (0 : ℝ)) (λ x, x⁻¹) :=
convex_on.congr (convex_on_zpow (-1)) (by simp)

lemma convex_on_one_div : convex_on ℝ (set.Ioi (0 : ℝ)) (λ x, 1 / x) :=
convex_on.congr (convex_on_zpow (-1)) (by simp)

lemma quadratic_is_concave {a b c : ℝ} (ha : 0 < a) :
  strict_convex_on ℝ set.univ (λ x, a * x ^ 2 + b * x + c) :=
begin
  have : ∀ x, a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - (a * (b / (2 * a)) ^ 2 - c),
  { intro x,
    rw [←sub_add, ←mul_sub, add_left_inj, add_sq, add_sub_cancel, mul_add, mul_div_assoc',
      mul_div_assoc', mul_assoc, mul_left_comm, ←mul_assoc, mul_div_cancel_left, mul_comm x],
    exact mul_ne_zero (by positivity) ha.ne' },
  simp only [this],
  refine strict_convex_on.sub_concave_on _ (concave_on_const _ convex_univ),
  refine strict_convex_on.const_mul _ ha,
  simpa using (even.strict_convex_on_pow even_two two_pos.ne').translate_left (b / (2 * a)),
end

lemma rearranging {c γ : ℝ} (hγ₀ : 0 < γ) (hγu : γ ≤ 0.2) :
  c < (1 - 1 / (200 * γ)) * (1 + (1 / (exp 1 * (1 - γ))))⁻¹ ↔
    (1 - c) * γ ^ 2 + (c * (1 + 1 / exp 1) - (1 + 1 / 200)) * γ + 1 / 200 < 0 :=
begin
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1),
  rw [←div_eq_mul_inv, ←div_div, one_sub_div hγ₀.ne', ←div_div, one_add_div (sub_pos_of_lt hγ₁).ne',
    div_div_eq_mul_div, div_mul_eq_mul_div, div_div, sub_add_eq_add_sub, sub_mul, mul_one_sub,
    mul_one_sub, lt_div_iff, mul_sub, sub_sub, add_sub_assoc', ←sub_add, sub_add_eq_add_sub,
    ←one_add_mul, mul_sub, lt_sub_iff_add_lt, mul_left_comm, sub_eq_add_neg, ←neg_mul, add_assoc,
    ←add_assoc ((-c) * _), ←add_one_mul, neg_add_eq_sub, ←sub_neg, add_comm, ←sq, ←add_sub,
    mul_comm γ, ←sub_mul, add_right_comm],
  refine mul_pos hγ₀ (sub_pos_of_lt (hγ₁.trans_le (le_add_of_nonneg_right _))),
  rw one_div_nonneg,
  exact (exp_pos _).le
end

-- lhs is 39/40 * (1 + 5 / (4 e))
lemma numerics_one {γ δ : ℝ} (hγl : 0 < γ) (hγu : γ ≤ 1 / 5) (hδ : δ = min (1 / 200) (γ / 20)) :
  0.6678 < (1 - δ / γ) * (1 + (1 / (exp 1 * (1 - γ))))⁻¹ :=
begin
  cases le_total γ 0.1 with hγl' hγl',
  { refine (numerics_one_left hγl hγl' _).trans_le' (by norm_num1),
    rw [hδ, min_eq_right_iff],
    refine (div_le_div_of_le (by norm_num1) hγl').trans_eq _,
    norm_num1 },
  rw [hδ, min_eq_left, div_div],
  swap,
  { linarith only [hγl'] },
  rw rearranging hγl hγu,
  set c : ℝ := 0.6678 with hc',
  let f : ℝ → ℝ := λ x, (1 - c) * x ^ 2 + (c * (1 + 1 / exp 1) - (1 + 1 / 200)) * x + 1 / 200,
  have hc : 0 < 1 - c, { rw hc', norm_num },
  have hf : strict_convex_on ℝ set.univ f := quadratic_is_concave hc,
  change f γ < 0,
  have hfive : (1 / 10 : ℝ) ≤ 1 / 5 := hγl'.trans hγu,
  have h₁ : f (1 / 10) < 0,
  { rw ←rearranging _ hfive,
    convert (numerics_one_middle_aux rfl).trans_le' _ using 3,
    { norm_num1 },
    { norm_num1 },
    { norm_num1 } },
  have h₂ : f (1 / 5) < 0,
  { rw [←rearranging (hγl.trans_le hγu) le_rfl, hc', rearranging_more hfive le_rfl],
    { refine exp_one_gt_d9.trans_le' _,
      norm_num1 },
    { norm_num1 },
    { norm_num1 } },
  have : convex_on ℝ (set.Icc (1 / 10 : ℝ) (1 / 5)) f := hf.convex_on.subset (set.subset_univ _)
    (convex_Icc _ _),
  have hγ : γ ∈ segment ℝ (1 / 10 : ℝ) (1 / 5),
  { rw segment_eq_Icc hfive,
    exact ⟨hγl', hγu⟩ },
  have := convex_on.le_on_segment this _ _ hγ,
  rotate,
  { rwa set.left_mem_Icc },
  { rwa set.right_mem_Icc },
  refine this.trans_lt _,
  rw max_lt_iff,
  exact ⟨h₁, h₂⟩
end

lemma nine_three (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  l ≤ k →
  ∀ γ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 5 →
  ∀ δ : ℝ, δ = min (1 / 200) (γ / 20) →
  ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), 1 / 4 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
  exp (- δ * k) * (k + l).choose l ≤ n →
  (2 / 3 : ℝ) * k ≤ (red_steps γ k l ini).card :=
begin
  obtain ⟨f, hf, hf'⟩ := nine_three_part_three γ₀ hγ₀,
  have := hf.bound (by norm_num1 : (0 : ℝ) < 0.001),
  filter_upwards [hf', top_adjuster (eventually_gt_at_top 0),
    top_adjuster (hf.bound (by norm_num1 : (0 : ℝ) < 0.001))] with
    l h9 hk₀ herr
    k hlk γ hγ hγl hγu δ hδ n χ hχ ini hini hn' hn,
  clear hf',
  have hl₀ : 0 < l := hk₀ l le_rfl,
  specialize h9 k γ hγ hγl hγu hlk δ hδ n χ hχ ini hini hn' hn,
  specialize herr k hlk,
  rw [norm_eq_abs, norm_coe_nat, abs_le] at herr,
  refine h9.trans' _,
  rw [mul_rotate],
  refine (add_le_add_left herr.1 _).trans' _,
  rw [←neg_mul, ←add_mul],
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  linarith only [numerics_one (hγ₀.trans_le hγl) hγu hδ],
end

lemma yael_two {n k a : ℕ} :
  n.asc_factorial (k + a) = (n + a).asc_factorial k * n.asc_factorial a :=
begin
  induction a with a ih,
  { simp },
  rw [nat.add_succ, nat.asc_factorial_succ, nat.asc_factorial_succ, mul_left_comm, ←mul_assoc,
    nat.add_succ n a, nat.succ_asc_factorial (n + a), ih, mul_assoc, add_comm k a, ←add_assoc],
end

lemma asc_mul_asc {a b c : ℕ} :
  a.asc_factorial b * (a + b).asc_factorial c = a.asc_factorial c * (a + c).asc_factorial b :=
by rw [mul_comm, ←yael_two, mul_comm, ←yael_two, add_comm]

lemma asc_div_asc_const_right' {a b c : ℕ} :
  (a.asc_factorial b : ℝ) / (a + c).asc_factorial b = a.asc_factorial c / (a + b).asc_factorial c :=
begin
  rw [div_eq_div_iff, ←nat.cast_mul, asc_mul_asc, nat.cast_mul],
  { positivity },
  { positivity },
end

lemma asc_div_asc_const_right {a b c : ℕ} :
  ((a + c).asc_factorial b : ℝ) / a.asc_factorial b = (a + b).asc_factorial c / a.asc_factorial c :=
begin
  rw [div_eq_div_iff, mul_comm, ←nat.cast_mul, asc_mul_asc, nat.cast_mul, mul_comm],
  { positivity },
  { positivity },
end

-- d = a + c
-- a = d - c
lemma asc_div_asc_const_right_sub' {b c d : ℕ} (h : c ≤ d) :
  ((d - c).asc_factorial b : ℝ) / d.asc_factorial b =
    (d - c).asc_factorial c / (d - c + b).asc_factorial c :=
begin
  obtain ⟨a, rfl⟩ := exists_add_of_le h,
  rw [add_tsub_cancel_left, add_comm, asc_div_asc_const_right'],
end

lemma choose_ratio {l k t : ℕ} (h : t ≤ k) :
  ((k + l - t).choose l : ℝ) / ((k + l).choose l) =
    ∏ (i : ℕ) in range t, (k - i) / (k + l - i) :=
begin
  rw [nat.choose_eq_desc_factorial_div_factorial, nat.choose_eq_desc_factorial_div_factorial,
    nat.cast_div_div_div_cancel_right, ←tsub_add_eq_add_tsub h,
    nat.add_desc_factorial_eq_asc_factorial, nat.add_desc_factorial_eq_asc_factorial,
    asc_div_asc_const_right_sub' h, ←nat.add_desc_factorial_eq_asc_factorial, nat.sub_add_cancel h,
    ←nat.add_desc_factorial_eq_asc_factorial, tsub_add_eq_add_tsub h, nat.sub_add_cancel,
    cast_desc_factorial_eq_prod, cast_desc_factorial_eq_prod, ←prod_div_distrib],
  { simp },
  { exact le_add_right h },
  { exact nat.factorial_dvd_desc_factorial _ _ },
  { exact nat.factorial_dvd_desc_factorial _ _ },
end

lemma fact_d_two_part_one {l k t : ℕ} (h : t ≤ k) :
  ((k + l - t).choose l : ℝ) / ((k + l).choose l) =
    (k / (k + l)) ^ t * ∏ i in range t, (1 - i * l / (k * (k + l - i))) :=
begin
  have : ((k : ℝ) / (k + l)) ^ t = ∏ i in range t, (k / (k + l)),
  { simp },
  rw [this, choose_ratio h, ←prod_mul_distrib],
  refine prod_congr rfl _,
  intros i hi,
  rw mem_range at hi,
  have hik : i < k := hi.trans_le h,
  have : 0 < k := pos_of_gt hik,
  have : 0 < k - i := nat.sub_pos_of_lt hik,
  rw [one_sub_div, mul_div_assoc', div_mul_eq_mul_div, mul_div_assoc,
    mul_div_mul_left, mul_sub, mul_comm _ (i : ℝ), sub_sub, ←mul_add, ←sub_mul, mul_div_cancel],
  { positivity },
  { positivity },
  rw [←sub_add_eq_add_sub, ←nat.cast_sub hik.le],
  positivity,
end

lemma fact_d_two_part_two {l k t : ℕ} (h : t ≤ k) :
  ∏ i in range t, (1 - i * l / (k * (k + l - i)) : ℝ) ≤
    exp (- l / (k * (k + l)) * ∑ i in range t, i) :=
begin
  rw [mul_sum, real.exp_sum],
  refine finset.prod_le_prod _ _,
  { intros i hi,
    rw [mem_range] at hi,
    have hik : i < k := hi.trans_le h,
    have : 0 < k := pos_of_gt hik,
    have : 0 < k - i := nat.sub_pos_of_lt hik,
    rw [sub_nonneg, ←sub_add_eq_add_sub, ←nat.cast_sub hik.le],
    refine div_le_one_of_le _ (by positivity),
    rw [←nat.cast_add, ←nat.cast_mul, ←nat.cast_mul, nat.cast_le],
    exact nat.mul_le_mul hik.le (nat.le_add_left _ _) },
  intros i hi,
  rw mem_range at hi,
  refine (add_one_le_exp _).trans' _,
  rw [neg_div, neg_mul, neg_add_eq_sub, sub_le_sub_iff_left, mul_comm, mul_div_assoc'],
  have hik : i < k := hi.trans_le h,
  have : 0 < k := pos_of_gt hik,
  have : 0 < k - i := nat.sub_pos_of_lt hik,
  refine div_le_div_of_le_left (by positivity) _ (mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _)),
  { rw [←sub_add_eq_add_sub, ←nat.cast_sub hik.le],
    positivity },
  simp,
end

lemma d_two {l k t : ℕ} {γ : ℝ} (ht : 0 < k) (h : t ≤ k) (hγ : γ = l / (k + l)):
  ((k + l - t).choose l : ℝ) ≤
    exp (- γ * (t * (t - 1)) / (2 * k)) * (1 - γ) ^ t * (k + l).choose l :=
begin
  have hγ₀ : 0 ≤ γ,
  { rw [hγ], positivity },
  have hγ₁ : γ ≤ 1,
  { rw [hγ], refine div_le_one_of_le (by simp) (by positivity) },
  rw [←div_le_iff, fact_d_two_part_one h],
  swap,
  { rw nat.cast_pos,
    exact nat.choose_pos (nat.le_add_left _ _) },
  rw [mul_comm, hγ, one_sub_div, add_sub_cancel],
  swap,
  { positivity },
  refine mul_le_mul_of_nonneg_right ((fact_d_two_part_two h).trans _) (by positivity),
  rw [exp_le_exp, ←div_div _ (2 : ℝ), mul_div_assoc, ←div_mul_eq_mul_div, neg_div, neg_div, div_div,
    neg_mul, neg_mul, mul_comm (k : ℝ), neg_le_neg_iff, ←nat.cast_sum, sum_range_id,
    ←nat.choose_two_right, nat.cast_choose_two],
end

lemma nine_six :
  ∀ (l k t : ℕ) (γ : ℝ), 0 < k → t ≤ k → γ = l / (k + l) →
  exp (-1) * (1 - γ) ^ (-t : ℝ) * exp (γ * t ^ 2 / (2 * k)) * (k + l - t).choose l ≤
    (k + l).choose l :=
begin
  intros l k t γ hk htk hγ,
  have hγ₀ : 0 ≤ γ,
  { rw [hγ], positivity },
  have hγ₁ : γ < 1,
  { rw [hγ, div_lt_one],
    { simpa only [lt_add_iff_pos_left, nat.cast_pos] using hk },
    { positivity } },
  refine (mul_le_mul_of_nonneg_left (d_two hk htk hγ) _).trans _,
  { exact mul_nonneg (mul_nonneg (exp_pos _).le
      (rpow_nonneg_of_nonneg (sub_pos_of_lt hγ₁).le _)) (exp_pos _).le },
  rw [←mul_assoc, mul_right_comm (exp _ : ℝ), ←real.exp_add, mul_mul_mul_comm, ←real.exp_add,
    add_assoc, ←add_div, ←rpow_nat_cast _ t, ←rpow_add (sub_pos_of_lt hγ₁), neg_add_self, rpow_zero,
    mul_one, neg_mul, ←sub_eq_add_neg, ←mul_sub, sq, ←mul_sub, sub_sub_cancel, mul_one],
  refine mul_le_of_le_one_left (nat.cast_nonneg _) _,
  rw exp_le_one_iff,
  rw [neg_add_le_iff_le_add, add_zero],
  refine div_le_one_of_le _ (by positivity),
  exact mul_le_mul (hγ₁.le.trans (by norm_num1)) (nat.cast_le.2 htk) (nat.cast_nonneg _)
    (by norm_num1),
end

lemma nine_five_density :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ γ₀ : ℝ, 0 < γ₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ η : ℝ, γ₀ ≤ γ → 0 ≤ η → 1 / 2 ≤ 1 - γ - η →
  ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), 1 - γ - η ≤ ini.p →
  γ ≤ 1 / 2 → γ < 1 → l ≤ k → 1 / 2 ≤ ini.p →
  exp (f k) *
    (1 - γ - η) ^ (γ * (red_steps γ k l ini).card / (1 - γ)) *
    (1 - γ - η) ^ (red_steps γ k l ini).card
    ≤ ini.p ^ ((red_steps γ k l ini).card + (density_steps γ k l ini).card) :=
begin
  have hp₀ : 0 < (1 / 2 : ℝ) := by norm_num1,
  have hμ₁ : (1 / 2 : ℝ) < 1 := by norm_num1,
  refine ⟨λ k, - (log 2) * ((7 / (1 - 1 / 2)) * k ^ (15 / 16 : ℝ)), _, _⟩,
  { refine is_o.const_mul_left _ _,
    refine is_o.const_mul_left _ _,
    suffices : (λ k : ℝ, k ^ (15 / 16 : ℝ)) =o[at_top] id,
    { exact is_o.comp_tendsto this tendsto_coe_nat_at_top_at_top },
    simpa using is_o_rpow_rpow (by norm_num1 : 15 / 16 < (1 : ℝ)) },
  intros γ₀ hγ₀,
  filter_upwards [eight_five γ₀ (1 / 2) (1 / 2) hγ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_at_top 0),
    beta_le_μ γ₀ _ _ hγ₀ hμ₁ hp₀ ] with
    l h₈₅ hk₀ hβμ
    k γ η hγl hη hγη n χ hχ ini hini hγu hγ₁ hlk hp₀',
  specialize h₈₅ k hlk γ hγl hγu n χ hχ ini hp₀',
  specialize hβμ k hlk γ hγl hγu n χ ini hp₀',
  have hst : ((density_steps γ k l ini).card : ℝ) ≤ γ / (1 - γ) * (red_steps γ k l ini).card +
    7 / (1 - 1 / 2) * k ^ (15 / 16 : ℝ),
  { refine h₈₅.trans (add_le_add_right (mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _)) _),
    exact div_le_div (hγ₀.le.trans hγl) hβμ (sub_pos_of_lt hγ₁) (sub_le_sub_left hβμ _) },
  have hp₀'' : 0 < ini.p := hp₀.trans_le hp₀',
  rw [←log_inv, ←rpow_def_of_pos, add_comm, ←one_div, pow_add],
  swap,
  { norm_num1 },
  refine mul_le_mul _ (pow_le_pow_of_le_left (hp₀.le.trans hγη) hini _) (pow_nonneg
    (hp₀.le.trans hγη) _) (pow_nonneg col_density_nonneg _),
  rw [←rpow_nat_cast, mul_comm],
  refine (rpow_le_rpow_of_exponent_ge hp₀'' col_density_le_one hst).trans' _,
  rw [div_mul_eq_mul_div γ, rpow_add hp₀''],
  refine mul_le_mul (rpow_le_rpow (hp₀.le.trans hγη) hini _) (rpow_le_rpow hp₀.le hp₀'
    (by positivity)) (by positivity) (rpow_nonneg_of_nonneg hp₀''.le _),
  exact div_nonneg (mul_nonneg (hγ₀.le.trans hγl) (nat.cast_nonneg _)) (sub_pos_of_lt hγ₁).le,
end

lemma nine_five :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ γ₀ : ℝ, 0 < γ₀ →
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  l ≤ k →
  ∀ γ δ η : ℝ, γ = l / (k + l) → γ₀ ≤ γ → 0 ≤ δ → δ ≤ γ / 20 → 0 ≤ η → 1 / 2 ≤ 1 - γ - η →
  ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ (ini : book_config χ), 1 - γ - η ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card →
  exp (- δ * k) * (k + l).choose l ≤ n →
  real.exp (- δ * k + f k) *
    (1 - γ - η) ^ (γ * (red_steps γ k l ini).card / (1 - γ)) *
      ((1 - γ - η) / (1 - γ)) ^ (red_steps γ k l ini).card *
        exp (γ * (red_steps γ k l ini).card ^ 2 / (2 * k)) *
          (k - (red_steps γ k l ini).card + l).choose l
    ≤ (end_state γ k l ini).Y.card :=
begin
  have hp₀ : 0 < (1 / 2 : ℝ) := by norm_num1,
  have hμ₁ : (1 / 2 : ℝ) < 1 := by norm_num1,
  obtain ⟨f₁, hf₁, hf₁'⟩ := six_one _ hp₀,
  obtain ⟨f₂, hf₂, hf₂'⟩ := nine_five_density,
  refine ⟨λ k, log 2 * (f₁ k + -2) + (-1) + f₂ k, _, _⟩,
  { refine is_o.add _ hf₂,
    refine is_o.add (is_o.const_mul_left (is_o.add hf₁ _) _) _,
    { exact (is_o_const_id_at_top _).comp_tendsto tendsto_coe_nat_at_top_at_top },
    { exact (is_o_const_id_at_top _).comp_tendsto tendsto_coe_nat_at_top_at_top } },
  clear hf₁ hf₂,
  intros γ₀ hγ₀,
  filter_upwards [eight_five γ₀ (1 / 2) (1 / 2) hγ₀ hμ₁ hp₀, hf₁' γ₀ _ hγ₀ hμ₁,
    hf₂' γ₀ hγ₀,
    nine_three_lower_n γ₀ hγ₀,
    top_adjuster (eventually_gt_at_top 0),
    beta_le_μ γ₀ _ _ hγ₀ hμ₁ hp₀,
    beta_pos γ₀ _ _ hγ₀ hμ₁ hp₀] with
    l h₈₅ h₆₁ hf₂ hn'' hk₀ hβμ hβ₀
    k hlk γ δ η hγ hγl hδ hδu hη hγη n χ hχ ini hini hn' hn,
  clear hf₁' hf₂',
  have hγu : γ ≤ 1 / 2,
  { linarith only [hγη, hη] },
  have hγ₁ : γ < 1 := hγu.trans_lt hμ₁,
  have hl₀ : 0 < l := hk₀ l le_rfl,
  have hp₀' : 1 / 2 ≤ ini.p := hγη.trans hini,
  specialize h₈₅ k hlk γ hγl hγu n χ hχ ini hp₀',
  specialize h₆₁ k hlk γ hγl hγu n χ hχ ini hp₀',
  specialize hn'' k γ hγ hγl hγ₁ hlk δ hδu n hn,
  specialize hβμ k hlk γ hγl hγu n χ ini hp₀',
  specialize hβ₀ k hlk γ hγl hγu n χ ini hp₀',
  specialize hf₂ k γ η hγl hη hγη n χ hχ ini hini hγu hγ₁ hlk hp₀',
  have htk : (red_steps γ k l ini).card ≤ k :=
    four_four_red _ (hk₀ _ hlk).ne' (hk₀ _ le_rfl).ne' hχ _,
  have : 2 ^ (-2 : ℝ) * (n : ℝ) ≤ ini.Y.card,
  { refine (nat.cast_le.2 hn').trans' ((ge_floor _).trans_eq' _),
    { rw [one_le_div (zero_lt_two' ℝ)],
      rw [←@nat.cast_le ℝ, nat.cast_two] at hn'',
      exact hn'' },
    rw [div_div, div_eq_mul_inv, mul_comm, ←sq, rpow_neg zero_lt_two.le, rpow_two] },
  replace this := (mul_le_mul_of_nonneg_left hn (by positivity)).trans this,
  rw [←mul_assoc] at this,
  have h₉₆ := nine_six l k (red_steps γ k l ini).card γ (hk₀ k hlk) htk hγ,
  replace this := (mul_le_mul_of_nonneg_left h₉₆ (by positivity)).trans this,
  clear h₉₆,
  have hp₀'' : 0 < ini.p := hp₀.trans_le hp₀',
  refine h₆₁.trans' ((mul_le_mul_of_nonneg_left this (by positivity)).trans' _),
  clear h₆₁ this,
  rw [tsub_add_eq_add_tsub htk, ←mul_assoc, ←mul_assoc, ←mul_assoc,
    rpow_neg (sub_pos_of_lt hγ₁).le (red_steps γ k l ini).card, div_pow, ←mul_assoc,
    rpow_nat_cast, div_eq_mul_inv (_ ^ _), ←mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  refine mul_le_mul_of_nonneg_right _ (exp_pos _).le,
  refine mul_le_mul_of_nonneg_right _ (inv_nonneg_of_nonneg (pow_nonneg
    (sub_nonneg_of_le hγ₁.le) _)),
  rw [mul_mul_mul_comm, ←rpow_add two_pos, ←mul_assoc, mul_assoc _ (real.exp _), ←real.exp_add,
    mul_right_comm _ (ini.p ^ _), rpow_def_of_pos two_pos, ←real.exp_add],
  refine (mul_le_mul_of_nonneg_left hf₂ (exp_pos _).le).trans' _,
  rw [←mul_assoc, ←mul_assoc, ←real.exp_add],
  rw [←add_assoc, add_left_comm (-δ * k)],

end

section

variables {V : Type*} [fintype V] [decidable_eq V]
open fintype

section

def density (G : simple_graph V) [decidable_rel G.adj] : ℚ :=
G.edge_finset.card / (card V).choose 2

lemma edge_finset_eq_filter (G : simple_graph V) [decidable_rel G.adj] :
  G.edge_finset = univ.filter (∈ sym2.from_rel G.symm) :=
begin
  rw [←finset.coe_inj, coe_edge_finset, coe_filter, coe_univ, set.sep_univ],
  refl
end

lemma univ_image_quotient_mk {α : Type*} (s : finset α) [fintype α] [decidable_eq α] :
  s.off_diag.image quotient.mk = s.sym2.filter (λ a, ¬ a.is_diag) :=
(sym2.filter_image_quotient_mk_not_is_diag _).symm

lemma edge_finset_eq_filter_filter (G : simple_graph V) [decidable_rel G.adj] :
  G.edge_finset = (univ.filter (λ a : sym2 V, ¬ a.is_diag)).filter (∈ sym2.from_rel G.symm) :=
begin
  rw [edge_finset_eq_filter, filter_filter],
  refine filter_congr _,
  rw sym2.forall,
  intros x y h,
  simp only [sym2.is_diag_iff_proj_eq, iff_and_self, sym2.from_rel_prop],
  intro h,
  exact h.ne,
end

lemma edge_finset_eq_filter' (G : simple_graph V) [decidable_rel G.adj] :
  G.edge_finset = (univ.off_diag.image quotient.mk).filter (∈ sym2.from_rel G.symm) :=
by rw [edge_finset_eq_filter_filter, ←sym2_univ, ←univ_image_quotient_mk]

lemma sum_sym2 {α β : Type*} [decidable_eq α] [add_comm_monoid β] {s : finset α} {f : sym2 α → β} :
  2 • ∑ x in s.off_diag.image quotient.mk, f x = ∑ x in s.off_diag, f (quotient.mk x) :=
begin
  rw [smul_sum, sum_image'],
  rintro ⟨x, y⟩ hxy,
  rw [mem_off_diag] at hxy,
  obtain ⟨hx : x ∈ s, hy : y ∈ s, hxy : x ≠ y⟩ := hxy,
  have hxy' : y ≠ x := hxy.symm,
  have : s.off_diag.filter (λ z, ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    rw [mem_filter, mem_insert, mem_singleton, sym2.eq_iff, prod.mk.inj_iff, prod.mk.inj_iff,
      and_iff_right_iff_imp],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); rw mem_off_diag; exact ⟨‹_›, ‹_›, ‹_›⟩ },
  rw [this, sum_pair, sym2.eq_swap, two_smul],
  simpa using hxy,
end

lemma sum_off_diag {α β : Type*} [decidable_eq α] [add_comm_monoid β] {s : finset α}
  {f : α × α → β} :
  ∑ x in s.off_diag, f x = ∑ x in s, ∑ y in s.erase x, f (x, y) :=
begin
  rw sum_sigma',
  refine sum_bij (λ x _, ⟨x.1, x.2⟩) _ _ _ _,
  { rintro ⟨x, y⟩ h,
    rw [mem_off_diag] at h,
    rw [mem_sigma, mem_erase, ne.def],
    exact ⟨h.1, ne.symm h.2.2, h.2.1⟩ },
  { rintro ⟨x, y⟩ h,
    refl },
  { rintro ⟨a₁, a₂⟩ ⟨a₃, a₄⟩ _ _ ⟨⟩,
    refl },
  rintro ⟨a, b⟩ h,
  simp only [mem_sigma, mem_erase] at h,
  refine ⟨(a, b), _⟩,
  simp [h.1, h.2.2, ne.symm h.2.1],
end

lemma density_eq_average (G : simple_graph V) [decidable_rel G.adj] :
  G.density =
    (card V * (card V - 1))⁻¹ * ∑ x : V, ∑ y in univ.erase x, if G.adj x y then 1 else 0 :=
begin
  rw [simple_graph.density, edge_finset_eq_filter', ←sum_boole, nat.cast_choose_two,
    div_div_eq_mul_div, mul_comm, ←nat.cast_two, ←nsmul_eq_mul, sum_sym2, div_eq_mul_inv, mul_comm,
    sum_off_diag],
  refl
end

lemma density_eq_average' (G : simple_graph V) [decidable_rel G.adj] :
  G.density =
    (card V * (card V - 1))⁻¹ * ∑ x y : V, if G.adj x y then 1 else 0 :=
begin
  rw [density_eq_average],
  congr' 2 with x : 1,
  simp
end

lemma density_eq_average_neighbors (G : simple_graph V) [decidable_rel G.adj] :
  G.density = (card V * (card V - 1))⁻¹ * ∑ x : V, (G.neighbor_finset x).card :=
begin
  rw [density_eq_average'],
  congr' 2 with x : 1,
  simp [neighbor_finset_eq_filter],
end

lemma density_compl (G : simple_graph V) [decidable_rel G.adj] (h : 2 ≤ card V) :
  Gᶜ.density = 1 - G.density :=
begin
  rw [simple_graph.density, card_compl_edge_finset_eq, nat.cast_sub edge_finset_card_le,
    ←one_sub_div, simple_graph.density],
  rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
  exact nat.choose_pos h,
end

lemma sum_ite_fintype {α β : Type*} [fintype α] [decidable_eq α] [add_comm_monoid β] (s : finset α)
  (f : α → β) : ∑ x in s, f x = ∑ x, ite (x ∈ s) (f x) 0 :=
by simp only [sum_ite_mem, univ_inter]

lemma sum_powerset_len_erase {α β : Type*} [fintype α] [decidable_eq α] [add_comm_monoid β] {n : ℕ}
  {s : finset α} (f : finset α → α → β) :
  ∑ U in powerset_len n s, ∑ y in Uᶜ, f U y = ∑ y, ∑ U in powerset_len n (s.erase y), f U y :=
begin
  simp_rw [sum_ite_fintype (_ᶜ : finset α), @sum_comm _ α],
  refine sum_congr rfl (λ y hy, _),
  rw [←sum_filter],
  refine sum_congr _ (λ _ _, rfl),
  ext U,
  simp [mem_powerset_len, subset_erase],
  tauto
end

lemma powerset_len_filter_mem {α : Type*} [decidable_eq α] {n : ℕ} {s : finset α} {x : α}
  (hx : x ∈ s) :
  (powerset_len (n + 1) s).filter (λ U, x ∈ U) = (powerset_len n (s.erase x)).image (insert x) :=
begin
  rw [←insert_erase hx, powerset_len_succ_insert, insert_erase hx, filter_union,
    filter_false_of_mem, filter_true_of_mem, empty_union],
  { simp },
  { simp [mem_powerset_len, subset_erase] {contextual := tt} },
  { simp },
end

lemma sum_powerset_len_insert {α β : Type*} [fintype α] [decidable_eq α] [add_comm_monoid β] {n : ℕ}
  {s : finset α} (f : finset α → α → β) :
  ∑ U in powerset_len (n + 1) s, ∑ x in U, f U x =
    ∑ x in s, ∑ U in powerset_len n (s.erase x), f (insert x U) x :=
begin
  have : ∑ x in s, ∑ U in powerset_len n (s.erase x), f (insert x U) x =
    ∑ x in s, ∑ U in (powerset_len (n + 1) s).filter (λ U, x ∈ U), f U x,
  { refine sum_congr rfl (λ x hx, _),
    rw [powerset_len_filter_mem hx, sum_image _],
    simp only [mem_powerset_len, subset_erase, and_imp],
    intros y hy hy' hy'' z hz hz' hz'' h,
    rw [←erase_insert hy', h, erase_insert hz'] },
  rw [this],
  simp only [sum_filter, @sum_comm _ _ α],
  refine sum_congr rfl (λ U hU, _),
  simp only [mem_powerset_len] at hU,
  simp only [sum_ite_mem],
  rw [(inter_eq_right_iff_subset _ _).2 hU.1],
end

lemma erase_eq_filter {α : Type*} [decidable_eq α] {s : finset α} (a : α) :
  s.erase a = s.filter (≠ a) :=
begin
  rw [filter_not, finset.filter_eq'],
  split_ifs,
  { rw [sdiff_singleton_eq_erase] },
  { rw [erase_eq_of_not_mem h, sdiff_empty] },
end

lemma sum_pair_subset {α β : Type*} [fintype α] [decidable_eq α] [add_comm_monoid β] {n : ℕ}
  {s : finset α} (f : finset α → α → α → β) :
  ∑ U in powerset_len (n + 1) s, ∑ x in U, ∑ y in Uᶜ, f U x y =
    ∑ x in s, ∑ y in univ.erase x, ∑ U in powerset_len n (s \ {x, y}), f (insert x U) x y :=
begin
  simp_rw [@sum_comm _ α α _ _ (_ᶜ)],
  rw [sum_powerset_len_erase],
  simp only [sum_powerset_len_insert],
  rw [sum_sigma' univ, sum_sigma' s],
  refine sum_bij (λ x hx, ⟨x.2, x.1⟩) _ _ _ _,
  { simp [eq_comm] {contextual := tt} },
  { rintro ⟨x, y⟩ hx,
    refine sum_congr _ (λ y hy, rfl),
    dsimp,
    rw [sdiff_insert, sdiff_singleton_eq_erase] },
  { rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    simp {contextual := tt} },
  { rintro ⟨x, y⟩,
    simp only [mem_sigma, mem_erase, mem_univ, and_true, sigma.exists, true_and, heq_iff_eq,
      and_imp, exists_prop, and_assoc],
    intros hx hxy,
    exact ⟨y, x, hxy.symm, hx, rfl, rfl⟩ },
end

lemma choose_helper {n k : ℕ} (h : k + 1 < n) :
  (n.choose (k + 1) : ℚ)⁻¹ * (((n - 2).choose k) * (1 / ((k + 1) * (n - (k + 1))))) =
    (n * (n - 1))⁻¹ :=
begin
  have : k + 2 ≤ n := h,
  have : 2 ≤ n := h.trans_le' (by simp),
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.1 this,
  rw [add_tsub_cancel_right],
  clear this h,
  simp only [add_le_add_iff_right] at this,
  rw [one_div, mul_left_comm, ←mul_inv, ←one_div, ←one_div, mul_one_div, mul_left_comm,
    ←nat.cast_add_one, ←nat.cast_sub, ←nat.cast_mul, ←nat.choose_mul_succ_eq, ←nat.cast_mul,
    ←mul_assoc, mul_comm (k + 1), ←nat.succ_mul_choose_eq, mul_comm (n + 1), mul_assoc,
    nat.cast_mul, ←div_div, div_self, mul_comm, nat.cast_mul, nat.cast_add n 2, nat.cast_two,
    add_sub_assoc, nat.cast_add_one],
  { norm_num1, refl },
  { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact nat.choose_pos this },
  { linarith }
end

lemma density_eq_average_partition (G : simple_graph V) [decidable_rel G.adj] (n : ℕ)
  (hn₀ : 0 < n) (hn : n < card V) :
  G.density = ((card V).choose n)⁻¹ * ∑ U in powerset_len n univ, G.edge_density U Uᶜ :=
begin
  cases n,
  { simpa using hn₀ },
  simp only [simple_graph.edge_density_def, simple_graph.interedges_def, ←sum_boole, sum_div,
    sum_product, density_eq_average, mul_sum],
  rw [sum_pair_subset],
  refine sum_congr rfl _,
  intros x hx,
  refine sum_congr rfl _,
  intros y hy,
  split_ifs,
  swap,
  { simp },
  simp only [←mul_sum],
  have : ∑ (U : finset V) in powerset_len n (univ \ {x, y}),
      (1 : ℚ) / ((insert x U).card * (insert x U)ᶜ.card) =
    ∑ (U : finset V) in powerset_len n (univ \ {x, y}), 1 / ((n + 1) * (card V - (n + 1))),
  { refine sum_congr rfl (λ U hU, _),
    simp only [mem_powerset_len, subset_sdiff, disjoint_insert_right,
      disjoint_singleton_right, subset_univ, true_and, and_assoc] at hU,
    rw [card_compl, card_insert_of_not_mem hU.1, hU.2.2, nat.cast_sub hn.le, nat.cast_add_one] },
  rw [this, sum_const, card_powerset_len, card_sdiff (subset_univ _), card_univ,
    card_doubleton h.ne, mul_one, nsmul_eq_mul],
  rw [choose_helper hn],
end

lemma exists_density_edge_density (G : simple_graph V) [decidable_rel G.adj] (n : ℕ)
  (hn₀ : 0 < n) (hn : n < card V) :
  ∃ U : finset V, U.card = n ∧ G.density ≤ G.edge_density U Uᶜ :=
begin
  suffices : ∃ U ∈ powerset_len n (univ : finset V), G.density ≤ G.edge_density U Uᶜ,
  { simpa [mem_powerset_len] },
  refine exists_le_of_sum_le _ _,
  { rw [←finset.card_pos, card_powerset_len, card_univ],
    exact nat.choose_pos hn.le },
  rw [sum_const, density_eq_average_partition _ _ hn₀ hn, card_powerset_len, card_univ,
    nsmul_eq_mul, mul_inv_cancel_left₀],
  rw [nat.cast_ne_zero],
  exact (nat.choose_pos hn.le).ne'
end

lemma exists_equibipartition_edge_density (G : simple_graph V) [decidable_rel G.adj]
  (hn : 2 ≤ card V) :
  ∃ X Y : finset V, disjoint X Y ∧ ⌊(card V / 2 : ℝ)⌋₊ ≤ X.card ∧ ⌊(card V / 2 : ℝ)⌋₊ ≤ Y.card
    ∧ G.density ≤ G.edge_density X Y :=
begin
  rw [←nat.cast_two, nat.floor_div_eq_div],
  have h₁ : 0 < card V / 2 := nat.div_pos hn two_pos,
  have h₂ : card V / 2 < card V := nat.div_lt_self (pos_of_gt hn) one_lt_two,
  obtain ⟨U, hU, hU'⟩ := exists_density_edge_density G (card V / 2) h₁ h₂,
  refine ⟨U, Uᶜ, disjoint_compl_right, hU.ge, _, hU'⟩,
  rw [card_compl, hU, le_tsub_iff_left h₂.le, ←two_mul],
  exact nat.mul_div_le _ _,
end

end

def top_edge_labelling.density {K : Type*} [decidable_eq K] (χ : top_edge_labelling V K) (k : K) :
  ℝ := density (χ.label_graph k)

lemma exists_equibipartition_col_density {n : ℕ}
  (χ : top_edge_labelling (fin n) (fin 2)) (hn : 2 ≤ n) :
  ∃ ini : book_config χ, χ.density 0 ≤ ini.p ∧
    ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card ∧ ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card :=
begin
  obtain ⟨X, Y, hd, hX, hY, p⟩ :=
    exists_equibipartition_edge_density (χ.label_graph 0) (by simpa using hn),
  rw [fintype.card_fin] at hX hY,
  refine ⟨⟨X, Y, ∅, ∅, hd, _, _, _, _, _, _, _, _, _⟩, rat.cast_le.2 p, hX, hY⟩,
  all_goals { simp }
end

lemma density_zero_one (χ : top_edge_labelling V (fin 2)) (h : 2 ≤ card V) :
  χ.density 0 = 1 - χ.density 1 :=
begin
  rw [top_edge_labelling.density, top_edge_labelling.density, ←rat.cast_one, ←rat.cast_sub,
    rat.cast_inj, ←density_compl _ h],
  simp only [←to_edge_labelling_label_graph_compl, label_graph_to_edge_labelling χ],
end

end

lemma nine_two_monotone {γ η : ℝ} (γ' δ' : ℝ) (hγu : γ ≤ γ') (hηγ : δ' ≤ 1 - γ' - η)
  (hδ : 0 < δ') (hγ1 : γ' < 1) (hδ' : δ' ≤ 1) :
  δ' ^ (1 / (1 - γ')) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  have : δ' ≤ 1 - γ - η := hηγ.trans (by linarith only [hγu]),
  refine (rpow_le_rpow hδ.le this _).trans' _,
  { exact div_nonneg (by norm_num1) (by linarith only [hγu, hγ1]) },
  refine rpow_le_rpow_of_exponent_ge hδ hδ' _,
  exact div_le_div_of_le_left zero_le_one (sub_pos_of_lt hγ1) (by linarith only [hγu])
end

lemma nine_two_numeric_aux {γ η : ℝ} (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
  (134 / 150) ^ (10 / 9 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  refine (nine_two_monotone (1 / 10) (67 / 75) hγu _ _ _ _).trans_eq' _,
  { linarith only [hηγ, hγu] },
  { norm_num1 },
  { norm_num1 },
  { norm_num1 },
  { norm_num },
end

lemma nine_two_numeric {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
  exp (- 1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  refine (nine_two_numeric_aux hγu hηγ).trans' _,
  have : (0 : ℝ) < 134 / 150 := by norm_num1,
  rw [←le_log_iff_exp_le (rpow_pos_of_pos this _), log_rpow this, ←div_le_iff'],
  swap, { positivity },
  norm_num1,
  rw [neg_le, ←log_inv, inv_div, le_div_iff, mul_comm, ←log_rpow, log_le_iff_le_exp, ←exp_one_rpow],
  { refine (rpow_le_rpow (by norm_num1) exp_one_gt_d9.le (by norm_num1)).trans' _,
    norm_num },
  { exact rpow_pos_of_pos (by norm_num1) _ },
  { norm_num1 },
  { norm_num1 },
end.

lemma nine_two_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
  (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
  (h : exp (- 1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
  exp (6 * γ * t ^ 2 / (20 * k)) ≤ exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
begin
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ],
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le],
  refine (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
    (exp_pos _).le).trans' _,
  rw [←exp_one_rpow (_ + _), ←rpow_mul (exp_pos _).le, exp_one_rpow, ←real.exp_add, exp_le_exp,
    sq, mul_mul_mul_comm, ←div_mul_eq_mul_div, ←mul_assoc γ, mul_div_assoc (γ * t),
    mul_comm (γ * t), ←add_mul, div_add'],
  swap, { positivity },
  refine mul_le_mul_of_nonneg_right _ (by positivity),
  rw [div_le_iff, div_mul_eq_mul_div, mul_div_assoc, mul_div_mul_right],
  { linarith },
  { positivity },
  { positivity },
end

-- lemma nine_two_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
--   (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
--   (h : exp (- 1 / 3 + 1 / 5) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
--   exp ((k : ℝ) * (γ * (2 / 15))) ≤ exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
-- begin
--   have : 0 < 1 - γ - η := by linarith only [hγu, hηγ],
--   rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le],
--   refine (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
--     (exp_pos _).le).trans' _,
--   rw [←exp_one_rpow (_ + _), ←rpow_mul (exp_pos _).le, exp_one_rpow, ←real.exp_add, exp_le_exp,
--     sq, ←mul_assoc γ, mul_div_assoc, ←mul_comm (γ * t), ←mul_add],
--   have : (k : ℝ) * (γ * (2 / 15)) ≤ γ * t * (1 / 5),
--   { rw [mul_left_comm, mul_assoc],
--     refine mul_le_mul_of_nonneg_left _ hγl,
--     linarith only [ht] },
--   refine this.trans (mul_le_mul_of_nonneg_left _ (by positivity)),
--   rw [div_add', le_div_iff],
--   { linarith only [ht] },
--   { positivity },
--   { positivity },
-- end

lemma nine_two_part_three {η γ : ℝ} (hγl : 0 ≤ η) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15) :
  exp (- 3 * η / 2) ≤ (1 - γ - η) / (1 - γ) :=
begin
  rw [←one_sub_div, ←div_mul_eq_mul_div],
  swap, { linarith },
  have h₂ : - 1 / 3 ≤ (-3 / 2) * η := by linarith,
  refine (general_convex_thing' (by linarith) h₂ (by norm_num)).trans _,
  have : 1 + (-10 / 9) * η ≤ 1 - η / (1 - γ),
  { rw [neg_div, neg_mul, ←sub_eq_add_neg, sub_le_sub_iff_left, div_eq_mul_one_div, mul_comm],
    refine mul_le_mul_of_nonneg_right _ hγl,
    rw [div_le_iff];
    linarith },
  refine this.trans' _,
  rw [←mul_assoc, ←div_mul_eq_mul_div, add_le_add_iff_left],
  refine mul_le_mul_of_nonneg_right _ hγl,
  suffices : exp (- 1 / 3) ≤ 61 / 81,
  { rw [mul_div_assoc, ←le_div_iff, sub_le_iff_le_add],
    { exact this.trans_eq (by norm_num1) },
    { norm_num1 } },
  refine le_of_pow_le_pow 3 (by norm_num1) (by norm_num1) _,
  rw [←exp_nat_mul, nat.cast_bit1, nat.cast_one, mul_div_cancel', ←inv_div, inv_pow, real.exp_neg],
  { refine inv_le_inv_of_le (by norm_num1) (exp_one_gt_d9.le.trans' (by norm_num1)) },
  { norm_num1 },
end

lemma nine_two_part_four {k t : ℕ} {η γ : ℝ} (hγl : 0 ≤ η) (hγu : γ ≤ 1 / 10) (hηγ : η ≤ γ / 15)
  (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
  exp (- 3 * γ * t ^ 2 / (20 * k)) ≤ ((1 - γ - η) / (1 - γ)) ^ t :=
begin
  refine (pow_le_pow_of_le_left (exp_pos _).le (nine_two_part_three hγl hγu hηγ) _).trans' _,
  rw [←exp_nat_mul, exp_le_exp, neg_mul, neg_mul, neg_div, neg_mul, neg_div, mul_neg,
    neg_le_neg_iff, mul_div_assoc, mul_left_comm, ←mul_assoc, sq, mul_mul_mul_comm, mul_div_assoc],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  refine (div_le_div_of_le (by positivity) hηγ).trans _,
  rw [div_div, div_eq_mul_one_div, mul_div_assoc],
  refine mul_le_mul_of_nonneg_left _ (by linarith),
  rw [le_div_iff, ←mul_assoc],
  { exact ht.trans' (mul_le_mul_of_nonneg_right (by norm_num1) (nat.cast_nonneg _)) },
  { positivity }
end

lemma nine_two_part_five {k t : ℕ} {η γ γ₀ δ fk : ℝ} (hη₀ : 0 ≤ η) (hγu : γ ≤ 1 / 10)
  (hηγ : η ≤ γ / 15) (hγ₀' : 0 < γ) (h₂ : 0 ≤ 1 - γ - η)
  (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) (hδ : δ = γ / 20) (hγ₀ : γ₀ ≤ γ)
  (hγ₁ : γ < 1) (hfk : -fk ≤ γ₀ / 60 * k) :
  1 ≤ exp (-δ * k + fk) * (1 - γ - η) ^ (γ * t / (1 - γ)) *
    ((1 - γ - η) / (1 - γ)) ^ t * exp (γ * t ^ 2 / (2 * ↑k)) :=
begin
  rw [mul_right_comm _ ((1 - γ - η) ^ (_ : ℝ)), mul_right_comm, mul_assoc],
  refine (mul_le_mul_of_nonneg_left (nine_two_part_two hγ₀'.le hγu hηγ ht hk
    (nine_two_numeric hγ₀'.le hγu hηγ)) _).trans' _,
  { exact mul_nonneg (exp_pos _).le (pow_nonneg (div_nonneg h₂
      (sub_pos_of_lt hγ₁).le) _) },
  rw [mul_right_comm, ←real.exp_add],
  refine (mul_le_mul_of_nonneg_left (nine_two_part_four hη₀ hγu hηγ ht hk)
    (exp_pos _).le).trans' _,
  rw [←real.exp_add, one_le_exp_iff, add_right_comm _ fk, add_right_comm _ fk, neg_mul,
    neg_mul, neg_mul, neg_div, add_assoc (- _), ←sub_eq_add_neg, ←sub_div,
    ←sub_neg_eq_add _ fk, sub_nonneg],
  have : - ((((2 / 3) ^ 2)⁻¹ * γ * t ^ 2) / (20 * k)) ≤ - (δ * k),
  { rw [neg_le_neg_iff, hδ, ←div_div, le_div_iff, mul_assoc, ←sq, ←div_mul_eq_mul_div,
      mul_div_assoc, mul_assoc, mul_left_comm],
    swap,
    { rw [nat.cast_pos],
      exact hk },
    refine mul_le_mul_of_nonneg_left _ (div_nonneg hγ₀'.le (by norm_num1)),
    rw [inv_mul_eq_div, le_div_iff', ←mul_pow],
    { exact pow_le_pow_of_le_left (by positivity) ht _ },
    { positivity } },
  have hfk' : -fk ≤ γ / 60 * k,
  { exact hfk.trans (mul_le_mul_of_nonneg_right (by linarith only [hγ₀]) (nat.cast_nonneg _)) },
  refine hfk'.trans ((add_le_add_right this _).trans' _),
  rw [neg_add_eq_sub, ←sub_div, mul_assoc, mul_assoc, mul_assoc, ←sub_mul, ←sub_mul, ←div_div,
    le_div_iff, mul_assoc, ←sq, div_mul_comm, mul_comm, mul_left_comm, mul_div_assoc,
    ←div_mul_eq_mul_div],
  swap,
  { positivity },
  refine mul_le_mul_of_nonneg_left _ hγ₀'.le,
  rw [←div_le_iff', div_div, div_eq_mul_one_div],
  swap,
  { norm_num1 },
  refine (pow_le_pow_of_le_left (by positivity) ht _).trans_eq' _,
  ring,
end

-- TODO: move
section

variables {V K : Type*} [decidable_eq K] [fintype K] {n : K → ℕ}

lemma ramsey_number_le_finset_aux {s : finset V} (C : top_edge_labelling V K)
  (h : ∃ (m : finset s) (c : K),
    (C.pullback (function.embedding.subtype _ : s ↪ V)).monochromatic_of m c ∧ n c ≤ m.card):
  ∃ (m : finset V) (c : K), m ⊆ s ∧ C.monochromatic_of m c ∧ n c ≤ m.card :=
begin
  obtain ⟨m, c, hm, hn⟩ := h,
  refine ⟨_, c, _, hm.map, hn.trans_eq (card_map _).symm⟩,
  simp only [subset_iff, finset.mem_map, function.embedding.coe_subtype, exists_prop,
    subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right, forall_exists_index],
  intros x hx _,
  exact hx
end

-- there should be a version of this for is_ramsey_valid and it should be useful *for* the proof
-- that ramsey numbers exist
lemma ramsey_number_le_finset {s : finset V} (h : ramsey_number n ≤ s.card)
  (C : top_edge_labelling V K) :
  ∃ (m : finset V) (c : K), m ⊆ s ∧ C.monochromatic_of m c ∧ n c ≤ m.card :=
begin
  have : ramsey_number n ≤ fintype.card s, { rwa fintype.card_coe },
  rw [ramsey_number_le_iff, is_ramsey_valid] at this,
  exact ramsey_number_le_finset_aux _ (this _)
end

lemma ramsey_number_le_choose' {i j : ℕ} : ramsey_number ![i, j] ≤ (i + j).choose i :=
((ramsey_number.mono_two (nat.le_succ _) (nat.le_succ _)).trans
  (ramsey_number_le_choose (i + 1) (j + 1))).trans
    (by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero, nat.add_succ, nat.succ_add_sub_one])

end

lemma nine_two (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ δ η : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 10 → δ = γ / 20 → 0 ≤ η → η ≤ γ / 15 →
  ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2), 1 - γ - η ≤ χ.density 0 →
  exp (- δ * k) * (k + l).choose l ≤ n →
  (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) :=
begin
  obtain ⟨f, hf, hf'⟩ := nine_five,
  filter_upwards [nine_three_lower_n γ₀ hγ₀, nine_three γ₀ hγ₀, hf' γ₀ hγ₀,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster (hf.bound (div_pos hγ₀ (by norm_num1) : 0 < γ₀ / 60))]
    with l hn₂ h₉₃ h₉₅ hk₀ hfk
      k γ δ η hγ hγl hγu hδ hη₀ hηγ n χ hχd hn,
  clear hf',
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1),
  have hl₀ : 0 < l := hk₀ l le_rfl,
  have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1)),
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl,
  have hδ' : δ = min (1 / 200) (γ / 20),
  { rw [hδ, min_eq_right],
    linarith only [hγu] },
  have hδ₀ : 0 ≤ δ,
  { rw [hδ],
    exact div_nonneg hγ₀'.le (by norm_num1) },
  by_contra hχ,
  have hp₀ : 1 / 2 ≤ 1 - γ - η,
  { linarith only [hγu, hηγ] },
  specialize hn₂ k γ hγ hγl hγ₁ hlk δ hδ.le n hn,
  obtain ⟨ini, hini, hXc, hYc⟩ := exists_equibipartition_col_density χ hn₂,
  replace hini := hχd.trans hini,
  have hini4 : 1 / 4 ≤ ini.p,
  { exact hini.trans' (hp₀.trans' (by norm_num1)) },
  specialize h₉₃ k hlk γ hγ hγl (hγu.trans (by norm_num1)) δ hδ' n χ hχ ini hini4 hXc hn,
  specialize h₉₅ k hlk γ δ η hγ hγl hδ₀ hδ.le hη₀ hp₀ n χ hχ ini hini hYc hn,
  specialize hfk k hlk,
  clear hδ',
  rw [norm_eq_abs, abs_le', norm_coe_nat] at hfk,
  have : 1 ≤ exp (-δ * k + f k) * (1 - γ - η) ^ (γ * ↑((red_steps γ k l ini).card) / (1 - γ)) *
    ((1 - γ - η) / (1 - γ)) ^ (red_steps γ k l ini).card *
    exp (γ * ↑((red_steps γ k l ini).card) ^ 2 / (2 * ↑k)) :=
    nine_two_part_five hη₀ hγu hηγ hγ₀' (hp₀.trans' (by norm_num1)) h₉₃ (hk₀ k hlk) hδ hγl hγ₁
      hfk.2,
  replace h₉₅ := h₉₅.trans' (mul_le_mul_of_nonneg_right this (nat.cast_nonneg _)),
  rw [one_mul, nat.cast_le, ←nat.choose_symm_add] at h₉₅,
  have := ramsey_number_le_finset (ramsey_number_le_choose'.trans h₉₅) χ,
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, tsub_le_iff_left,
    matrix.head_cons] at this hχ,
  obtain ⟨m, (⟨hm₀, hm₁, hm₂⟩ | ⟨hm₀, hm₁, hm₂⟩)⟩ := this,
  swap,
  { exact hχ ⟨m, or.inr ⟨hm₁, hm₂⟩⟩ },
  refine hχ ⟨(end_state γ k l ini).A ∪ m, or.inl ⟨_, hm₂.trans _⟩⟩,
  { rw [coe_union, top_edge_labelling.monochromatic_of_union],
    refine ⟨(end_state γ k l ini).red_A, hm₁, _⟩,
    exact (end_state γ k l ini).red_XYA.symm.subset_right (hm₀.trans (subset_union_right _ _)) },
  rwa [card_union_eq, add_le_add_iff_right],
  { exact t_le_A_card γ (hk₀ k hlk).ne' (hk₀ l le_rfl).ne' ini },
  exact (end_state γ k l ini).hYA.symm.mono_right hm₀,
end

def equiv.to_finset {α : Type*} {s : set α} [fintype s] : s.to_finset ≃ s :=
⟨λ x, ⟨x, by simpa using x.2⟩, λ x, ⟨x, by simp⟩, λ x, subtype.ext rfl, λ x, subtype.ext rfl⟩

lemma finset.card_congr_of_equiv {α β : Type*} {s : finset α} {t : finset β}
  (e : s ≃ t) : s.card = t.card :=
begin
  refine finset.card_congr (λ x hx, e ⟨x, hx⟩) (λ x hx, (e _).2) (λ x y hx hy h, _)
    (λ x hx, ⟨e.symm ⟨x, hx⟩, (e.symm _).2, _⟩),
  { rw [←subtype.ext_iff, equiv.apply_eq_iff_eq, subtype.ext_iff] at h,
    exact h },
  rw [subtype.coe_eta, equiv.apply_symm_apply, subtype.coe_mk],
end

lemma density_graph_iso {V V' : Type*} [fintype V] [fintype V'] [decidable_eq V] [decidable_eq V']
  {G : simple_graph V} {G' : simple_graph V'} [decidable_rel G.adj] [decidable_rel G'.adj]
  (e : G ≃g G') : G.density = G'.density :=
begin
  rw [simple_graph.density, e.card_eq_of_iso, simple_graph.edge_finset, simple_graph.density,
    simple_graph.edge_finset, finset.card_congr_of_equiv],
  exact equiv.to_finset.trans (e.map_edge_set.trans equiv.to_finset.symm),
end

def label_graph_iso {V V' K : Type*} {χ : top_edge_labelling V K} (k : K) (f : V' ≃ V) :
  (χ.pullback f.to_embedding).label_graph k ≃g χ.label_graph k :=
{ to_equiv := f,
  map_rel_iff' :=
  begin
    intros x y,
    simp only [ne.def, embedding_like.apply_eq_iff_eq, equiv.coe_to_embedding,
      top_edge_labelling.label_graph_adj, top_edge_labelling.pullback_get],
  end }

lemma nine_two_variant (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ δ η : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 10 → δ = γ / 20 → 0 ≤ η → η ≤ γ / 15 →
  ∀ V : Type*, decidable_eq V → fintype V → ∀ χ : top_edge_labelling V (fin 2), by exactI
  1 - γ - η ≤ χ.density 0 →
  exp (- δ * k) * (k + l).choose l ≤ fintype.card V →
  (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) :=
begin
  filter_upwards [nine_two γ₀ hγ₀] with l hl
    k γ δ η hγ hγl hγu hδ hη hηγ V _inst_1 _inst_2 χ hχ hn,
  resetI,
  obtain ⟨e⟩ := fintype.trunc_equiv_fin V,
  let χ' : top_edge_labelling (fin (fintype.card V)) (fin 2) := χ.pullback e.symm.to_embedding,
  have : 1 - γ - η ≤ χ'.density 0,
  { refine hχ.trans_eq _,
    rw [top_edge_labelling.density, top_edge_labelling.density, rat.cast_inj],
    refine density_graph_iso _,
    exact (label_graph_iso _ _).symm },
  obtain ⟨m, c, hm, hmc⟩ := hl k γ δ η hγ hγl hγu hδ hη hηγ (fintype.card V) χ' this hn,
  refine ⟨m.map e.symm.to_embedding, c, hm.map, hmc.trans _⟩,
  rw [card_map]
end

lemma nine_one_part_one {m : ℝ} (hm : 1 < m) :
  (⌈(m / exp 1 : ℝ)⌉₊ : ℝ) < m :=
begin
  have : 1 / 2 < m / 2 := div_lt_div_of_lt two_pos hm,
  refine ((ceil_lt_two_mul this).trans_le' _).trans_eq _,
  { refine nat.cast_le.2 (nat.ceil_mono _),
    exact div_le_div_of_le_left (by linarith) two_pos (exp_one_gt_d9.le.trans' (by norm_num1)) },
  exact mul_div_cancel' _ two_pos.ne',
end

lemma gamma'_le_gamma_iff {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) :
  (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2 ↔ (l * (k + l) : ℝ) / (k + 2 * l) < m :=
begin
  have : (l : ℝ) * l * (k + l - m) - (l - m) * ((k + l) * (k + l)) =
    k * (m * (k + 2 * l) - l * (k + l)), { ring_nf },
  rw [div_pow, div_lt_iff, div_lt_iff, div_mul_eq_mul_div, lt_div_iff, ←sub_pos, sq, sq, this,
    mul_pos_iff, or_iff_left, and_iff_right, sub_pos],
  { rwa nat.cast_pos },
  { simp only [not_and', not_lt, nat.cast_nonneg, implies_true_iff] },
  { positivity },
  { positivity },
  rw [add_sub_assoc, ←nat.cast_sub h],
  positivity
end

lemma gamma_mul_k_le_m_of {k l m : ℕ} (h : m ≤ l) (h' : 0 < k)
  (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2) :
  (l / (k + l) : ℝ) * k ≤ m :=
begin
  rw [gamma'_le_gamma_iff h h'] at hg,
  refine hg.le.trans' _,
  rw [div_mul_eq_mul_div, div_le_div_iff, ←sub_nonneg],
  { ring_nf,
    positivity },
  { positivity },
  { positivity },
end

noncomputable def U_lower_bound_ratio (ξ : ℝ) (k l m : ℕ) : ℝ :=
(1 + ξ) ^ m * ∏ i in range m, (l - i) / (k + l - i)

lemma U_lower_bound_ratio_eq {ξ : ℝ} (k l m : ℕ) :
  U_lower_bound_ratio ξ k l m = ∏ i in range m, ((1 + ξ) * ((l - i) / (k + l - i))) :=
begin
  rw [U_lower_bound_ratio, prod_mul_distrib],
  simp,
end

lemma U_lower_bound_ratio_of_l_lt_m {ξ : ℝ} {k l m : ℕ} (h : l < m) :
  U_lower_bound_ratio ξ k l m = 0 :=
begin
  rw ←mem_range at h,
  rw [U_lower_bound_ratio, prod_eq_zero h, mul_zero],
  rw [sub_self, zero_div],
end

lemma U_lower_bound_ratio_nonneg {ξ : ℝ} {k l m : ℕ} (hξ : 0 ≤ ξ) :
  0 ≤ U_lower_bound_ratio ξ k l m :=
begin
  cases lt_or_le l m,
  { rw U_lower_bound_ratio_of_l_lt_m h },
  rw [U_lower_bound_ratio_eq],
  refine prod_nonneg (λ i hi, _),
  have : (0 : ℝ) ≤ l - i,
  { rw [sub_nonneg, nat.cast_le],
    exact h.trans' (mem_range.1 hi).le },
  rw [mem_range] at hi,
  refine mul_nonneg (by linarith only [hξ]) (div_nonneg this _),
  rw [add_sub_assoc],
  exact add_nonneg (nat.cast_nonneg _) this
end

lemma U_lower_bound_ratio_pos {ξ : ℝ} {k l m : ℕ} (hξ : 0 ≤ ξ) (h : m ≤ l) :
  0 < U_lower_bound_ratio ξ k l m :=
begin
  rw U_lower_bound_ratio_eq,
  refine prod_pos _,
  intros i hi,
  rw [mem_range] at hi,
  rw [add_sub_assoc],
  have : (0 : ℝ) < l - i,
  { rw [sub_pos, nat.cast_lt],
    exact hi.trans_le h },
  positivity
end

lemma U_lower_bound_decreasing {ξ : ℝ} (k l : ℕ) (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1)
  (hlk : l ≤ k) (hk : 0 < k) :
  antitone (U_lower_bound_ratio ξ k l) :=
begin
  refine antitone_nat_of_succ_le _,
  intro m,
  cases le_or_lt l m,
  { rw U_lower_bound_ratio_of_l_lt_m,
    { exact U_lower_bound_ratio_nonneg hξ },
    rwa nat.lt_add_one_iff },
  rw [U_lower_bound_ratio_eq, prod_range_succ, ←U_lower_bound_ratio_eq],
  refine mul_le_of_le_one_right _ _,
  { exact U_lower_bound_ratio_nonneg hξ },
  rw [mul_div_assoc', add_sub_assoc, ←nat.cast_sub h.le, div_le_one, add_comm, add_one_mul,
    add_le_add_iff_right],
  { refine (mul_le_of_le_one_left (nat.cast_nonneg _) hξ').trans _,
    rw nat.cast_le,
    exact (nat.sub_le _ _).trans hlk },
  positivity
end

lemma xi_numeric : exp (1 / 20) < (1 + 1 / 16) :=
begin
  refine lt_of_pow_lt_pow 20 (by norm_num1) _,
  rw [←exp_nat_mul],
  refine (exp_one_lt_d9.trans_eq' (by norm_num)).trans_le _,
  norm_num
end

lemma U_lower_bound_ratio_lower_bound_aux_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m ≤ l) (hk₀ : 0 < k)
  (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
  (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
  (hn : exp (- δ * k) * (k + l).choose l ≤ n) :
  ((k + l - m).choose k : ℝ) ≤ n * U_lower_bound_ratio (1 / 16) k l m :=
begin
  have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml,
  rw [U_lower_bound_ratio, add_comm (k : ℝ), ←this],
  refine (mul_le_mul_of_nonneg_right hn _).trans' _,
  { positivity },
  rw [mul_div_assoc', mul_assoc, ←nat.choose_symm_add, add_comm l, mul_div_cancel',
    add_tsub_assoc_of_le hml, nat.choose_symm_add, ←mul_assoc],
  swap,
  { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact nat.choose_pos (by simp) },
  refine le_mul_of_one_le_left (nat.cast_nonneg _) _,
  rw [neg_mul, real.exp_neg, inv_mul_eq_div, one_le_div (exp_pos _), hδ, div_mul_eq_mul_div, hγ],
  refine (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le m).trans' _,
  rw [←exp_nat_mul, mul_one_div, exp_le_exp],
  exact div_le_div_of_le (by norm_num1) (gamma_mul_k_le_m_of hml hk₀ hg),
end

lemma U_lower_bound_ratio_lower_bound_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
  (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
  (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
  (hn : exp (- δ * k) * (k + l).choose l ≤ n) :
  (k : ℝ) ≤ n * U_lower_bound_ratio (1 / 16) k l m :=
begin
  refine (U_lower_bound_ratio_lower_bound_aux_aux hml.le hk₀ hγ hδ hg hn).trans' _,
  rw [nat.cast_le, add_tsub_assoc_of_le hml.le],
  have : 1 ≤ l - m,
  { rw [nat.succ_le_iff],
    exact nat.sub_pos_of_lt hml },
  refine (nat.choose_le_choose k (add_le_add_left this k)).trans' _,
  rw [nat.choose_symm_add, nat.choose_one_right],
  simp
end

lemma U_lower_bound_ratio_lower_bound' {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
  (hlk : l ≤ k) (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
  (hn : exp (- δ * k) * (k + l).choose l ≤ n) (h : (k : ℝ) < (l - 2) * l) :
  (k : ℝ) ≤ n * U_lower_bound_ratio (1 / 16) k l m :=
begin
  cases lt_or_le ((l - m : ℝ) / (k + l - m)) ((l / (k + l)) ^ 2) with h' h',
  { exact U_lower_bound_ratio_lower_bound_aux hml hk₀ hγ hδ h' hn },
  let mst := ⌊(l * (k + l) : ℝ) / (k + 2 * l)⌋₊ + 1,
  have hm : m < mst,
  { rw [←not_lt, gamma'_le_gamma_iff hml.le hk₀, not_lt] at h',
    rw [←@nat.cast_lt ℝ],
    refine h'.trans_lt _,
    rw nat.cast_add_one,
    exact nat.lt_floor_add_one _ },
  rw ←sub_pos at h,
  have : mst < l,
  { rw [←@nat.cast_lt ℝ, nat.cast_add_one, ←lt_sub_iff_add_lt],
    refine (nat.floor_le (by positivity)).trans_lt _,
    rw [div_lt_iff, ←sub_pos],
    { ring_nf, exact h },
    { positivity } },
  refine (U_lower_bound_ratio_lower_bound_aux this hk₀ hγ hδ _ hn).trans (mul_le_mul_of_nonneg_left
    (U_lower_bound_decreasing k l (by norm_num1) (by norm_num1) hlk hk₀ hm.le) (nat.cast_nonneg _)),
  rw [gamma'_le_gamma_iff this.le hk₀, nat.cast_add_one],
  exact nat.lt_floor_add_one _
end

lemma small_k {k l : ℕ} {γ γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγl : γ₀ ≤ γ) (hγ : γ = l / (k + l))
  (hk₀ : 0 < k) : (k : ℝ) ≤ l * (γ₀⁻¹ - 1) :=
begin
  subst γ,
  rwa [le_div_iff, ←le_div_iff' hγ₀, ←le_sub_iff_add_le, div_eq_mul_inv, ←mul_sub_one] at hγl,
  positivity
end

def is_good_clique {n : ℕ} (ξ : ℝ) (k l : ℕ)
  (χ : top_edge_labelling (fin n) (fin 2)) (x : finset (fin n)) : Prop :=
χ.monochromatic_of x 1 ∧
  (n : ℝ) * (U_lower_bound_ratio ξ k l x.card) ≤ (common_blues χ x).card

lemma empty_is_good {n k l : ℕ} {ξ : ℝ} {χ : top_edge_labelling (fin n) (fin 2)} :
  is_good_clique ξ k l χ ∅ :=
begin
  split,
  { simp },
  rw [U_lower_bound_ratio_eq, card_empty, prod_range_zero, mul_one, nat.cast_le, common_blues],
  simp
end

lemma good_clique_bound {n k l ξ} {χ : top_edge_labelling (fin n) (fin 2)} {x : finset (fin n)}
  (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
  (hx : is_good_clique ξ k l χ x) :
  x.card < l :=
begin
  by_contra',
  exact hχ ⟨x, 1, hx.1, by simpa using this⟩,
end

lemma common_blues_insert {V : Type*} [fintype V] [decidable_eq V] {x : finset V} {i : V}
  {χ : top_edge_labelling V (fin 2)} :
  common_blues χ (insert i x) = blue_neighbors χ i ∩ common_blues χ x :=
begin
  ext v,
  simp [common_blues],
end

lemma maximally_good_clique_aux {V : Type*} [decidable_eq V] [fintype V]
  {χ : top_edge_labelling V (fin 2)} {U : finset V} :
  (χ.pullback (function.embedding.subtype (∈ U))).density 1 =
    (U.card * (U.card - 1))⁻¹ * ∑ v in U, (blue_neighbors χ v ∩ U).card :=
begin
  rw [top_edge_labelling.density, density_eq_average_neighbors, fintype.subtype_card,
    filter_mem_eq_inter, univ_inter, rat.cast_mul, ←nat.cast_sum, ←nat.cast_sum, rat.cast_inv,
    rat.cast_mul, rat.cast_sub, rat.cast_one, rat.cast_coe_nat, rat.cast_coe_nat],
  congr' 2,
  refine sum_bij (λ x _, x) (λ x _, x.2) _ (λ _ _ _ _, subtype.ext) _,
  swap,
  { intros x hx,
    refine ⟨⟨x, hx⟩, mem_univ _, rfl⟩ },
  rintro ⟨x, hx⟩ -,
  refine card_congr (λ x _, x) _ (λ _ _ _ _, subtype.ext) _,
  { simp only [subtype.forall, mem_neighbor_finset, top_edge_labelling.label_graph_adj,
      top_edge_labelling.pullback_get, mem_inter, mem_col_neighbors, forall_exists_index, ne.def,
      function.embedding.coe_subtype, subtype.coe_mk, coe_mem, and_true],
    intros y hy h hxy,
    exact ⟨h, hxy⟩ },
  { intros y,
    simp only [mem_neighbor_finset, top_edge_labelling.label_graph_adj, mem_col_neighbors,
      mem_inter, subtype.exists, subtype.coe_mk, and_imp, exists_imp_distrib, ne.def,
      function.embedding.coe_subtype, exists_prop, exists_eq_right, exists_and_distrib_right,
      top_edge_labelling.pullback_get],
    intros h h' hy,
    exact ⟨hy, h, h'⟩ },
end

lemma big_U {U : ℕ} (hU : 256 ≤ U) : (U : ℝ) / (U - 1) * (1 + 1 / 16) ≤ 1 + 1 / 15 :=
begin
  have : (256 : ℝ) ≤ U, { exact (nat.cast_le.2 hU).trans_eq' (by norm_num1) },
  rw [div_mul_eq_mul_div, div_le_iff];
  linarith,
end

-- here
lemma maximally_good_clique {n k l : ℕ} {ξ ξ' : ℝ} {χ : top_edge_labelling (fin n) (fin 2)}
  (hξ : 0 ≤ ξ)
  (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
  {x : finset (fin n)}
  (hU : ((common_blues χ x).card : ℝ) / ((common_blues χ x).card - 1) * (1 + ξ) ≤ 1 + ξ')
  (hU' : 2 ≤ (common_blues χ x).card)
  (hx : is_good_clique ξ k l χ x)
  (h : ∀ i : fin n, i ∉ x → is_good_clique ξ k l χ (insert i x) → false) :
  1 - (1 + ξ') * ((l - x.card : ℝ) / (k + l - x.card)) ≤
    (χ.pullback (function.embedding.subtype _ : common_blues χ x ↪ fin n)).density 0 :=
begin
  classical,
  have hml := good_clique_bound hχ hx,
  rw [is_good_clique] at hx,
  have : ∀ i ∈ common_blues χ x, i ∉ x ∧
    ¬ ((n : ℝ) * (U_lower_bound_ratio ξ k l (insert i x).card) ≤ (common_blues χ (insert i x)).card),
  { intros i hi,
    rw [common_blues, mem_filter] at hi,
    have : i ∉ x,
    { intro h',
      exact not_mem_col_neighbors (hi.2 i h') },
    refine ⟨this, λ hi', h i this ⟨_, hi'⟩⟩,
    rw [coe_insert, top_edge_labelling.monochromatic_of_insert],
    swap,
    { exact this },
    refine ⟨hx.1, _⟩,
    intros y hy,
    have := hi.2 y hy,
    rw [mem_col_neighbors'] at this,
    obtain ⟨_, z⟩ := this,
    exact z },
  have hz : ∀ i ∈ common_blues χ x,
    ((blue_neighbors χ i ∩ common_blues χ x).card : ℝ) <
      (common_blues χ x).card * ((1 + ξ) * ((l - x.card) / (k + l - x.card))),
  { intros i hi,
    obtain ⟨hi', hi''⟩ := this i hi,
    rw [card_insert_of_not_mem hi', not_le, common_blues_insert, U_lower_bound_ratio_eq,
      prod_range_succ, ←U_lower_bound_ratio_eq, ←mul_assoc, add_sub_assoc] at hi'',
    have : (0 : ℝ) < (1 + ξ) * ((l - x.card) / (k + (l - x.card))),
    { have : (0 : ℝ) < l - x.card,
      { rwa [sub_pos, nat.cast_lt] },
      positivity },
    replace hi'' := hi''.trans_le (mul_le_mul_of_nonneg_right hx.2 this.le),
    rwa [add_sub_assoc'] at hi'' },
  rw [density_zero_one, maximally_good_clique_aux, sub_le_sub_iff_left],
  swap,
  { rw [fintype.subtype_card, filter_mem_eq_inter, univ_inter],
    exact hU' },
  refine (mul_le_mul_of_nonneg_left (sum_le_sum (λ i hi, (hz i hi).le)) _).trans _,
  { rw [inv_nonneg],
    refine mul_nonneg (nat.cast_nonneg _) _,
    rw [sub_nonneg, nat.one_le_cast],
    exact hU'.trans' (by norm_num1) },
  rw [sum_const, nsmul_eq_mul, inv_mul_eq_div, mul_div_mul_left, ←div_mul_eq_mul_div, ←mul_assoc],
  swap,
  { rw [nat.cast_ne_zero],
    linarith only [hU'] },
  refine mul_le_mul_of_nonneg_right _ _,
  swap,
  { rw [add_sub_assoc, ←nat.cast_sub hml.le],
    positivity },
  exact hU
end

lemma nine_one_end {k l n : ℕ} {ξ : ℝ} {χ : top_edge_labelling (fin n) (fin 2)} {x : finset (fin n)}
  (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
  (hx : is_good_clique ξ k l χ x)
  (h : ∃ (m : finset (fin n)) (c : fin 2), m ⊆ common_blues χ x ∧ χ.monochromatic_of ↑m c ∧
    ![k, l - x.card] c ≤ m.card) :
  false :=
begin
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
    tsub_le_iff_right] at h,
  obtain ⟨m, (hm | ⟨hm, hm', hm''⟩)⟩ := h,
  { exact hχ ⟨m, 0, hm.2⟩ },
  have : disjoint m x,
  { refine disjoint.mono_left hm _,
    simp only [disjoint_right, common_blues, mem_filter, mem_col_neighbors, mem_univ, true_and,
      not_forall, not_exists],
    intros i hi,
    exact ⟨i, hi, λ q, (q rfl).elim⟩ },
  refine hχ ⟨m ∪ x, 1, _, by simpa [this] using hm''⟩,
  rw [coe_union, top_edge_labelling.monochromatic_of_union],
  exact ⟨hm', hx.1, monochromatic_between_common_blues.symm.subset_left hm⟩,
end

lemma nine_one_part_two {k l n : ℕ} {γ δ : ℝ} {χ : top_edge_labelling (fin n) (fin 2)}
  {x : finset (fin n)}
  (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
  (hml : x.card < l) (hl₀ : 0 < l) (hlk : l ≤ k)
  (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hm : exp (-δ * k) * (k + l).choose l ≤ n)
  (hx : is_good_clique (1 / 16) k l χ x)
  (hγ' : (l - x.card : ℝ) / (k + l - x.card) < (l / (k + l)) ^ 2) :
  false :=
begin
  have := nat.cast_le.1 ((U_lower_bound_ratio_lower_bound_aux_aux hml.le (hl₀.trans_le hlk) hγ hδ
    hγ' hm).trans hx.2),
  rw add_tsub_assoc_of_le hml.le at this,
  have := ramsey_number_le_finset (ramsey_number_le_choose'.trans this) χ,
  exact nine_one_end hχ hx this
end

lemma nine_one_part_three {k l m n : ℕ} {γ γ' δ : ℝ} {χ : top_edge_labelling (fin n) (fin 2)}
  (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
  (hml : m < l) (hk₀ : 0 < k)
  (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hγ' : γ' = (l - m) / (k + l - m))
  (h : exp (-δ * k) * ((k + l).choose l) * U_lower_bound_ratio (1 / 16) k l m <
    exp (-(γ' / 20) * k) * ↑((k + (l - m)).choose (l - m))) :
  false :=
begin
  have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml.le,
  rw [←nat.cast_add, add_comm l, add_tsub_assoc_of_le hml.le, nat.choose_symm_add] at this,
  rw [←not_le] at h,
  refine h _,
  rw [U_lower_bound_ratio, ←nat.cast_add, ←this, nat.choose_symm_add, mul_assoc, mul_div_assoc',
    mul_div_cancel', ←mul_assoc],
  swap,
  { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact nat.choose_pos (by simp) },
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le _)
    (exp_pos _).le).trans' _,
  rw [←exp_nat_mul, ←real.exp_add, exp_le_exp, hδ, neg_mul, neg_mul, neg_add_eq_sub,
    le_sub_iff_add_le, neg_add_eq_sub, mul_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    ←sub_div, hγ, hγ', ←sub_mul],
  refine div_le_div_of_le (by norm_num1) _,
  rw [←le_div_iff],
  swap,
  { rw [nat.cast_pos], exact hk₀ },
  refine (sub_le_sub_left (div_le_div_of_le_left _ _ (sub_le_self _ _)) _).trans _,
  { rw [sub_nonneg, nat.cast_le], exact hml.le },
  { rw [add_sub_assoc, ←nat.cast_sub hml.le], positivity },
  { exact nat.cast_nonneg _ },
  rw [←sub_div, sub_sub_self],
  exact div_le_div_of_le_left (nat.cast_nonneg _) (by positivity) (by simp),
end

lemma gamma'_le_gamma {k l m : ℕ} (hk : 0 < k) (h : m ≤ l) :
  (l - m : ℝ) / (k + l - m) ≤ l / (k + l) :=
begin
  rw [div_le_div_iff, ←sub_nonneg],
  { ring_nf,
    positivity },
  { rw [add_sub_assoc, ←nat.cast_sub h], positivity },
  { positivity },
end

lemma l_minus_m_big (γ₀ : ℝ) (hγ₀ : 0 < γ₀) {k l m : ℕ} (hml : m ≤ l) (hl₀ : 0 < l)
  (hkl : (k : ℝ) ≤ l * (γ₀⁻¹ - 1))
  (h₁ : 0 < γ₀⁻¹ - 1 + 2)
  (h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹)
  (hγ' : (m : ℝ) ≤ l * (k + ↑l) / (k + 2 * l)) :
  ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m :=
begin
  rw [nat.ceil_le, nat.cast_sub hml, le_sub_comm, ←mul_one_sub],
  refine hγ'.trans _,
  rw mul_div_assoc,
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  rw [div_le_iff, one_sub_mul, le_sub_comm, add_sub_add_left_eq_sub],
  swap,
  { positivity },
  refine (mul_le_mul_of_nonneg_left (add_le_add_right hkl _) h₂.le).trans _,
  rw [mul_comm (2 : ℝ), ←mul_add, mul_left_comm, inv_mul_cancel h₁.ne'],
  linarith
end

lemma nine_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ δ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 10 → δ = γ / 20 →
  (ramsey_number ![k, l] : ℝ) ≤ exp (- δ * k + 1) * (k + l).choose l :=
begin
  have h₁ : 0 < γ₀⁻¹ - 1 + 2 := by { rw [sub_add], norm_num, positivity },
  have h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹ := by positivity,
  have q := (tendsto_nat_ceil_at_top.comp (tendsto_id.at_top_mul_const' h₂)).comp
    tendsto_coe_nat_at_top_at_top,
  filter_upwards [top_adjuster (eventually_ge_at_top 2), eventually_gt_at_top 0,
    eventually_ge_at_top 256, eventually_gt_at_top (⌊γ₀⁻¹ - 1 + 2⌋₊),
    q.eventually (top_adjuster (nine_two_variant (γ₀ ^ 2) (pow_pos hγ₀ _)))] with
      l hk₂ hl₀ hk₂₅₆ hlγ₀ hk₉₂
    k γ δ hγ hγl hγu hδ,
  let n := ⌈(ramsey_number ![k, l] / exp 1 : ℝ)⌉₊,
  have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1)),
  have hnr : n < ramsey_number ![k, l],
  { rw [←@nat.cast_lt ℝ],
    refine nine_one_part_one _,
    simp only [nat.one_lt_cast],
    refine ramsey_number_ge_min _ _,
    simp only [fin.forall_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons],
    exact ⟨hk₂ _ hlk, hk₂ _ le_rfl⟩ },
  rw [←not_le, ramsey_number_le_iff_fin, is_ramsey_valid, not_forall] at hnr,
  obtain ⟨χ : top_edge_labelling (fin n) (fin 2), hχ⟩ := hnr,
  suffices : (n : ℝ) ≤ exp (- δ * k) * (k + l).choose l,
  { rw [add_comm, real.exp_add, mul_assoc, ←div_le_iff' (exp_pos _)],
    exact this.trans' (nat.le_ceil _) },
  by_contra' hm,
  classical,
  have : (univ.filter (is_good_clique (1 / 16) k l χ)).nonempty :=
    ⟨∅, by simp only [mem_filter, empty_is_good, mem_univ, true_and]⟩,
  obtain ⟨x, hx, hxy⟩ := exists_maximal _ this,
  simp only [mem_filter, mem_univ, true_and] at hx hxy,
  have hml := good_clique_bound hχ hx,
  let U := common_blues χ x,
  have hkl := small_k hγ₀ hγl hγ (hl₀.trans_le hlk),
  have : 256 ≤ U.card,
  { refine (hk₂₅₆.trans hlk).trans _,
    rw ←@nat.cast_le ℝ,
    refine hx.2.trans' _,
    refine U_lower_bound_ratio_lower_bound' hml (hl₀.trans_le hlk) hlk hγ hδ hm.le _,
    rw mul_comm,
    refine hkl.trans_lt _,
    refine mul_lt_mul_of_pos_left _ (nat.cast_pos.2 hl₀),
    rwa [lt_sub_iff_add_lt, ←nat.floor_lt' hl₀.ne'] },
  let m := x.card,
  let γ' : ℝ := (l - m) / (k + l - m),
  cases lt_or_le γ' ((l / (k + l)) ^ 2) with hγ' hγ',
  { exact nine_one_part_two hχ hml hl₀ hlk hγ hδ hm.le hx hγ' },
  have hγ'γ : γ' ≤ γ := (gamma'_le_gamma (hl₀.trans_le hlk) hml.le).trans_eq hγ.symm,
  have hlm : ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m,
  { rw [←not_lt, gamma'_le_gamma_iff hml.le (hl₀.trans_le hlk), not_lt] at hγ',
    exact l_minus_m_big _ hγ₀ hml.le hl₀ hkl h₁ h₂ hγ' },
  have hγ'_eq : γ' = ↑(l - m) / (↑k + ↑(l - m)),
  { rw [nat.cast_sub hml.le, add_sub_assoc'] },
  have hγ'₀ : 0 ≤ γ',
  { rw hγ'_eq,
    positivity },
  have hxy' : ∀ i ∉ x, is_good_clique (1 / 16) k l χ (insert i x) → false,
  { intros i hi hi',
    exact hxy (insert i x) hi' (ssubset_insert hi) },
  have := maximally_good_clique (by norm_num1) hχ (big_U this) (this.trans' (by norm_num1)) hx hxy',
  rw [one_add_mul, mul_comm (1 / 15 : ℝ), mul_one_div, ←sub_sub] at this,
  specialize hk₉₂ (l - m) hlm k γ' (γ' / 20) (γ' / 15) hγ'_eq (hγ'.trans' (pow_le_pow_of_le_left
    hγ₀.le (hγl.trans_eq hγ) _)) (hγ'γ.trans hγu) rfl (div_nonneg hγ'₀ (by norm_num1)) le_rfl _ _ _
    _ this,
  replace hk₉₂ := λ z, nine_one_end hχ hx (ramsey_number_le_finset_aux _ (hk₉₂ z)),
  rw [imp_false, not_le, fintype.subtype_card, filter_mem_eq_inter, univ_inter] at hk₉₂,
  replace hk₉₂ := hx.2.trans hk₉₂.le,
  replace hk₉₂ := (mul_lt_mul_of_pos_right hm (U_lower_bound_ratio_pos (by norm_num1)
    hml.le)).trans_le hk₉₂,
  exact nine_one_part_three hχ hml (hl₀.trans_le hlk) hγ hδ rfl hk₉₂,
end

lemma nine_one_o_filter (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ δ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 10 → δ = γ / 20 →
  (ramsey_number ![k, l] : ℝ) ≤ exp (- δ * k + f k) * (k + l).choose l :=
begin
  refine ⟨λ i, 1, _, nine_one_precise _ hγ₀⟩,
  exact is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_coe_nat_at_top_at_top,
end

lemma nine_one_nine : ∀ᶠ l in at_top, ∀ k, k = 9 * l →
  (ramsey_number ![k, l] : ℝ) ≤ exp (- l / 25) * (k + l).choose l :=
begin
  filter_upwards [nine_one_precise (1 / 10) (by norm_num1), eventually_ge_at_top 200] with l hl hl'
    k hk,
  subst hk,
  refine (hl (9 * l) (1 / 10) (1 / 10 / 20) _ le_rfl le_rfl rfl).trans _,
  { rw [nat.cast_mul, ←add_one_mul, mul_comm, ←div_div, div_self],
    { norm_num1 },
    { positivity } },
  refine mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (nat.cast_nonneg _),
  have : (200 : ℝ) ≤ l := by exact_mod_cast hl',
  rw [nat.cast_mul],
  norm_num1,
  linarith
end

end simple_graph
