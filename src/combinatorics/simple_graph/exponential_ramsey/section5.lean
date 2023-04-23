import combinatorics.simple_graph.exponential_ramsey.section4
import combinatorics.simple_graph.graph_probability
import algebra.order.chebyshev

open real

lemma mul_log_two_le_log_one_add {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) : ε * log 2 ≤ log (1 + ε) :=
begin
  rw le_log_iff_exp_le,
  swap,
  { linarith },
  have : 0 ≤ 1 - ε, { rwa sub_nonneg },
  have := convex_on_exp.2 (set.mem_univ 0) (set.mem_univ (log 2)) this hε (by simp),
  simp only [smul_eq_mul, mul_zero, zero_add, real.exp_zero, mul_one, exp_log two_pos] at this,
  refine this.trans_eq _,
  ring_nf
end

namespace simple_graph

open filter finset nat

lemma top_adjuster {p : ℕ → Prop} (h : ∀ᶠ k : ℕ in at_top, p k) :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k → p k :=
begin
  rw eventually_at_top at h ⊢,
  obtain ⟨n, hn⟩ := h,
  refine ⟨n, _⟩,
  rintro i (hi : n ≤ i) j hj,
  exact hn j (hi.trans hj),
end

lemma eventually_le_floor (c : ℝ) (hc : c < 1) :
  ∀ᶠ k : ℝ in at_top, c * k ≤ ⌊k⌋₊ :=
begin
  cases le_or_lt c 0,
  { filter_upwards [eventually_ge_at_top (0 : ℝ)] with x hx,
    exact (nat.cast_nonneg _).trans' (mul_nonpos_of_nonpos_of_nonneg h hx) },
  filter_upwards [eventually_ge_at_top (1 - c)⁻¹] with x hx,
  refine (nat.sub_one_lt_floor x).le.trans' _,
  rwa [le_sub_comm, ←one_sub_mul, ←div_le_iff', one_div],
  rwa sub_pos,
end

lemma ceil_eventually_le (c : ℝ) (hc : 1 < c) :
  ∀ᶠ k : ℝ in at_top, (⌈k⌉₊ : ℝ) ≤ c * k :=
begin
  filter_upwards [(tendsto_id.const_mul_at_top (sub_pos_of_lt hc)).eventually_ge_at_top 1,
    eventually_ge_at_top (0 : ℝ)] with x hx hx',
  refine (nat.ceil_lt_add_one hx').le.trans _,
  rwa [id.def, sub_one_mul, le_sub_iff_add_le'] at hx,
end

lemma is_o_rpow_rpow {r s : ℝ} (hrs : r < s) :
  (λ (x : ℝ), x ^ r) =o[at_top] (λ x, x ^ s) :=
begin
  rw asymptotics.is_o_iff,
  intros ε hε,
  have : 0 < s - r := sub_pos_of_lt hrs,
  filter_upwards [eventually_gt_at_top (0 : ℝ),
    (tendsto_rpow_at_top this).eventually_ge_at_top (1 / ε)] with x hx hx',
  rwa [norm_rpow_of_nonneg hx.le, norm_rpow_of_nonneg hx.le, norm_of_nonneg hx.le, ←div_le_iff' hε,
    div_eq_mul_one_div, ←le_div_iff' (rpow_pos_of_pos hx _), ←rpow_sub hx],
end

lemma is_o_id_rpow {s : ℝ} (hrs : 1 < s) : (λ x : ℝ, x) =o[at_top] (λ x, x ^ s) :=
by simpa only [rpow_one] using is_o_rpow_rpow hrs

lemma is_o_one_rpow {s : ℝ} (hrs : 0 < s) : (λ (x : ℝ), (1 : ℝ)) =o[at_top] (λ x, x ^ s) :=
by simpa only [rpow_zero] using is_o_rpow_rpow hrs

lemma one_lt_q_function_aux : ∀ᶠ k : ℕ in at_top,
  0.8 * (2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k) ≤ ⌊2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k⌋₊ :=
begin
  have : tendsto (λ x : ℝ, 2 * x ^ (1 / 4 : ℝ) * log x) at_top at_top,
  { refine tendsto.at_top_mul_at_top _ tendsto_log_at_top,
    exact (tendsto_rpow_at_top (by norm_num)).const_mul_at_top two_pos },
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have := (this.comp t).eventually (eventually_le_floor 0.8 (by norm_num)),
  filter_upwards [this] with k hk,
  rw [neg_div, rpow_neg (nat.cast_nonneg _), div_inv_eq_mul],
  exact hk,
end

lemma one_lt_q_function : ∀ᶠ k : ℕ in at_top,
  ∀ p₀ : ℝ, 0 ≤ p₀ →
  1 ≤ q_function k p₀ ⌊2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k⌋₊ :=
begin
  have hc : 1 < log 2 * (4 / 5 * 2),
  { rw [←div_lt_iff],
    { exact log_two_gt_d9.trans_le' (by norm_num) },
    norm_num },
  have := ((is_o_id_rpow hc).add (is_o_one_rpow (zero_lt_one.trans hc))).def zero_lt_one,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [eventually_ge_at_top 1, one_lt_q_function_aux, t.eventually_ge_at_top 1,
    t.eventually this]
    with k hk hk' hk₁ hk₂ --
    p₀ hp₀,
  have hk₀' : (0 : ℝ) < k := nat.cast_pos.2 hk,
  rw q_function,
  set ε : ℝ := (k : ℝ) ^ (-1 / 4 : ℝ),
  have hε : 0 < ε := rpow_pos_of_pos hk₀' _,
  have hε₁ : ε ≤ 1 := rpow_le_one_of_one_le_of_nonpos (nat.one_le_cast.2 hk) (by norm_num),
  refine le_add_of_nonneg_of_le hp₀ _,
  rw [one_le_div hk₀', le_sub_iff_add_le, ←rpow_nat_cast],
  refine (rpow_le_rpow_of_exponent_le _ hk').trans' _,
  { rw [le_add_iff_nonneg_right],
    exact hε.le },
  rw [rpow_def_of_pos, ←mul_assoc, ←mul_assoc, mul_comm, ←rpow_def_of_pos hk₀'],
  swap,
  { positivity },
  have : log 2 * (4 / 5 * 2) ≤ log (1 + ε) * (4 / 5) * (2 / ε),
  { rw [mul_div_assoc' _ _ ε, le_div_iff' hε, ←mul_assoc, mul_assoc (log _)],
    refine mul_le_mul_of_nonneg_right (mul_log_two_le_log_one_add hε.le hε₁) _,
    norm_num1 },
  refine (rpow_le_rpow_of_exponent_le hk₁ this).trans' _,
  rwa [norm_of_nonneg, one_mul, norm_of_nonneg] at hk₂,
  { exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
  positivity
end

lemma height_upper_bound : ∀ᶠ k : ℕ in at_top,
  ∀ p₀ : ℝ, 0 ≤ p₀ →
  ∀ p : ℝ, p ≤ 1 →
  (height k p₀ p : ℝ) ≤ 2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k :=
begin
  have : tendsto (λ k : ℝ, ⌊2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k⌋₊) at_top at_top,
  { refine tendsto_nat_floor_at_top.comp _,
    rw neg_div,
    refine tendsto.at_top_mul_at_top _ tendsto_log_at_top,
    have : ∀ᶠ k : ℝ in at_top, 2 * k ^ (1 / 4 : ℝ) = 2 / k ^ (-(1 / 4) : ℝ),
    { filter_upwards [eventually_ge_at_top (0 : ℝ)] with k hk,
      rw [rpow_neg hk, div_inv_eq_mul] },
    refine tendsto.congr' this _,
    exact (tendsto_rpow_at_top (by norm_num)).const_mul_at_top two_pos },
  have := this.comp tendsto_coe_nat_at_top_at_top,
  filter_upwards [eventually_ne_at_top 0, this.eventually_ge_at_top 1,
    one_lt_q_function] with k hk hk' hk'' --
    p₀ hp₀ p hp,
  rw [←nat.le_floor_iff', height, dif_pos],
  rotate,
  { exact ⟨hk, hp₀, hp⟩ },
  { rw ←pos_iff_ne_zero,
    exact one_le_height },
  refine nat.find_min' _ _,
  exact ⟨hk', hp.trans (hk'' p₀ hp₀)⟩,
end

open_locale big_operators

-- #check weight

variables {V : Type*} [decidable_eq V] [fintype V] {χ : top_edge_labelling V (fin 2)}

lemma five_five_aux_part_one {X Y : finset V} :
  ∑ x y in X, red_density χ X Y * ((red_neighbors χ x ∩ Y).card) =
    (red_density χ X Y) ^ 2 * X.card ^ 2 * Y.card :=
begin
  simp_rw [sum_const, nsmul_eq_mul, ←mul_sum],
  suffices : red_density χ X Y * X.card * Y.card = ∑ (x : V) in X, (red_neighbors χ x ∩ Y).card,
  { rw [←this, sq, sq],
    linarith only },
  rcases X.eq_empty_or_nonempty with rfl | hX,
  { rw [card_empty, nat.cast_zero, mul_zero, zero_mul, sum_empty] },
  rcases Y.eq_empty_or_nonempty with rfl | hY,
  { simp only [inter_empty, card_empty, nat.cast_zero, mul_zero, sum_const_zero] },
  rw [mul_assoc, red_density_eq_sum, div_mul_cancel],
  positivity
end

lemma five_five_aux_part_two {X Y : finset V} :
  ∑ x y in X, (red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card =
    ∑ z in Y, (red_neighbors χ z ∩ X).card ^ 2 :=
begin
  simp_rw [inter_comm, card_eq_sum_ones, ←@filter_mem_eq_inter _ _ Y, ←@filter_mem_eq_inter _ _ X,
    sum_filter, sq, sum_mul, mul_sum, boole_mul, ←ite_and, mem_inter, @sum_comm _ _ _ _ Y],
  refine sum_congr rfl (λ x hx, _),
  refine sum_congr rfl (λ x' hx', _),
  refine sum_congr rfl (λ y hy, _),
  refine if_congr _ rfl rfl,
  rw @mem_col_neighbor_finset_comm _ _ _ _ _ _ y,
  rw @mem_col_neighbor_finset_comm _ _ _ _ _ _ y,
end

lemma five_five_aux {X Y : finset V} :
  ∑ x y in X, red_density χ X Y * (red_neighbors χ x ∩ Y).card ≤
    ∑ x y in X, (red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card :=
begin
  simp only [←nat.cast_sum],
  rw [five_five_aux_part_one, five_five_aux_part_two, nat.cast_sum],
  have : (∑ z in Y, (red_neighbors χ z ∩ X).card : ℝ) ^ 2 ≤
    (Y.card : ℝ) * ∑ z in Y, ((red_neighbors χ z ∩ X).card : ℝ) ^ 2 := sq_sum_le_card_mul_sum_sq,
  rcases X.eq_empty_or_nonempty with rfl | hX,
  { simp },
  rcases Y.eq_empty_or_nonempty with rfl | hY,
  { simp },
  have hY : 0 < (Y.card : ℝ) := by positivity,
  rw [←div_le_iff' hY] at this,
  simp only [nat.cast_pow],
  refine this.trans_eq' _,
  rw [red_density, col_density_comm, ←red_density],
  rw [red_density_eq_sum, div_pow, div_mul_eq_mul_div, mul_pow, mul_div_mul_right,
    div_mul_eq_mul_div, sq (Y.card : ℝ), mul_div_mul_right _ _ hY.ne'],
  positivity
end

-- (13) observation 5.5
lemma five_five (χ : top_edge_labelling V (fin 2)) (X Y : finset V) :
  0 ≤ ∑ x y in X, pair_weight χ X Y x y :=
begin
  simp_rw [pair_weight, ←mul_sum, sum_sub_distrib],
  refine mul_nonneg (by positivity) (sub_nonneg_of_le _),
  exact five_five_aux
end

lemma tendsto_nat_ceil_at_top {α : Type*} [linear_ordered_semiring α] [floor_semiring α] :
  tendsto (λ (x : α), ⌈x⌉₊) at_top at_top :=
nat.ceil_mono.tendsto_at_top_at_top (λ n, ⟨n, (nat.ceil_nat_cast _).ge⟩)

lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
  log x ≤ log y :=
(log_le_log hx (hx.trans_le hxy)).2 hxy

lemma log_n_large (c : ℝ) : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  c ≤ 1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have := ((tendsto_rpow_at_top h34).at_top_mul_at_top tendsto_log_at_top).const_mul_at_top
    (show (0 : ℝ) < 1 / 128, by norm_num),
  filter_upwards [(this.comp t).eventually_ge_at_top c, t.eventually_gt_at_top (0 : ℝ)] with
    l hl hl' k hlk,
  refine hl.trans _,
  dsimp,
  rw ←mul_assoc,
  exact mul_le_mul_of_nonneg_left (log_le_log_of_le hl' (nat.cast_le.2 hlk)) (by positivity),
end

lemma five_six_aux_left_term : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  (⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ : ℝ) ^ ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ *
    ((k : ℝ) ^ (-1/8 : ℝ)) ^ ((⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 / 4) < 1 / 2 :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h12 : (0 : ℝ) < 1 / 2, { norm_num },
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have h32 : (0 : ℝ) < 3 / 2, { norm_num },
  have := ((tendsto_rpow_at_top h34).comp t).eventually (ceil_eventually_le 2 one_lt_two),
  filter_upwards [this, log_n_large 1, t.eventually_gt_at_top (1 : ℝ),
    (((tendsto_rpow_at_top h32).at_top_mul_at_top tendsto_log_at_top).comp t).eventually_gt_at_top
      (64 * log 2)] with l h₁ h₂ h₃ h₄
    k hlk,
  dsimp at h₁,
  specialize h₂ k hlk,
  have h₃' : (1 : ℝ) < k := h₃.trans_le (nat.cast_le.2 hlk),
  have h₃'1 : (0 : ℝ) < k := zero_lt_one.trans h₃',
  have h'₁ : (0 : ℝ) < ⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊,
  { rw [nat.cast_pos, nat.floor_pos],
    exact one_le_exp (h₂.trans' zero_le_one) },
  rw [←rpow_mul (nat.cast_nonneg k), ←log_lt_log_iff],
  rotate,
  { exact mul_pos (pow_pos h'₁ _) (rpow_pos_of_pos h₃'1 _) },
  { norm_num1 },
  rw [log_mul, log_pow, log_rpow h₃'1, mul_comm],
  rotate,
  { exact (pow_pos h'₁ _).ne' },
  { exact (rpow_pos_of_pos h₃'1 _).ne' },
  refine (add_le_add_right (mul_le_mul (log_le_log_of_le h'₁ (nat.floor_le (exp_pos _).le)) h₁
    (nat.cast_nonneg _) _) _).trans_lt _,
  { rw log_exp,
    exact h₂.trans' zero_le_one },
  rw [log_exp, neg_div, neg_mul, div_mul_div_comm, one_mul, mul_right_comm, ←add_mul,
    mul_mul_mul_comm, ←rpow_add (zero_lt_one.trans h₃), mul_comm (1 / 128 : ℝ), ←div_eq_mul_one_div,
    div_eq_mul_one_div (_ ^ 2 : ℝ)],
  have : (l : ℝ) ^ (2 * (3 / 4) : ℝ) ≤ (⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2,
  { calc _ = (l : ℝ) ^ ((3 / 4) * 2 : ℝ) : by rw [mul_comm]
      ... = ((l : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℝ) : rpow_mul (nat.cast_nonneg _) _ _
      ... = ((l : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℕ) : rpow_two _
      ... ≤ (⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 :
        pow_le_pow_of_le_left (by positivity) (nat.le_ceil _) _ },
  refine (mul_le_mul_of_nonneg_right (add_le_add_left (neg_le_neg (mul_le_mul_of_nonneg_right
    this (by norm_num))) _) (log_nonneg h₃'.le)).trans_lt _,
  rw [←two_mul, mul_comm (_ / _), ←sub_eq_add_neg, ←mul_sub, mul_right_comm],
  norm_num1,
  rw [one_div (2 : ℝ), mul_neg, log_inv, neg_lt_neg_iff, ←div_eq_mul_one_div, lt_div_iff'],
  swap,
  { norm_num },
  exact (mul_le_mul_of_nonneg_left (log_le_log_of_le (zero_lt_one.trans h₃) (nat.cast_le.2 hlk))
    (by positivity)).trans_lt' h₄,
end

lemma five_six_aux_right_term_aux : ∀ᶠ k : ℝ in at_top,
  1 ≤ 32 * k ^ (1 / 8 : ℝ) - log k :=
begin
  have h8 : (0 : ℝ) < 1 / 8, { norm_num },
  filter_upwards [(is_o_log_rpow_at_top h8).def zero_lt_one,
    (tendsto_rpow_at_top h8).eventually_ge_at_top 1,
    tendsto_log_at_top.eventually_ge_at_top (0 : ℝ),
    eventually_ge_at_top (0 : ℝ)] with x hx hx' hxl hx₀,
  rw [norm_of_nonneg hxl, norm_of_nonneg (rpow_nonneg_of_nonneg hx₀ _), one_mul] at hx,
  linarith only [hx, hx']
end

lemma five_six_aux_right_term : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  (⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ : ℝ) ^ k *
    exp (- k ^ (-1 / 8 : ℝ) * k ^ 2 / 4)
    < 1 / 2 :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h : (0 : ℝ) < 3 / 4 + 1, { norm_num1 },
  filter_upwards [eventually_gt_at_top 1, log_n_large 1,
    top_adjuster (((tendsto_rpow_at_top h).comp t).eventually_gt_at_top (128 * log 2)),
    top_adjuster (t.eventually five_six_aux_right_term_aux)] with
    l h₁ h₂ h₃ h₄ --
    k hlk,
  specialize h₂ k hlk,
  have h'₁ : (0 : ℝ) < ⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊,
  { rw [nat.cast_pos, nat.floor_pos],
    exact one_le_exp (h₂.trans' zero_le_one) },
  rw [neg_mul, ←rpow_two, ←rpow_add, ←log_lt_log_iff (mul_pos (pow_pos h'₁ _) (exp_pos _)),
    log_mul (pow_ne_zero _ h'₁.ne') (exp_pos _).ne', log_exp, log_pow],
  rotate,
  { norm_num1 },
  { rwa nat.cast_pos,
    exact zero_lt_one.trans (h₁.trans_le hlk) },
  refine (add_le_add_right (mul_le_mul_of_nonneg_left (log_le_log_of_le h'₁ (nat.floor_le
    (exp_pos _).le)) (nat.cast_nonneg _)) _).trans_lt _,
  rw [log_exp, mul_right_comm, ←mul_assoc],
  refine (add_le_add_right (mul_le_mul_of_nonneg_left (rpow_le_rpow (nat.cast_nonneg _)
    (nat.cast_le.2 hlk) _) (mul_nonneg (nat.cast_nonneg _) (mul_nonneg _ _))) _).trans_lt _,
  { norm_num1 },
  { norm_num1 },
  { exact log_nonneg (nat.one_le_cast.2 (h₁.le.trans hlk)) },
  rw [mul_comm, ←mul_assoc, ←rpow_add_one, neg_div, ←sub_eq_add_neg, ←mul_assoc],
  swap,
  { rw [nat.cast_ne_zero],
    linarith only [h₁.le.trans hlk] },
  have h : (k : ℝ) ^ ((-1) / 8 + 2 : ℝ) / 4 =
    k ^ (3 / 4 + 1 : ℝ) * (1 / 128) * (32 * k ^ (1 / 8 : ℝ)),
  { rw [←div_eq_mul_one_div, div_eq_mul_one_div _ (4 : ℝ), div_mul_eq_mul_div, mul_left_comm,
      ←rpow_add, ←div_mul_eq_mul_div, mul_comm],
    { norm_num1, refl },
    rwa nat.cast_pos,
    exact zero_lt_one.trans (h₁.trans_le hlk) },
  rw [h, ←mul_sub, one_div (2 : ℝ), log_inv, lt_neg, ←mul_neg, neg_sub, mul_one_div,
    div_mul_eq_mul_div, lt_div_iff'],
  swap, { norm_num1 },
  refine (h₃ _ hlk).trans_le _,
  exact le_mul_of_one_le_right (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (h₄ _ hlk),
end

lemma five_six_aux_part_one : ∃ c : ℝ, 0 < c ∧ ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  exp (c * l ^ (3 / 4 : ℝ) * log k) ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
  refine ⟨1 / 128, by norm_num, _⟩,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_at_top h34)).comp t,
  filter_upwards [eventually_gt_at_top 1, eventually_ge_at_top 2,
    this.eventually_ge_at_top 2, five_six_aux_left_term, five_six_aux_right_term]
    with l hl₁ℕ hl₂ℕ hl₃ hf' hf'' k hlk,
  have hl₁ℝ : (1 : ℝ) < l := nat.one_lt_cast.2 hl₁ℕ,
  have hk₁ℕ : 1 < k := hl₁ℕ.trans_le hlk,
  have hk₁ℝ : (1 : ℝ) < k := nat.one_lt_cast.2 hk₁ℕ,
  refine le_of_lt _,
  rw ←nat.floor_lt (exp_pos _).le,
  specialize hf' k hlk,
  specialize hf'' k hlk,
  set p : ℝ := k ^ (-1/8 : ℝ),
  have hp₀ : 0 < p,
  { refine rpow_pos_of_pos _ _,
    refine hk₁ℝ.trans_le' (by norm_num) },
  have hp₁ : p < 1,
  { refine rpow_lt_one_of_one_lt_of_neg hk₁ℝ _,
    norm_num1 },
  rw ramsey_number_pair_swap,
  refine basic_off_diagonal_ramsey_bound hp₀ hp₁ hl₃ (hl₂ℕ.trans hlk) _,
  exact (add_lt_add hf' hf'').trans_eq (by norm_num),
end

lemma five_six : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  k ^ 6 * ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤
    ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
  obtain ⟨c, hc, hf⟩ := five_six_aux_part_one,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h23 : (0 : ℝ) < 2 / 3, { norm_num },
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have h2334 : (2 / 3 : ℝ) < (3 / 4), { norm_num },
  have hc6 : 0 < c / 6, { positivity },
  have := ((is_o_one_rpow h34).add (is_o_rpow_rpow h2334)).def hc6,
  filter_upwards [hf, top_adjuster (t.eventually_gt_at_top 0),
    top_adjuster ((tendsto_log_at_top.comp t).eventually_ge_at_top 0),
    ((tendsto_rpow_at_top h23).comp t).eventually (ceil_eventually_le 6 (by norm_num)),
    t.eventually (((is_o_one_rpow h34).add (is_o_rpow_rpow h2334)).def hc6)] with
    l hl hl₀ hll₀ hl' hl₁
    k hlk,
  specialize hl k hlk,
  rw ramsey_number_pair_swap,
  refine (nat.mul_le_mul_left _ ramsey_number_le_right_pow_left').trans _,
  rw [←@nat.cast_le ℝ, ←pow_add, nat.cast_pow],
  refine hl.trans' _,
  rw [←log_le_iff_le_exp (pow_pos (hl₀ _ hlk) _), log_pow, nat.cast_add, nat.cast_bit0,
    nat.cast_bit1, nat.cast_one],
  refine mul_le_mul_of_nonneg_right _ (hll₀ _ hlk),
  refine (add_le_add_left hl' _).trans _,
  rw [←mul_one_add, ←le_div_iff', ←div_mul_eq_mul_div],
  swap,
  { norm_num1 },
  refine ((le_norm_self _).trans hl₁).trans_eq _,
  rw [norm_of_nonneg],
  exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _,
end

lemma abs_pair_weight_le_one {X Y : finset V} {x y : V} : |pair_weight χ X Y x y| ≤ 1 :=
begin
  rw [pair_weight, abs_mul, abs_inv],
  cases nat.eq_zero_or_pos Y.card,
  { rw [h, nat.cast_zero, abs_zero, inv_zero, zero_mul],
    exact zero_le_one },
  rw [nat.abs_cast, inv_mul_le_iff, mul_one],
  swap,
  { rwa nat.cast_pos },
  have hr₀ : 0 ≤ red_density χ X Y,
  { rw [red_density, col_density, rat.cast_nonneg],
    exact edge_density_nonneg _ _ _ },
  have hr₁ : red_density χ X Y ≤ 1,
  { rw [red_density, col_density, ←rat.cast_one, rat.cast_le],
    exact edge_density_le_one _ _ _ },
  have : set.uIcc (red_density χ X Y * (red_neighbors χ x ∩ Y).card)
    (red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card ⊆
    set.uIcc 0 Y.card,
  { rw [set.uIcc_subset_uIcc_iff_mem, set.uIcc_of_le, set.mem_Icc, set.mem_Icc, and_assoc],
    swap,
    { exact nat.cast_nonneg _ },
    exact ⟨by positivity, mul_le_of_le_one_of_le' hr₁ (nat.cast_le.2 (card_le_of_subset
      (inter_subset_right _ _))) hr₀ (nat.cast_nonneg _), nat.cast_nonneg _, nat.cast_le.2
      (card_le_of_subset (inter_subset_right _ _))⟩ },
  refine (set.abs_sub_le_of_uIcc_subset_uIcc this).trans _,
  simp
end

lemma sum_pair_weight_eq {X Y : finset V} (y : V) (hy : y ∈ X) :
  ∑ x in X, pair_weight χ X Y y x = weight χ X Y y + pair_weight χ X Y y y :=
by rw [weight, sum_erase_add _ _ hy]

lemma double_sum_pair_weight_eq {X Y : finset V} :
  ∑ x y in X, pair_weight χ X Y x y = ∑ y in X, (weight χ X Y y + pair_weight χ X Y y y) :=
sum_congr rfl sum_pair_weight_eq

lemma sum_pair_weight_le {X Y : finset V} (y : V) (hy : y ∈ X) :
  weight χ X Y y + pair_weight χ X Y y y ≤ X.card :=
begin
  rw [←sum_pair_weight_eq _ hy],
  refine le_of_abs_le ((abs_sum_le_sum_abs _ _).trans _),
  refine (sum_le_card_nsmul _ _ 1 _).trans_eq (nat.smul_one_eq_coe _),
  intros x hx,
  exact abs_pair_weight_le_one,
end

variables (μ : ℝ)
lemma five_four_aux (k l : ℕ) (ini : book_config χ) (i : ℕ)
  (hi : i ∈ red_or_density_steps μ k l ini) :
  (0 : ℝ) ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] * (algorithm μ k l ini i).X.card +
    ((algorithm μ k l ini i).X.card - ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊]) *
    (weight χ (algorithm μ k l ini i).X (algorithm μ k l ini i).Y (get_x k l i hi) + 1) :=
begin
  set C := algorithm μ k l ini i,
  let m := ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊],
  have hi' := hi,
  simp only [red_or_density_steps, mem_filter, mem_range] at hi',
  change (0 : ℝ) ≤ m * C.X.card +
    (C.X.card - m) * (weight χ C.X C.Y (get_x k l i hi) + 1),
  refine (five_five χ C.X C.Y).trans _,
  rw [double_sum_pair_weight_eq],
  rw book_config.num_big_blues at hi',
  have : C.X.card - m ≤ (book_config.central_vertices μ C).card,
  { rw [tsub_le_iff_right, book_config.central_vertices],
    refine (add_le_add_left hi'.2.2.le _).trans' ((card_union_le _ _).trans' (card_le_of_subset _)),
    rw ←filter_or,
    simp only [finset.subset_iff, mem_filter, true_and] {contextual := tt},
    intros x hx,
    exact le_total _ _ },
  obtain ⟨nei, Bnei, neicard⟩ := exists_smaller_set _ _ this,
  have : ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] < C.X.card :=
    ramsey_number_lt_of_lt_final_step hi'.1,
  have hm : m ≤ C.X.card,
  { refine this.le.trans' _,
    refine ramsey_number.mono_two le_rfl _,
    refine nat.ceil_mono _,
    rcases nat.eq_zero_or_pos l with rfl | hl,
    { rw [nat.cast_zero, zero_rpow, zero_rpow]; norm_num1 },
    refine rpow_le_rpow_of_exponent_le _ (by norm_num1),
    rwa [nat.one_le_cast, nat.succ_le_iff] },
  have : book_config.central_vertices μ C ⊆ C.X := filter_subset _ _,
  have h : (C.X \ nei).card = m,
  { rw [card_sdiff (Bnei.trans this), neicard, nat.sub_sub_self hm] },
  rw [←sum_sdiff (Bnei.trans this), ←nsmul_eq_mul, ←nat.cast_sub hm, ←neicard, ←h, ←nsmul_eq_mul],
  refine add_le_add (sum_le_card_nsmul _ _ _ _) (sum_le_card_nsmul _ _ _ _),
  { intros x hx,
    exact sum_pair_weight_le x (sdiff_subset _ _ hx)},
  intros x hx,
  refine add_le_add _ (le_of_abs_le abs_pair_weight_le_one),
  refine book_config.get_central_vertex_max _ _ _ _ _,
  exact Bnei hx,
end

example {x y : ℕ} (hy : 1 < y) (hx : 0 < x) : x < y * x :=
begin
  exact lt_mul_left hx hy,
end

lemma five_four_end : ∀ᶠ k : ℝ in at_top, 1 / (k ^ 6 - 1) + 1 / k ^ 6 ≤ 1 / k ^ 5 :=
begin
  filter_upwards [eventually_ge_at_top (3 : ℝ)] with k hk₁,
  rw [←add_halves' (1 / k ^ 5), div_div],
  have h1 : 0 < k ^ 5 * 2,
  { positivity },
  suffices h2 : k ^ 5 * 2 ≤ k ^ 6 - 1,
  { refine add_le_add (one_div_le_one_div_of_le h1 h2) (one_div_le_one_div_of_le h1 (h2.trans _)),
    simp },
  rw [pow_succ' _ 5, le_sub_comm, ←mul_sub],
  exact one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le (hk₁.trans' (by norm_num)) _)
    (by linarith only [hk₁]),
end

lemma five_four :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
  ∀ i : ℕ,
  ∀ hi : i ∈ red_or_density_steps μ k l ini,
  - ((algorithm μ k l ini i).X.card : ℝ) / k ^ 5 ≤
    weight χ (algorithm μ k l ini i).X (algorithm μ k l ini i).Y (get_x k l i hi) :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h23 : (0 : ℝ) < 2 / 3, { norm_num },
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_at_top h23)).comp t,
  filter_upwards [five_six, this.eventually_ge_at_top 1,
    top_adjuster (eventually_gt_at_top 1),
    top_adjuster (t.eventually five_four_end)] with l hl hl' hl₂ hl₃
    k hlk n χ ini i hi,
  specialize hl₂ k hlk,
  specialize hl₃ k hlk,
  have hi' := hi,
  rw [red_or_density_steps, mem_filter, mem_range] at hi',
  set C := algorithm μ k l ini i,
  change - (C.X.card : ℝ) / k ^ 5 ≤ weight χ C.X C.Y (get_x k l i hi),
  let m := ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊],
  have h₅₄ : (0 : ℝ) ≤ m * C.X.card + (C.X.card - m) * (weight χ C.X C.Y _ + 1) :=
    five_four_aux μ k l ini i hi,
  have hm : 1 ≤ m,
  { refine ramsey_number_ge_min _ _,
    simp only [fin.forall_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
      hl₂.le, true_and, hl'] },
  have hX : k ^ 6 * m ≤ C.X.card := (hl k hlk).trans (ramsey_number_lt_of_lt_final_step hi'.1).le,
  have h : (k ^ 6 - 1 : ℝ) * m ≤ (C.X.card : ℝ) - m,
  { rw [sub_one_mul, sub_le_sub_iff_right],
    exact_mod_cast hX },
  have c : (k ^ 6 : ℝ) ≤ C.X.card,
  { rw [←nat.cast_pow, nat.cast_le],
    exact hX.trans' (nat.le_mul_of_pos_right hm) },
  have b' : (m : ℝ) < C.X.card,
  { rw [nat.cast_lt],
    refine hX.trans_lt' _,
    refine lt_mul_left hm _,
    exact one_lt_pow hl₂ (by norm_num) },
  have b : (0 : ℝ) < C.X.card - m,
  { rwa [sub_pos] },
  have : (0 : ℝ) < C.X.card,
  { refine b.trans_le _,
    simp only [sub_le_self_iff, nat.cast_nonneg] },
  rw [neg_div, div_eq_mul_one_div, ←mul_neg, ←le_div_iff' this],
  have : - (m / (C.X.card - m) + 1 / C.X.card : ℝ) ≤ weight χ C.X C.Y (get_x k l i hi) / C.X.card,
  { rw [neg_le_iff_add_nonneg', add_assoc, div_add_div_same, add_comm (1 : ℝ),
      div_add_div _ _ b.ne' this.ne'],
    exact div_nonneg h₅₄ (mul_nonneg b.le (nat.cast_nonneg _)) },
  refine this.trans' _,
  rw [neg_le_neg_iff],
  refine (add_le_add (div_le_div_of_le_left _ _ h)
    (div_le_div_of_le_left zero_le_one _ c)).trans _,
  { exact nat.cast_nonneg _ },
  { refine mul_pos (sub_pos_of_lt (one_lt_pow (nat.one_lt_cast.2 hl₂) (by norm_num1))) _,
    rwa nat.cast_pos },
  { refine pow_pos _ _,
    rwa nat.cast_pos,
    exact hl₂.le },
  rw [mul_comm, ←div_div, div_self],
  swap,
  { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact hm },
  exact hl₃
end

lemma five_seven_aux {k : ℕ} {p₀ p : ℝ} :
  α_function k (height k p₀ p) =
    (k : ℝ) ^ (- 1 / 4 : ℝ) * (q_function k p₀ (height k p₀ p - 1) - q_function k p₀ 0 + 1 / k) :=
by rw [α_function, q_function, q_function, pow_zero, sub_self, zero_div, add_zero, add_sub_cancel',
    ←add_div, sub_add_cancel, mul_div_assoc]

lemma height_spec {k : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) (hp₀ : 0 ≤ p₀) (hp₁ : p ≤ 1) :
  p ≤ q_function k p₀ (height k p₀ p) :=
begin
  rw [height, dif_pos],
  exact (nat.find_spec (q_function_above_p hk hp₀ hp₁)).2,
  exact ⟨hk, hp₀, hp₁⟩
end

lemma height_min {k h : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) (hp₀ : 0 ≤ p₀) (hp₁ : p ≤ 1) (hh : h ≠ 0) :
  p ≤ q_function k p₀ h → height k p₀ p ≤ h :=
begin
  intro h',
  rw [height, dif_pos],
  refine nat.find_min' (q_function_above_p hk hp₀ hp₁) ⟨hh.bot_lt, h'⟩,
  exact ⟨hk, hp₀, hp₁⟩
end

lemma q_increasing {k h₁ h₂ : ℕ} {p₀ : ℝ} (h : h₁ ≤ h₂) :
  q_function k p₀ h₁ ≤ q_function k p₀ h₂ :=
begin
  rw [q_function, q_function, add_le_add_iff_left],
  refine div_le_div_of_le (nat.cast_nonneg _) (sub_le_sub_right (pow_le_pow _ h) _),
  rw le_add_iff_nonneg_right,
  exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _,
end

lemma five_seven_left {k : ℕ} {p₀ p : ℝ} :
  (k : ℝ) ^ (- 1 / 4 : ℝ) / k ≤ α_function k (height k p₀ p) :=
begin
  rw [five_seven_aux, div_eq_mul_one_div],
  refine mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  rw [le_add_iff_nonneg_left, sub_nonneg],
  refine q_increasing _,
  exact nat.zero_le _
end

lemma α_one {k : ℕ} : α_function k 1 = (k : ℝ) ^ (- 1 / 4 : ℝ) / k :=
by rw [α_function, nat.sub_self, pow_zero, mul_one]

lemma five_seven_right {k : ℕ} {p₀ p : ℝ} (h : q_function k p₀ 0 ≤ p) (hk : k ≠ 0) (hp₀ : 0 ≤ p₀)
  (hp₁ : p ≤ 1) :
  α_function k (height k p₀ p) ≤ (k : ℝ) ^ (- 1 / 4 : ℝ) * (p - q_function k p₀ 0 + 1 / k) :=
begin
  rw [five_seven_aux],
  refine mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  simp only [add_le_add_iff_right, sub_le_sub_iff_right],
  by_contra',
  cases lt_or_eq_of_le (@one_le_height k p₀ p) with h₁ h₁,
  { have := height_min hk hp₀ hp₁ _ this.le,
    { rw ←not_lt at this,
      exact this (nat.sub_lt one_le_height zero_lt_one) },
    rwa [ne.def, nat.sub_eq_zero_iff_le, not_le] },
  rw h₁ at this,
  refine this.not_le _,
  rwa nat.sub_self,
end

lemma five_seven_extra {k : ℕ} {p₀ p : ℝ} (h' : p ≤ q_function k p₀ 1) :
  height k p₀ p = 1 :=
begin
  rw [height],
  split_ifs,
  { rw nat.find_eq_iff,
    simp [h'] },
  refl
end

-- WARNING: the hypothesis 1 / k ≤ ini.p should be seen as setting an absolute lower bound on p₀,
-- and k and ini both depend on it, with 1 / k ≤ it ≤ ini.p
lemma five_eight {μ : ℝ} {k l : ℕ} {ini : book_config χ} (h : 1 / (k : ℝ) ≤ ini.p)
  (hk : k ≠ 0)
  {i : ℕ} (hi : i ∈ degree_steps μ k l ini)
  (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
  (1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * (algorithm μ k l ini i).p * (algorithm μ k l ini (i + 1)).Y.card ≤
    (red_neighbors χ x ∩ (algorithm μ k l ini (i + 1)).Y).card :=
begin
  set C := algorithm μ k l ini i,
  set ε := (k : ℝ) ^ (- 1 / 4 : ℝ),
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_Y],
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_X, mem_filter] at hx,
  rw [degree_steps, mem_filter, mem_range] at hi,
  change (1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * C.p * C.Y.card ≤ (red_neighbors χ x ∩ C.Y).card,
  change x ∈ C.X ∧ (C.p - _ * α_function k (C.height k ini.p)) * (C.Y.card : ℝ) ≤
    (red_neighbors χ x ∩ C.Y).card at hx,
  have : 1 / (k : ℝ) < C.p := one_div_k_lt_p_of_lt_final_step hi.1,
  refine hx.2.trans' (mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _)),
  rw [one_sub_mul, sub_le_sub_iff_left],
  cases le_total C.p (q_function k ini.p 0) with h' h',
  { rw [book_config.height, five_seven_extra, α_one, mul_div_assoc', ←rpow_add' (nat.cast_nonneg _),
      div_eq_mul_one_div],
    { refine (mul_le_mul_of_nonneg_left this.le (rpow_nonneg_of_nonneg (nat.cast_nonneg _)
        _)).trans_eq _,
      norm_num },
    { norm_num },
    exact h'.trans (q_increasing zero_le_one) },
  refine (mul_le_mul_of_nonneg_left (five_seven_right h' hk _ _)
    (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)).trans _,
  { rw [book_config.p, red_density, col_density, ←rat.cast_zero, rat.cast_le],
    exact edge_density_nonneg _ _ _ },
  { rw [book_config.p, red_density, col_density, ←rat.cast_one, rat.cast_le],
    exact edge_density_le_one _ _ _ },
  rw [←mul_assoc, ←rpow_add' (nat.cast_nonneg _)],
  swap,
  { norm_num1 },
  refine mul_le_mul _ _ _ _,
  { refine le_of_eq _,
    norm_num },
  { rw [q_function_zero, sub_add, sub_le_self_iff, sub_nonneg],
    exact h },
  { refine add_nonneg _ _,
    { rwa sub_nonneg },
    { positivity } },
  { positivity }
end

end simple_graph
