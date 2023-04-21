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
lemma five_five {X Y : finset V} : 0 ≤ ∑ x y in X, pair_weight χ X Y x y :=
begin
  simp_rw [pair_weight, ←mul_sum, sum_sub_distrib],
  refine mul_nonneg (by positivity) (sub_nonneg_of_le _),
  exact five_five_aux
end

lemma five_six : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  k ^ 6 * ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤
    ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
end

end simple_graph
