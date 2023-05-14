import combinatorics.simple_graph.exponential_ramsey.section5

namespace simple_graph

open_locale big_operators exponential_ramsey

open filter finset nat real

variables {V : Type*} [decidable_eq V] [fintype V] {χ : top_edge_labelling V (fin 2)}
variables {μ p₀ : ℝ} {k l : ℕ} {ini : book_config χ} {i : ℕ}

meta def my_p : tactic unit := tactic.to_expr ```((algorithm μ k l ini Ᾰ).p) >>= tactic.exact
meta def my_p' : tactic unit := tactic.to_expr ```(λ i, (algorithm μ k l ini i).p) >>= tactic.exact
meta def my_r : tactic unit := tactic.to_expr ```(red_steps μ k l ini) >>= tactic.exact
meta def my_b : tactic unit := tactic.to_expr ```(big_blue_steps μ k l ini) >>= tactic.exact
meta def my_s : tactic unit := tactic.to_expr ```(density_steps μ k l ini) >>= tactic.exact
meta def my_d : tactic unit := tactic.to_expr ```(degree_steps μ k l ini) >>= tactic.exact
meta def my_ε : tactic unit := tactic.to_expr ```((k : ℝ) ^ (- 1 / 4 : ℝ)) >>= tactic.exact

local notation `p_` := λ Ᾰ, by my_p
local notation `ℛ` := by my_r
local notation `ℬ` := by my_b
local notation `𝒮` := by my_s
local notation `𝒟` := by my_d
local notation `ε` := by my_ε

lemma six_four_red (hi : i ∈ red_steps μ k l ini) :
  (algorithm μ k l ini i).p - α_function k (height k ini.p (algorithm μ k l ini i).p) ≤
    (algorithm μ k l ini (i + 1)).p :=
begin
  change (_ : ℝ) ≤ red_density χ _ _,
  rw [red_applied hi, book_config.red_step_basic_X, book_config.red_step_basic_Y],
  have hi' := hi,
  simp only [red_steps, mem_image, mem_filter, exists_prop, subtype.coe_mk, mem_attach,
    true_and, subtype.exists, exists_and_distrib_right, exists_eq_right] at hi',
  obtain ⟨hx, hx'⟩ := hi',
  exact hx'
end

lemma six_four_density (μ p₀ : ℝ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀ ≤ ini.p →
  ∀ i : ℕ,
    i ∈ density_steps μ k l ini →
  (algorithm μ k l ini i).p ≤ (algorithm μ k l ini (i + 1)).p :=
five_three_left _ _ hμ₁ hp₀

lemma six_four_density' (μ p₀ : ℝ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ 𝒮 → p_ i ≤ p_ (i + 1) :=
six_four_density μ p₀ hμ₁ hp₀

lemma increase_average {α : Type*} {s : finset α} {f : α → ℝ} {k : ℝ}
  (hk : k ≤ (∑ i in s, f i) / s.card) :
  (∑ i in s, f i) / s.card ≤
    (∑ i in s.filter (λ j, k ≤ f j), f i) / (s.filter (λ j, k ≤ f j)).card :=
begin
  classical,
  rcases s.eq_empty_or_nonempty with rfl | hs,
  { rw [filter_empty] },
  have hs' : (0 : ℝ) < s.card,
  { rwa [nat.cast_pos, card_pos] },
  have : (s.filter (λ j, k ≤ f j)).nonempty,
  { rw [nonempty_iff_ne_empty, ne.def, filter_eq_empty_iff],
    intro h,
    simp only [not_le] at h,
    rw le_div_iff' hs' at hk,
    refine (sum_lt_sum_of_nonempty hs h).not_le _,
    rwa [sum_const, nsmul_eq_mul] },
  have hs'' : (0 : ℝ) < (s.filter (λ j, k ≤ f j)).card,
  { rwa [nat.cast_pos, card_pos] },
  rw [div_le_div_iff hs' hs'', ←sum_filter_add_sum_filter_not s (λ j : α, k ≤ f j), add_mul,
    ←le_sub_iff_add_le', ←mul_sub, ←cast_card_sdiff (filter_subset _ s), mul_comm],
  have h₁ : ∑ i in s.filter (λ x, ¬k ≤ f x), f i ≤ (s.filter (λ x, ¬ k ≤ f x)).card * k,
  { rw [←nsmul_eq_mul],
    refine sum_le_card_nsmul _ _ _ _,
    simp [le_of_lt] {contextual := tt} },
  have h₂ : ((s.filter (λ x, k ≤ f x)).card : ℝ) * k ≤ ∑ i in s.filter (λ j, k ≤ f j), f i,
  { rw [←nsmul_eq_mul],
    refine card_nsmul_le_sum _ _ _ _,
    simp [le_of_lt] {contextual := tt} },
  refine (mul_le_mul_of_nonneg_left h₁ (nat.cast_nonneg _)).trans _,
  refine (mul_le_mul_of_nonneg_right h₂ (nat.cast_nonneg _)).trans' _,
  rw [←filter_not, mul_right_comm, mul_assoc],
end

lemma col_density_eq_average {i : fin 2} {X Y : finset V} :
  col_density χ i X Y = (∑ x in X, (col_neighbors χ i x ∩ Y).card / Y.card) / X.card :=
by rw [col_density_eq_sum, ←sum_div, div_div, mul_comm]

lemma six_four_degree (hi : i ∈ degree_steps μ k l ini) :
  p_ i ≤ p_ (i + 1) :=
begin
  change red_density χ _ _ ≤ red_density χ _ _,
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_X,
    book_config.degree_regularisation_step_Y],
  set C := algorithm μ k l ini i,
  set α := α_function k (C.height k ini.p),
  rw col_density_eq_average,
  have : C.X.filter (λ x, (C.p - k ^ (1 / 8 : ℝ) * α) * C.Y.card ≤
    ((col_neighbors χ 0 x ∩ C.Y).card)) = C.X.filter (λ x, C.p - k ^ (1 / 8 : ℝ) * α ≤
    (col_neighbors χ 0 x ∩ C.Y).card / C.Y.card),
  { refine filter_congr _,
    intros x hx,
    rw le_div_iff,
    rw [nat.cast_pos, card_pos],
    refine Y_nonempty _,
    rw [degree_steps, mem_filter, mem_range] at hi,
    exact hi.1 },
  rw this,
  rw col_density_eq_average,
  refine increase_average _,
  rw [←col_density_eq_average, book_config.p, sub_le_self_iff],
  exact mul_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (α_nonneg _ _),
end

lemma book_config.get_book_snd_nonempty (hμ₀ : 0 < μ) {X : finset V} (hX : X.nonempty) :
  (book_config.get_book χ μ X).2.nonempty :=
begin
  rw [←card_pos, ←@nat.cast_pos ℝ],
  refine book_config.get_book_relative_card.trans_lt' _,
  refine div_pos (mul_pos (pow_pos hμ₀ _) _) two_pos,
  rwa [nat.cast_pos, card_pos],
end

lemma six_four_blue' (hμ₀ : 0 < μ) (hi : i + 1 ∈ big_blue_steps μ k l ini) :
  p_ i - k ^ (1 / 8 : ℝ) * α_function k (height k ini.p (p_ i)) ≤ p_ (i + 2) :=
begin
  change _ ≤ red_density χ _ _,
  rw [big_blue_applied hi, book_config.big_blue_step_X, book_config.big_blue_step_Y],
  have h : i + 1 < final_step μ k l ini,
  { rw [big_blue_steps, mem_filter, mem_range] at hi,
    exact hi.1 },
  have hi' : i ∈ degree_steps μ k l ini,
  { rw [big_blue_steps, mem_filter, nat.even_add_one, not_not] at hi,
    rw [degree_steps, mem_filter, mem_range],
    exact ⟨h.trans_le' (nat.le_succ _), hi.2.1⟩ },
  rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_Y,
    ←degree_regularisation_applied hi'],
  rw [col_density_eq_average],
  let C := algorithm μ k l ini i,
  let C' := algorithm μ k l ini (i + 1),
  have : ∀ x ∈ (C'.big_blue_step μ).X, C.p - k ^ (1 / 8 : ℝ) * α_function k (C.height k ini.p) ≤
    (red_neighbors χ x ∩ C.Y).card / C.Y.card,
  { intros x hx,
    have : x ∈ (algorithm μ k l ini (i + 1)).X := book_config.get_book_snd_subset hx,
    rw [degree_regularisation_applied hi', book_config.degree_regularisation_step_X,
      mem_filter] at this,
    rw [le_div_iff],
    { exact this.2 },
    rw [nat.cast_pos, card_pos],
    refine Y_nonempty _,
    exact h.trans_le' (nat.le_succ _) },
  refine (div_le_div_of_le _ (card_nsmul_le_sum _ _ _ this)).trans' _,
  { exact nat.cast_nonneg _ },
  rw [book_config.big_blue_step_X, nsmul_eq_mul, mul_div_cancel_left],
  { refl },
  rw [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
  refine book_config.get_book_snd_nonempty hμ₀ _,
  exact X_nonempty h,
end

lemma six_four_blue (hμ₀ : 0 < μ) (hi : i ∈ big_blue_steps μ k l ini) :
  (algorithm μ k l ini (i - 1)).p -
    k ^ (1 / 8 : ℝ) * α_function k (height k ini.p (algorithm μ k l ini (i - 1)).p) ≤
    (algorithm μ k l ini (i + 1)).p :=
begin
  have hi' := hi,
  rw [big_blue_steps, mem_filter, ←nat.odd_iff_not_even, odd_iff_exists_bit1] at hi,
  obtain ⟨b, rfl⟩ := hi.2.1,
  refine six_four_blue' hμ₀ _,
  rw [bit1, nat.add_sub_cancel],
  exact hi'
end

lemma height_mono {p₁ p₂ : ℝ} (hk : k ≠ 0) (hp₀ : 0 ≤ p₀) (hp₂ : p₂ ≤ 1) (h : p₁ ≤ p₂) :
  height k p₀ p₁ ≤ height k p₀ p₂ :=
begin
  refine height_min hk hp₀ (h.trans hp₂) _ _,
  { rw ←pos_iff_ne_zero,
    exact one_le_height },
  exact h.trans (height_spec hk hp₀ hp₂),
end

lemma six_five_density (μ p₀ : ℝ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ density_steps μ k l ini →
  height k ini.p (algorithm μ k l ini i).p ≤ height k ini.p (algorithm μ k l ini (i + 1)).p :=
begin
  filter_upwards [six_four_density μ p₀ hμ₁ hp₀, top_adjuster (eventually_ne_at_top 0)] with
    l hl hk' k hlk n χ ini hini i hi,
  exact height_mono (hk' _ hlk) col_density_nonneg col_density_le_one (hl k hlk n χ ini hini i hi)
end

lemma six_five_degree (μ : ℝ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
  ∀ i : ℕ, i ∈ degree_steps μ k l ini →
  height k ini.p (algorithm μ k l ini i).p ≤ height k ini.p (algorithm μ k l ini (i + 1)).p :=
begin
  filter_upwards [top_adjuster (eventually_ne_at_top 0)] with l hk' k hlk n χ ini i hi,
  exact height_mono (hk' _ hlk) col_density_nonneg col_density_le_one (six_four_degree hi),
end

open_locale topology

-- lemma six_five_red_aux_delete_me :
--   ∀ᶠ ε : ℝ in 𝓝 0, ε + ε ^ 2 ≤ 1 :=
-- begin
--   have := (continuous_pow 2),
-- end

lemma six_five_red_aux :
  ∀ᶠ x : ℝ in 𝓝[≥] 0, x * (1 + x) ^ 2 + 1 ≤ (1 + x) ^ 2 :=
begin
  rw eventually_nhds_within_iff,
  filter_upwards [eventually_le_nhds (show (0 : ℝ) < 1 / 2, by norm_num)] with x hx₂ hx₀,
  rw set.mem_Ici at hx₀,
  rw ←sub_nonpos,
  ring_nf,
  refine mul_nonpos_of_nonpos_of_nonneg _ hx₀,
  rw [sub_nonpos, add_one_mul],
  nlinarith
end

lemma six_five_red_aux_glue :
  ∀ᶠ k : ℕ in at_top,
    (k : ℝ) ^ (-(1 / 4) : ℝ) * (1 + k ^ (- (1 / 4) : ℝ)) ^ 2 + 1 ≤
      (1 + (k : ℝ) ^ (-(1 / 4) : ℝ)) ^ 2 :=
begin
  suffices : tendsto (λ k : ℕ, (k : ℝ) ^ (-(1 / 4) : ℝ)) at_top (𝓝[≥] 0),
  { exact this.eventually six_five_red_aux },
  rw tendsto_nhds_within_iff,
  refine ⟨(tendsto_rpow_neg_at_top (by norm_num)).comp tendsto_coe_nat_at_top_at_top, _⟩,
  refine eventually_of_forall _,
  intros x,
  exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _,
end

lemma nat.cast_sub_le {x y : ℕ} : (x - y : ℝ) ≤ (x - y : ℕ) :=
by rw [sub_le_iff_le_add, ←nat.cast_add, nat.cast_le, ←tsub_le_iff_right]

lemma six_five_red (μ p₀ : ℝ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ red_steps μ k l ini →
  height k ini.p (algorithm μ k l ini i).p - 2 ≤ height k ini.p (algorithm μ k l ini (i + 1)).p :=
begin
  filter_upwards [top_adjuster (eventually_ne_at_top 0),
    top_adjuster six_five_red_aux_glue] with
    l hk' hk'' k hlk n χ ini hini i hi,
  set p := (algorithm μ k l ini i).p,
  set h := height k ini.p p,
  specialize hk' k hlk,
  cases lt_or_le h 4 with hh hh,
  { rw nat.lt_succ_iff at hh,
    rw tsub_le_iff_right,
    refine hh.trans _,
    rw [nat.succ_le_succ_iff, nat.succ_le_succ_iff],
    exact one_le_height },
  suffices ht : q_function k ini.p (h - 3) < (algorithm μ k l ini (i + 1)).p,
  { by_contra' ht',
    rw [lt_tsub_iff_right, nat.lt_iff_add_one_le, add_assoc, ←bit1, ←le_tsub_iff_right] at ht',
    swap,
    { exact hh.trans' (nat.le_succ _) },
    have := (q_increasing ht').trans_lt ht,
    exact this.not_le (height_spec hk' col_density_nonneg col_density_le_one) },
  refine (six_four_red hi).trans_lt' _,
  have : q_function k ini.p (h - 1) < p, { exact q_height_lt_p (hh.trans_lt' (by norm_num)) },
  refine (sub_lt_sub_right this _).trans_le' _,
  change q_function _ _ _ ≤ _ - α_function _ h,
  rw [q_function, q_function, add_sub_assoc, add_le_add_iff_left, α_function, ←sub_div],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  rw [le_sub_iff_add_le', add_sub_assoc', sub_le_sub_iff_right, neg_div],
  have : h - 1 = (h - 3) + 2,
  { rw [nat.sub_eq_iff_eq_add, add_assoc, ←bit1, nat.sub_add_cancel],
    { exact hh.trans' (nat.le_succ _) },
    { exact hh.trans' (by norm_num) } },
  rw [this, add_comm _ 2, pow_add, ←mul_assoc, ←add_one_mul],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _),
  exact hk'' k hlk,
end

lemma general_convex_thing {a x : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) (ha : a ≠ 0) :
  exp x ≤ 1 + (exp a - 1) * x / a :=
begin
  have h₁ : 0 ≤ x / a := div_nonneg hx (hx.trans hxa),
  have h₂ : 0 ≤ 1 - x / a,
  { rw sub_nonneg,
    exact div_le_one_of_le hxa (hx.trans hxa) },
  have := convex_on_exp.2 (set.mem_univ 0) (set.mem_univ a) h₂ h₁ (by simp),
  simp only [ha, smul_eq_mul, mul_zero, div_mul_cancel, ne.def, not_false_iff, zero_add,
    real.exp_zero, mul_one] at this,
  refine this.trans_eq _,
  ring_nf,
end

lemma general_convex_thing' {a x : ℝ} (hx : x ≤ 0) (hxa : a ≤ x) (ha : a ≠ 0) :
  exp x ≤ 1 + (exp a - 1) * x / a :=
begin
  have h₁ : 0 ≤ x / a := div_nonneg_of_nonpos hx (hx.trans' hxa),
  have h₂ : 0 ≤ 1 - x / a,
  { rwa [sub_nonneg, div_le_one_of_neg],
    exact lt_of_le_of_ne (hxa.trans hx) ha },
  have := convex_on_exp.2 (set.mem_univ 0) (set.mem_univ a) h₂ h₁ (by simp),
  simp only [ha, smul_eq_mul, mul_zero, div_mul_cancel, ne.def, not_false_iff, zero_add,
    real.exp_zero, mul_one] at this,
  refine this.trans_eq _,
  ring_nf,
end

lemma convex_thing_aux {x : ℝ} (hε : 0 ≤ x) (hx' : x ≤ 2 / 7) :
  exp (-(7 * log 2 / 4 * x)) ≤ 1 - 7 / 2 * (1 - 1 / sqrt 2) * x :=
begin
  have h' : 0 < log 2 := log_pos (by norm_num),
  let a := - log 2 / 2,
  have : - log 2 / 2 ≠ 0,
  { norm_num },
  refine (general_convex_thing' _ _ this).trans_eq _,
  { rw [neg_nonpos],
    positivity },
  { nlinarith },
  have : exp (-log 2 / 2) = 1 / sqrt 2,
  { rw [div_eq_mul_one_div, neg_mul, real.exp_neg, exp_mul, exp_log, rpow_div_two_eq_sqrt,
      rpow_one, one_div];
    norm_num },
  rw [this, neg_div, mul_div_assoc, neg_div, ←div_neg, neg_neg, div_div_eq_mul_div,
    sub_eq_add_neg _ (_ * _ : ℝ), add_right_inj, div_mul_eq_mul_div, div_mul_eq_mul_div, div_div,
    mul_right_comm _ (log 2), mul_right_comm _ (log 2), mul_div_mul_right _ _ h'.ne', ←neg_mul,
    ←mul_neg, neg_sub, mul_right_comm (7 / 2 : ℝ), mul_comm, mul_right_comm (7 : ℝ),
    ←div_mul_eq_mul_div],
  congr' 2,
  norm_num1
end

lemma convex_thing {x : ℝ} (hε : 0 ≤ x) (hε' : x ≤ 2 / 7) :
  exp (-(7 * log 2 / 4 * x)) ≤ 1 - x :=
begin
  refine (convex_thing_aux hε hε').trans _,
  rw sub_le_sub_iff_left,
  refine le_mul_of_one_le_left hε _,
  rw [←div_le_iff', le_sub_comm, one_div],
  swap, { norm_num1 },
  refine inv_le_of_inv_le (by norm_num) _,
  refine le_sqrt_of_sq_le _,
  norm_num,
end

lemma six_five_blue_aux :
  ∀ᶠ x : ℝ in 𝓝 0, 0 < x → (1 + x ^ 2) ^ (-⌊2 * x⁻¹⌋₊ : ℝ) ≤ 1 - x :=
begin
  have h₁ := tendsto_inv_zero_at_top.const_mul_at_top (show (0 : ℝ) < 2, by norm_num),
  have h₂ := h₁.eventually (eventually_le_floor (7 / 8) (by norm_num)),
  rw eventually_nhds_within_iff at h₂,
  filter_upwards [h₂, eventually_lt_nhds (show (0 : ℝ) < 1, by norm_num),
    eventually_le_nhds (show (0 : ℝ) < 2 / 7, by norm_num)] with x hε hε₁ hε₂₇
    hε₀,
  specialize hε hε₀,
  have : 7 / (4 * x) ≤ ⌊2 * x⁻¹⌋₊,
  { refine hε.trans_eq' _,
    rw [←div_div, div_eq_mul_inv, ←mul_assoc],
    norm_num },
  have h₃ : 1 < 1 + x ^ 2,
  { rw lt_add_iff_pos_right,
    exact pow_pos hε₀ _ },
  have h₄ : 0 < 1 + x ^ 2 := zero_lt_one.trans h₃,
  rw [←log_le_log (rpow_pos_of_pos h₄ _) (sub_pos_of_lt hε₁), log_rpow h₄, neg_mul, neg_le],
  refine (mul_le_mul this (mul_log_two_le_log_one_add (pow_nonneg hε₀.le _) _) (mul_nonneg
    (pow_nonneg hε₀.le _) (log_nonneg one_lt_two.le)) (nat.cast_nonneg _)).trans' _,
  { exact pow_le_one _ hε₀.le hε₁.le },
  have : 7 / (4 * x) * (x ^ 2 * log 2) = (7 * log 2 / 4) * x,
  { rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ←mul_assoc, mul_right_comm, sq, ←mul_assoc,
      mul_div_mul_right _ _ hε₀.ne'] },
  rw [this, neg_le, le_log_iff_exp_le (sub_pos_of_lt hε₁)],
  exact convex_thing hε₀.le hε₂₇,
end

lemma six_five_blue (μ p₀ : ℝ) (hμ₀ : 0 < μ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ big_blue_steps μ k l ini →
  (height k ini.p (algorithm μ k l ini (i - 1)).p : ℝ) - 2 * (k : ℝ) ^ (1 / 8 : ℝ) ≤
    height k ini.p (algorithm μ k l ini (i + 1)).p :=
begin
  have : tendsto (λ k : ℕ, (k : ℝ) ^ (-(1 / 8) : ℝ)) at_top (𝓝 0) :=
    (tendsto_rpow_neg_at_top (by norm_num)).comp tendsto_coe_nat_at_top_at_top,
  filter_upwards [top_adjuster (eventually_gt_at_top 0),
    top_adjuster (this.eventually six_five_blue_aux)] with
    l hk₀ hkε k hlk n χ ini hini i hi,
  specialize hk₀ k hlk,
  set p := (algorithm μ k l ini (i - 1)).p,
  set h := height k ini.p p,
  have hk : (0 : ℝ) ≤ k ^ (1 / 8 : ℝ) := (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  have hk' : (0 : ℝ) ≤ 2 * k ^ (1 / 8 : ℝ) := mul_nonneg two_pos.le hk,
  cases le_or_lt ((h : ℝ) - 2 * k ^ (1 / 8 : ℝ)) 1 with hh hh,
  { refine hh.trans _,
    rw nat.one_le_cast,
    exact one_le_height },
  have : q_function k ini.p (h - 1) < p,
  { refine q_height_lt_p _,
    rw ←@nat.one_lt_cast ℝ,
    refine hh.trans_le _,
    rw [sub_le_self_iff],
    exact hk' },
  change (h : ℝ) - _ ≤ _,
  rw [sub_le_iff_le_add, ←nat.le_floor_iff, add_comm, nat.floor_add_nat hk', ←tsub_le_iff_left],
  rotate,
  { exact add_nonneg (nat.cast_nonneg _) hk' },
  have z : 1 ≤ h - ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊,
  { rw [nat.succ_le_iff],
    refine nat.sub_pos_of_lt _,
    rw [nat.floor_lt hk', ←sub_pos],
    exact hh.trans_le' zero_le_one },
  suffices ht : q_function k ini.p (h - ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊ - 1) <
    (algorithm μ k l ini (i + 1)).p,
  { by_contra' ht',
    rw [nat.lt_iff_add_one_le, ←le_tsub_iff_right z] at ht',
    have := (q_increasing ht').trans_lt ht,
    exact this.not_le (height_spec hk₀.ne' col_density_nonneg col_density_le_one) },
  refine (six_four_blue hμ₀ hi).trans_lt' _,
  refine (sub_lt_sub_right this _).trans_le' _,
  rw [α_function, q_function, q_function, add_sub_assoc, add_le_add_iff_left, mul_div_assoc',
    ←sub_div],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  have hz : (0 : ℝ) < 1 + ε,
  { exact add_pos_of_pos_of_nonneg zero_lt_one (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
  rw [sub_sub, add_comm (1 : ℝ) (_ * _), ←sub_sub, sub_le_sub_iff_right, ←mul_assoc, ←one_sub_mul,
    tsub_tsub, add_comm _ 1, ←tsub_tsub, pow_sub₀, mul_comm],
  rotate,
  { exact hz.ne' },
  { rw [←@nat.cast_le ℝ],
    refine (nat.floor_le hk').trans _,
    refine nat.cast_sub_le.trans' _,
    rw [nat.cast_one, le_sub_comm],
    exact hh.le },
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg hz.le _),
  let ν : ℝ := k ^ (-(1 / 8) : ℝ),
  suffices : (1 + ν ^ 2) ^ (-⌊2 * ν⁻¹⌋₊ : ℝ) ≤ 1 - ν,
  { convert this using 2,
    { rw [←rpow_nat_cast, ←rpow_neg hz.le, ←rpow_neg (nat.cast_nonneg _), neg_neg,
        ←rpow_two, ←rpow_mul (nat.cast_nonneg _)],
      norm_num },
    rw [←rpow_add' (nat.cast_nonneg _)],
    { congr' 1,
      norm_num1 },
    norm_num1 },
  exact hkε k hlk (rpow_pos_of_pos (nat.cast_pos.2 hk₀) _),
end

noncomputable def decrease_steps (μ : ℝ) (k l : ℕ) (ini : book_config χ) : finset ℕ :=
  (red_steps μ k l ini ∪ big_blue_steps μ k l ini ∪ density_steps μ k l ini).filter
    (λ i, (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p)

lemma sub_one_mem_degree {i : ℕ} (hi : i < final_step μ k l ini) (hi' : odd i) :
  1 ≤ i ∧ i - 1 ∈ degree_steps μ k l ini :=
begin
  rw odd_iff_exists_bit1 at hi',
  obtain ⟨i, rfl⟩ := hi',
  refine ⟨by simp, _⟩,
  rw [bit1, nat.add_sub_cancel, degree_steps, mem_filter, mem_range],
  exact ⟨hi.trans_le' (nat.le_succ _), even_bit0 _⟩,
end

lemma big_blue_steps_sub_one_mem_degree {i : ℕ} (hi : i ∈ big_blue_steps μ k l ini) :
  1 ≤ i ∧ i - 1 ∈ degree_steps μ k l ini :=
begin
  rw [big_blue_steps, mem_filter, mem_range, ←nat.odd_iff_not_even] at hi,
  exact sub_one_mem_degree hi.1 hi.2.1,
end

lemma red_or_density_steps_sub_one_mem_degree {i : ℕ} (hi : i ∈ red_or_density_steps μ k l ini) :
  1 ≤ i ∧ i - 1 ∈ degree_steps μ k l ini :=
begin
  rw [red_or_density_steps, mem_filter, mem_range, ←nat.odd_iff_not_even] at hi,
  exact sub_one_mem_degree hi.1 hi.2.1,
end

lemma red_steps_sub_one_mem_degree {i : ℕ} (hi : i ∈ red_steps μ k l ini) :
  1 ≤ i ∧ i - 1 ∈ degree_steps μ k l ini :=
red_or_density_steps_sub_one_mem_degree (red_steps_subset_red_or_density_steps hi)

lemma density_steps_sub_one_mem_degree {i : ℕ} (hi : i ∈ density_steps μ k l ini) :
  1 ≤ i ∧ i - 1 ∈ degree_steps μ k l ini :=
red_or_density_steps_sub_one_mem_degree (density_steps_subset_red_or_density_steps hi)

lemma height_eq_one {p : ℝ} (h : p ≤ p₀) : height k p₀ p = 1 :=
begin
  apply five_seven_extra,
  rw [q_function, pow_one, add_sub_cancel'],
  refine h.trans _,
  simp only [le_add_iff_nonneg_right],
  positivity
end

lemma six_three_blue (μ p₀ : ℝ) (hμ₀ : 0 < μ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∑ i in (big_blue_steps μ k l ini).filter
    (λ i, (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p),
    ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
    ε :=
begin
  filter_upwards [top_adjuster (eventually_ge_at_top 1),
    four_three μ hμ₀] with l hl₁ hb
    k hlk n χ hχ ini hini,
  let BZ := (big_blue_steps μ k l ini).filter
    (λ i, (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p),
  change ∑ i in BZ, _ ≤ _,
  have : ∀ i ∈ BZ, (algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p ≤ 1 / k,
  { intros i hi,
    rw [mem_filter] at hi,
    have : height k ini.p (algorithm μ k l ini (i - 1)).p = 1,
    { refine height_eq_one _,
      exact hi.2.2 },
    have h' := six_four_blue hμ₀ hi.1,
    rw [this, sub_le_comm] at h',
    refine h'.trans _,
    rw [α_one, mul_div_assoc'],
    refine div_le_div_of_le (nat.cast_nonneg _) _,
    rw ←rpow_add' (nat.cast_nonneg _),
    refine rpow_le_one_of_one_le_of_nonpos (nat.one_le_cast.2 (hl₁ k hlk)) (by norm_num),
    norm_num },
  refine (sum_le_card_nsmul _ _ _ this).trans _,
  rw [nsmul_eq_mul, mul_one_div],
  have : (BZ.card : ℝ) ≤ l ^ (3 / 4 : ℝ),
  { refine (hb k hlk n χ hχ ini).trans' _,
    rw nat.cast_le,
    exact card_le_of_subset (filter_subset _ _) },
  refine (div_le_div_of_le _ this).trans _,
  { exact nat.cast_nonneg _ },
  have : (0 : ℝ) < k,
  { rwa nat.cast_pos,
    exact hl₁ k hlk },
  rw [div_le_iff this, ←rpow_add_one this.ne'],
  exact (rpow_le_rpow (nat.cast_nonneg _) (nat.cast_le.2 hlk) (by norm_num)).trans_eq (by norm_num)
end

lemma p₀_lt_of_one_lt_height {k : ℕ} {p₀ p : ℝ} (h : 1 < height k p₀ p) :
  p₀ < p :=
begin
  by_contra',
  rw height_eq_one this at h,
  simpa using h
end

lemma six_three_red_aux (μ p₀ : ℝ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i ∈ red_steps μ k l ini,
    (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p →
    (algorithm μ k l ini (i - 1)).p ≤ ini.p →
    ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
    ε / k :=
begin
  filter_upwards [top_adjuster (eventually_ge_at_top 1)] with l hl₁
    k hlk n χ ini hini i hi hi₁ hi₂,
  refine (sub_le_sub_left (six_four_red hi) _).trans _,
  cases eq_or_lt_of_le one_le_height,
  { rw [←sub_add, ←h, α_one, add_le_iff_nonpos_left, sub_nonpos],
    have := red_steps_sub_one_mem_degree hi,
    refine (six_four_degree this.2).trans_eq _,
    rw nat.sub_add_cancel this.1 },
  have m := p₀_lt_of_one_lt_height h,
  have : q_function k ini.p 0 ≤ (algorithm μ k l ini i).p,
  { rw q_function_zero,
    exact m.le },
  refine (sub_le_sub_right hi₂ _).trans _,
  rw ←sub_add,
  refine (add_le_add_left (five_seven_right this) _).trans _,
  rw [q_function_zero, mul_add, mul_one_div, ←add_assoc, add_le_iff_nonpos_left,
    ←le_neg_iff_add_nonpos_left, neg_sub],
  refine mul_le_of_le_one_left _ _,
  { rw sub_nonneg,
    exact m.le },
  refine rpow_le_one_of_one_le_of_nonpos _ (by norm_num),
  rw nat.one_le_cast,
  exact hl₁ k hlk
end

lemma six_three_red (μ p₀ : ℝ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∑ i in (red_steps μ k l ini).filter
    (λ i, (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p),
    ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
    ε :=
begin
  filter_upwards [eventually_gt_at_top 0, six_three_red_aux μ p₀] with l hl₀ hlr
    k hlk n χ hχ ini hini,
  let RZ := (red_steps μ k l ini).filter
    (λ i, (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p),
  change ∑ i in RZ, (_ : ℝ) ≤ _,
  have : ∀ i ∈ RZ, (algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p ≤
    ε / k,
  { intros i hi,
    simp only [RZ, mem_filter] at hi,
    exact hlr k hlk n χ ini hini i hi.1 hi.2.1 hi.2.2 },
  refine (sum_le_card_nsmul _ _ _ this).trans _,
  have : (RZ.card : ℝ) ≤ k,
  { rw nat.cast_le,
    refine (card_le_of_subset (filter_subset _ _)).trans _,
    exact four_four_red μ (hl₀.trans_le hlk).ne' hl₀.ne' hχ ini },
  rw [nsmul_eq_mul],
  refine (mul_le_mul_of_nonneg_right this _).trans_eq _,
  { positivity },
  rw mul_div_cancel',
  rw nat.cast_ne_zero,
  exact (hl₀.trans_le hlk).ne',
end

lemma six_three (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∑ i in decrease_steps μ k l ini,
    ((algorithm μ k l ini (i - 1)).p - (algorithm μ k l ini (i + 1)).p) ≤
    2 * ε :=
begin
  filter_upwards [six_four_density μ p₀ hμ₁ hp₀,
    six_three_red μ p₀, six_three_blue μ p₀ hμ₀] with l hld hlr hlb
    k hlk n χ hχ ini hini,
  specialize hlr k hlk n χ hχ ini hini,
  specialize hlb k hlk n χ hχ ini hini,
  have : (density_steps μ k l ini).filter
    (λ i, (algorithm μ k l ini (i + 1)).p < (algorithm μ k l ini (i - 1)).p ∧
          (algorithm μ k l ini (i - 1)).p ≤ ini.p) = ∅,
  { rw filter_eq_empty_iff,
    intros i hi,
    rw [not_and_distrib, not_lt],
    left,
    refine (hld k hlk n χ ini hini i hi).trans' _,
    have := density_steps_sub_one_mem_degree hi,
    refine (six_four_degree this.2).trans _,
    rw nat.sub_add_cancel this.1 },
  rw [decrease_steps, filter_union, this, union_empty, filter_union, sum_union],
  { clear this,
    refine (add_le_add hlr hlb).trans_eq _,
    rw two_mul },
  clear this hlr hlb,
  refine disjoint_filter_filter _,
  refine big_blue_steps_disjoint_red_or_density_steps.symm.mono_left _,
  exact red_steps_subset_red_or_density_steps
end

lemma α_increasing {h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) : α_function k h₁ ≤ α_function k h₂ :=
begin
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  refine mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  refine pow_le_pow _ _,
  { rw [le_add_iff_nonneg_right],
    exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
  exact nat.sub_le_sub_right hh _,
end

lemma six_four_weak_aux : ∀ᶠ k : ℝ in at_top, ∀ h : ℕ, 1 ≤ h →
    (1 + k ^ (- 1 / 4 : ℝ)) ^ (h + 2 - 1) ≤
      k ^ (1 / 8 : ℝ) * (1 + k ^ (- 1 / 4 : ℝ)) ^ (h - 1) :=
begin
  have h₄ := tendsto_rpow_neg_at_top (show (0 : ℝ) < 1 / 4, by norm_num),
  have h₈ := tendsto_rpow_at_top (show (0 : ℝ) < 1 / 8, by norm_num),
  have := eventually_le_nhds (show (0 : ℝ) < 1 / 4, by norm_num),
  filter_upwards [eventually_ge_at_top (0 : ℝ), h₄.eventually this,
    h₈.eventually_ge_at_top 2] with k hk₀ hk₄ hk₈ h hh,
  rw [nat.sub_add_comm hh, pow_add, mul_comm, neg_div],
  have : 0 ≤ 1 + k ^ -(1 / 4 : ℝ),
  { exact le_add_of_nonneg_of_le zero_le_one (rpow_nonneg_of_nonneg hk₀ _) },
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg this _),
  refine hk₈.trans' _,
  refine (pow_le_pow_of_le_left this (add_le_add_left hk₄ _) _).trans _,
  norm_num
end

lemma six_four_weak (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ∈ red_steps μ k l ini ∪ big_blue_steps μ k l ini ∪ density_steps μ k l ini →
  p_ (i + 1) ≤ ini.p →
  p_ (i - 1) - k ^ (1 / 8 : ℝ) * α_function k (height k ini.p (p_ (i - 1))) ≤ p_ (i + 1) :=
begin
  filter_upwards [six_four_density μ p₀ hμ₁ hp₀, six_five_red μ p₀,
    top_adjuster (tendsto_coe_nat_at_top_at_top.eventually six_four_weak_aux)] with l hl hr hk
    k hlk n χ ini hini i hi hi',
  simp only [mem_union, or_assoc] at hi,
  rcases hi with (hir | hib | his),
  rotate,
  { exact six_four_blue hμ₀ hib },
  { refine (hl k hlk n χ ini hini i his).trans' _,
    rw sub_le_iff_le_add,
    have := density_steps_sub_one_mem_degree his,
    refine (six_four_degree this.2).trans _,
    rw [nat.sub_add_cancel this.1, le_add_iff_nonneg_right],
    exact mul_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (α_nonneg _ _) },
  refine (six_four_red hir).trans' _,
  have hirs := red_steps_sub_one_mem_degree hir,
  have := six_four_degree hirs.2,
  rw nat.sub_add_cancel hirs.1 at this,
  refine sub_le_sub this _,
  have := hr k hlk n χ ini hini i hir,
  rw [height_eq_one hi', tsub_le_iff_right] at this,
  have : height k ini.p (algorithm μ k l ini i).p ≤
    height k ini.p (algorithm μ k l ini (i - 1)).p + 2,
  { refine this.trans _,
    rw add_le_add_iff_right,
    exact one_le_height },
  refine (α_increasing this).trans _,
  rw [α_function, α_function, mul_div_assoc'],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  rw [mul_left_comm],
  refine mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  exact hk _ hlk _ one_le_height,
end

lemma six_two_part_one {f : ℕ → ℝ}
  {j j' : ℕ} (hj : odd j) (hj' : odd j') (hjj : j' ≤ j) :
  f (j' + 1) - f (j + 1) = ∑ i in (finset.Icc (j' + 2) j).filter odd, (f (i - 1) - f (i + 1)) :=
begin
  rw odd_iff_exists_bit1 at hj hj',
  obtain ⟨j, rfl⟩ := hj,
  obtain ⟨j', rfl⟩ := hj',
  rw bit1_le_bit1 at hjj,
  have : (Icc (bit1 j' + 2) (bit1 j)).filter odd =
    (Icc (j' + 1) j).map ⟨(bit1 : ℕ → ℕ), λ i i', nat.bit1_inj⟩,
  { ext i,
    simp only [mem_filter, mem_Icc, finset.mem_map, odd_iff_exists_bit1, bit1, exists_prop,
      function.embedding.coe_fn_mk, and_assoc],
    split,
    { rintro ⟨hi, hi', i, rfl⟩,
      simp only [add_le_add_iff_right, bit0_le_bit0] at hi',
      rw [add_right_comm, add_le_add_iff_right, ←bit0_add, bit0_le_bit0] at hi,
      exact ⟨i, hi, hi', rfl⟩ },
    rintro ⟨i, hi, hi', rfl⟩,
    rw [add_right_comm, add_le_add_iff_right, add_le_add_iff_right, bit0_le_bit0,
      ←bit0_add, bit0_le_bit0],
    exact ⟨hi, hi', i, rfl⟩ },
  rw [this, sum_map, ←nat.Ico_succ_right, sum_Ico_eq_sum_range, nat.succ_sub_succ],
  have : ∀ k : ℕ, (f (bit1 (j' + 1 + k) - 1) - f (bit1 (j' + 1 + k) + 1)) =
    f (bit0 (j' + 1 + k)) - f (bit0 (j' + 1 + (k + 1))),
  { intro k,
    rw [bit1, nat.add_sub_cancel, add_assoc _ 1 1, ←bit0, ←bit0_add, add_assoc (j' + 1)] },
  dsimp,
  simp only [this],
  rw [sum_range_sub', add_zero, bit1, bit1, add_assoc, add_assoc, ←bit0, ←bit0_add, ←bit0_add,
    add_assoc, add_left_comm, add_tsub_cancel_of_le hjj, add_comm j],
end

lemma sum_le_of_nonneg {α : Type*} {f : α → ℝ} {s : finset α} :
  ∑ x in s, f x ≤ ∑ x in s.filter (λ i, 0 < f i), f x :=
begin
  rw [←sum_filter_add_sum_filter_not s (λ i, 0 < f i), add_le_iff_nonpos_right],
  exact sum_nonpos (by simp {contextual := tt})
end

lemma mem_union_of_odd {i : ℕ} (hi : odd i) (hi' : i < final_step μ k l ini) :
  i ∈ red_steps μ k l ini ∪ ℬ ∪ 𝒮 :=
begin
  rw [union_right_comm, red_steps_union_density_steps, union_comm, big_blue_steps,
    red_or_density_steps, ←filter_or, mem_filter, mem_range, ←and_or_distrib_left, ←not_lt,
    and_iff_left (em' _), ←nat.odd_iff_not_even, and_iff_left hi],
  exact hi'
end

lemma six_two_part_two {μ : ℝ} {k l : ℕ} {ini : book_config χ}
  {j j' : ℕ} (hjm : j < final_step μ k l ini)
  (hij : ∀ i : ℕ, j' + 1 ≤ i → i ≤ j → odd i → p_ (i - 1) ≤ ini.p) :
  ∑ i in (finset.Icc (j' + 2) j).filter odd, (p_ (i - 1) - p_ (i + 1)) ≤
    ∑ i in decrease_steps μ k l ini, (p_ (i - 1) - p_ (i + 1)) :=
begin
  have : ∑ i in (finset.Icc (j' + 2) j).filter odd, (p_ (i - 1) - p_ (i + 1)) ≤
    ∑ i in (finset.Icc (j' + 2) j).filter (λ i, odd i ∧ p_ (i + 1) < p_ (i - 1)),
      (p_ (i - 1) - p_ (i + 1)),
  { rw [←filter_filter],
    refine sum_le_of_nonneg.trans_eq _,
    simp only [sub_pos] },
  refine this.trans _,
  clear this,
  refine sum_le_sum_of_subset_of_nonneg _ _,
  swap,
  { simp only [mem_filter, nat.odd_iff_not_even, mem_Icc, not_and, not_le, and_imp, sub_nonneg,
      decrease_steps],
    intros i _ h _ _,
    exact h.le },
  intros i,
  simp only [mem_filter, decrease_steps, and_imp, mem_Icc],
  intros hi hi₁ hi₂ hi₃,
  refine ⟨_, hi₃, _⟩,
  { exact mem_union_of_odd hi₂ (hi₁.trans_lt hjm) },
  exact hij i (hi.trans' (nat.le_succ _)) hi₁ hi₂,
end

lemma six_two_part_three (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ j : ℕ, j < final_step μ k l ini → odd j →
  (algorithm μ k l ini (j + 1)).p ≤ ini.p → ini.p ≤ (algorithm μ k l ini (j - 1)).p →
  ini.p - ε ≤ (algorithm μ k l ini (j + 1)).p :=
begin
  filter_upwards [six_four_weak μ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_ge_at_top 1)] with l hl hl₁
    k hlk n χ hχ ini hini j hj hj₁ hj₂ hj₃,
  have : j ∈ red_steps μ k l ini ∪ big_blue_steps μ k l ini ∪ density_steps μ k l ini :=
    mem_union_of_odd hj₁ hj,
  refine (hl k hlk n χ ini hini j this hj₂).trans' _,
  have hj₄ : q_function k ini.p 0 ≤ (algorithm μ k l ini (j - 1)).p,
  { rw q_function_zero,
    exact hj₃ },
  rw [le_sub_comm],
  refine (mul_le_mul_of_nonneg_left (five_seven_right hj₄) (rpow_nonneg_of_nonneg
    (nat.cast_nonneg _) _)).trans _,
  rw [q_function_zero, ←mul_assoc, ←sub_add, mul_add],
  refine add_le_add _ _,
  { refine mul_le_of_le_one_left (sub_nonneg_of_le hj₃) _,
    rw [←rpow_add' (nat.cast_nonneg _)],
    refine rpow_le_one_of_one_le_of_nonpos (nat.one_le_cast.2 (hl₁ k hlk)) (by norm_num),
    norm_num1 },
  rw mul_right_comm,
  refine mul_le_of_le_one_left (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) _,
  rw [mul_one_div, ←rpow_sub_one],
  { exact rpow_le_one_of_one_le_of_nonpos (nat.one_le_cast.2 (hl₁ k hlk)) (by norm_num) },
  rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
  exact hl₁ k hlk
end

lemma six_two_main (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i < final_step μ k l ini → i ∉ 𝒟 →
  ini.p - 3 * ε ≤ p_ (i + 1) :=
begin
  filter_upwards [six_three μ p₀ hμ₀ hμ₁ hp₀,
    six_two_part_three μ p₀ hμ₀ hμ₁ hp₀] with l hl hl'
    k hlk n χ hχ ini hini j hj hj₁,
  cases le_or_lt ini.p (p_ (j + 1)),
  { refine h.trans' _,
    rw [sub_le_self_iff],
    positivity },
  dsimp at h,
  have hj₂ : odd j,
  { rw [degree_steps, mem_filter, mem_range] at hj₁,
    simpa only [hj, true_and, ←nat.odd_iff_not_even] using hj₁ },
  let js := (range (j + 1)).filter (λ j', odd j' ∧ ini.p ≤ p_ (j' - 1)),
  have hjs : js.nonempty,
  { rw [filter_nonempty_iff],
    refine ⟨1, _, odd_one, _⟩,
    { simp only [mem_range, lt_add_iff_pos_left],
      exact hj₂.pos },
    dsimp,
    rw [nat.sub_self, algorithm_zero] },
  let j' : ℕ := js.max' hjs,
  have hj' : j' ≤ j ∧ odd j' ∧ ini.p ≤ p_ (j' - 1),
  { simpa only [mem_filter, mem_range_succ_iff, and_imp] using finset.max'_mem _ hjs },
  have : ∀ i : ℕ, j' + 1 ≤ i → i ≤ j → odd i → p_ (i - 1) ≤ ini.p,
  { intros i hi₁ hi₂ hi₃,
    by_contra' hi₄,
    have : i ∈ js,
    { rw [mem_filter, mem_range_succ_iff],
      exact ⟨hi₂, hi₃, hi₄.le⟩ },
    rw nat.succ_le_iff at hi₁,
    exact (finset.le_max' _ _ this).not_lt hi₁ },
  dsimp at this,
  have p_first : p_ (j' + 1) - 2 * ε ≤ p_ (j + 1),
  { rw [sub_le_comm, six_two_part_one hj₂ hj'.2.1 hj'.1],
    refine (six_two_part_two hj this).trans _,
    exact hl k hlk n χ hχ ini hini },
  refine p_first.trans' _,
  have : p_ (j' + 1) ≤ ini.p,
  { cases eq_or_lt_of_le hj'.1 with hjj hjj,
    { rw hjj,
      exact h.le },
    rw ←nat.add_one_le_iff at hjj,
    refine this (j' + 2) (nat.le_succ _) _ (by simp [hj'] with parity_simps),
    cases eq_or_lt_of_le hjj with hjj' hjj',
    { rw [←hjj'] at hj₂,
      simp only [nat.odd_iff_not_even] at hj₂,
      refine (hj₂ _).elim,
      simpa with parity_simps using hj'.2.1 },
    rw nat.add_one_le_iff,
    exact hjj' },
  refine (sub_le_sub_right
    (hl' k hlk n χ hχ ini hini j' (hj'.1.trans_lt hj) hj'.2.1 this hj'.2.2) _).trans' _,
  rw [bit1, add_one_mul, sub_sub, add_comm],
end

lemma six_two (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i : ℕ, i ≤ final_step μ k l ini → ini.p - 3 * ε ≤ p_ i :=
begin
  filter_upwards [six_two_main μ p₀ hμ₀ hμ₁ hp₀] with l hl
    k hlk n χ hχ ini hini i hi,
  cases i,
  { rw [algorithm_zero, sub_le_self_iff],
    positivity },
  rw nat.succ_eq_add_one at hi ⊢,
  rw nat.succ_le_iff at hi,
  by_cases i ∈ 𝒟,
  { refine (six_four_degree h).trans' _,
    rw [degree_steps, mem_filter, even_iff_exists_two_mul, mem_range] at h,
    obtain ⟨(rfl | i), rfl⟩ := h.2,
    { dsimp,
      rw [mul_zero, algorithm_zero, sub_le_self_iff],
      positivity },
    have : 2 * i.succ = bit1 i + 1,
    { rw [nat.mul_succ, bit1, ←bit0_eq_two_mul, add_assoc] },
    rw this at *,
    refine hl k hlk n χ hχ ini hini (bit1 i) _ _,
    { exact hi.trans_le' (nat.le_succ _) },
    rw [degree_steps, mem_filter],
    simp },
  exact hl k hlk n χ hχ ini hini i hi h
end

lemma two_approx {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
  2 ^ (-2 * x) ≤ 1 - x :=
begin
  have p : - 2 * log 2 ≤ 0, { simp [log_nonneg one_le_two] },
  have hu₀ : x * (- 2 * log 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx p,
  have hu₁ : - log 2 ≤ x * (- 2 * log 2), { nlinarith },
  have := general_convex_thing' hu₀ hu₁ (neg_ne_zero.2 (log_pos one_lt_two).ne'),
  rw [←mul_assoc, ←mul_assoc, div_neg, mul_div_cancel _ (log_pos one_lt_two).ne', ←sub_eq_add_neg,
    mul_comm, ←rpow_def_of_pos zero_lt_two, mul_comm] at this,
  refine this.trans_eq _,
  rw [real.exp_neg, exp_log],
  { norm_num,
    rw [mul_comm, mul_one_div, mul_div_cancel_left],
    norm_num1 },
  norm_num1
end

lemma six_one_ind (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ∀ i, i ≤ final_step μ k l ini →
  ((1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * (ini.p - 3 * ε)) ^
    (red_or_density_steps μ k l ini ∩ range i).card *
    ini.Y.card ≤ (algorithm μ k l ini i).Y.card :=
begin
  have h₄ : (0 : ℝ) < 1 / 4 := by norm_num,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [top_adjuster (((tendsto_rpow_neg_at_top h₄).comp t).eventually
    (eventually_le_nhds (show 0 < p₀ / 3, by positivity))),
    top_adjuster (eventually_ge_at_top 1),
    top_adjuster (t.eventually_ge_at_top p₀⁻¹),
    six_two μ p₀ hμ₀ hμ₁ hp₀] with l hl hl' hl₂ hl₃
    k hlk n χ hχ ini hini i hi,
  induction i with i ih,
  { rw [nat.nat_zero_eq_zero, range_zero, inter_empty, card_empty,
      pow_zero, one_mul, algorithm_zero] },
  rw [nat.succ_le_iff] at hi,
  have hi' := hi,
  rw [←mem_range, ←union_partial_steps, mem_union, mem_union, or_assoc, or_rotate] at hi',
  rw [range_succ],
  rcases hi' with hib | hid | hirs,
  { have hi'' := finset.disjoint_left.1 big_blue_steps_disjoint_red_or_density_steps hib,
    rw [inter_insert_of_not_mem hi''],
    refine (ih hi.le).trans_eq _,
    rw [big_blue_applied hib, book_config.big_blue_step_Y] },
  { have hi'' := finset.disjoint_left.1
      degree_steps_disjoint_big_blue_steps_union_red_or_density_steps hid,
    rw [mem_union, not_or_distrib] at hi'',
    rw [inter_insert_of_not_mem hi''.2],
    refine (ih hi.le).trans_eq _,
    rw [degree_regularisation_applied hid, book_config.degree_regularisation_step_Y] },
  rw [inter_insert_of_mem hirs, card_insert_of_not_mem, pow_succ, mul_assoc],
  swap,
  { simp },
  have hk₈ : (0 : ℝ) ≤ 1 - k ^ (-1 / 8 : ℝ),
  { rw [sub_nonneg],
    refine rpow_le_one_of_one_le_of_nonpos _ (by norm_num),
    rw nat.one_le_cast,
    exact hl' k hlk },
  refine (mul_le_mul_of_nonneg_left (ih hi.le) (mul_nonneg _ _)).trans _,
  { exact hk₈ },
  { rw [sub_nonneg],
    refine hini.trans' _,
    rw [←le_div_iff', neg_div],
    { exact hl k hlk },
    norm_num1 },
  have hd : 1 ≤ i ∧ i - 1 ∈ degree_steps μ k l ini := red_or_density_steps_sub_one_mem_degree hirs,
  have : (algorithm μ k l ini i.succ).Y = red_neighbors χ (get_x hirs) ∩ (algorithm μ k l ini i).Y,
  { rw [←red_steps_union_density_steps, mem_union] at hirs,
    cases hirs with hir his,
    { rw [red_applied hir, book_config.red_step_basic_Y] },
    { rw [density_applied his, book_config.density_boost_step_basic_Y] } },
  rw this,
  have hp₀' : (1 : ℝ) / k ≤ ini.p,
  { refine hini.trans' _,
    rw [one_div],
    exact inv_le_of_inv_le hp₀ (hl₂ k hlk) },
  have := five_eight hp₀' hd.2 (get_x hirs),
  rw nat.sub_add_cancel hd.1 at this,
  refine (this (book_config.get_central_vertex_mem_X _ _ _)).trans' _,
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  refine mul_le_mul_of_nonneg_left _ hk₈,
  exact hl₃ k hlk n χ hχ ini hini (i - 1) ((nat.sub_le _ _).trans hi.le),
end

-- cocoloco
-- potential
-- wavelength
-- underground

lemma six_one_explicit (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  ((1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * (1 - 3 * ε / ini.p)) ^ (2 * k) *
    ini.p ^ ((red_steps μ k l ini).card + (density_steps μ k l ini).card) *
    ini.Y.card ≤ (end_state μ k l ini).Y.card :=
begin
  have h₄ : (0 : ℝ) < 1 / 4 := by norm_num,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [six_one_ind μ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (((tendsto_rpow_neg_at_top h₄).comp t).eventually
    (eventually_le_nhds (show 0 < p₀ / 3, by positivity))),
    top_adjuster (eventually_ge_at_top 1),
    top_adjuster (eventually_gt_at_top 0)] with l hl hl' hl₁ hl₀
    k hlk n χ hχ ini hini,
  have : red_or_density_steps μ k l ini ∩ range (final_step μ k l ini) =
    red_or_density_steps μ k l ini,
  { rw [inter_eq_left_iff_subset],
    exact filter_subset _ _ },
  specialize hl k hlk n χ hχ ini hini _ le_rfl,
  refine hl.trans' _,
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  rw [this, ←red_steps_union_density_steps, card_disjoint_union red_steps_disjoint_density_steps],
  have : (1 - 3 * ε / ini.p : ℝ) * ini.p = ini.p - 3 * ε,
  { rw [one_sub_mul, div_mul_cancel],
    exact (hp₀.trans_le hini).ne' },
  rw [←this, ←mul_assoc, mul_pow _ _ (_ + _)],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg col_density_nonneg _),
  have : (k : ℝ) ^ (- 1 / 8 : ℝ) ≤ 1,
  { refine rpow_le_one_of_one_le_of_nonpos _ (by norm_num),
    rw nat.one_le_cast,
    exact hl₁ k hlk },
  refine pow_le_pow_of_le_one _ _ _,
  { refine mul_nonneg _ _,
    { rwa sub_nonneg },
    { rw sub_nonneg,
      refine div_le_one_of_le (hini.trans' _) col_density_nonneg,
      rw [←le_div_iff', neg_div],
      { exact hl' k hlk },
      norm_num1 } },
  { rw mul_comm,
    refine mul_le_one _ (sub_nonneg_of_le this) _,
    { rw sub_le_self_iff,
      refine div_nonneg _ col_density_nonneg,
      positivity },
    { rw sub_le_self_iff,
      positivity } },
  rw two_mul,
  refine add_le_add (four_four_red μ (hl₀ k hlk).ne' (hl₀ l le_rfl).ne' hχ ini) _,
  refine ((four_four_blue_density μ (hl₀ k hlk).ne' (hl₀ l le_rfl).ne' hχ ini).trans hlk).trans' _,
  exact le_add_self,
end

open asymptotics

lemma six_one (μ p₀ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hp₀ : 0 < p₀) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ ini : book_config χ, p₀ ≤ ini.p →
  (2 : ℝ) ^ f k *
    ini.p ^ ((red_steps μ k l ini).card + (density_steps μ k l ini).card) *
      ini.Y.card ≤ (end_state μ k l ini).Y.card :=
begin
  let g : ℝ → ℝ := (λ k, -2 * k ^ (-1 / 8 : ℝ) - 2 * (3 * k ^ (-1 / 4 : ℝ) / p₀)),
  refine ⟨λ k : ℕ, g k * (2 * k), _, _⟩,
  { suffices : g =o[at_top] (λ x, (1 : ℝ)),
    { have := this.comp_tendsto tendsto_coe_nat_at_top_at_top,
      refine (this.mul_is_O (is_O_const_mul_self (2 : ℝ) _ at_top)).congr_right _,
      simp only [one_mul, eq_self_iff_true, forall_const]},
    refine asymptotics.is_o.sub _ _,
    { refine is_o.const_mul_left _ _,
      simpa using is_o_rpow_rpow (show - 1 / 8 < (0 : ℝ), by norm_num) },
    { simp_rw [div_eq_mul_one_div (_ * _), mul_comm _ (1 / p₀), ←mul_assoc],
      refine is_o.const_mul_left _ _,
      simpa using is_o_rpow_rpow (show - 1 / 4 < (0 : ℝ), by norm_num) } },
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h₈ := tendsto_rpow_neg_at_top (show (0 : ℝ) < 1 / 8, by norm_num),
  have h₄ := tendsto_rpow_neg_at_top (show (0 : ℝ) < 1 / 4, by norm_num),
  filter_upwards [six_one_explicit μ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster ((h₄.comp t).eventually
      (eventually_le_nhds (show 0 < p₀ / (2 * 3), by positivity))),
    top_adjuster ((h₈.comp t).eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2, by norm_num)))]
    with l hl hl₄ hl₈
    k hlk n χ hχ ini hini,
  refine (hl k hlk n χ hχ ini hini).trans' _,
  clear hl,
  rw [mul_assoc, mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg col_density_nonneg _)
    (nat.cast_nonneg _)),
  rw [rpow_mul, ←nat.cast_two, ←nat.cast_mul, nat.cast_two, rpow_nat_cast],
  swap,
  { exact two_pos.le },
  refine pow_le_pow_of_le_left (rpow_nonneg_of_nonneg two_pos.le _) _ _,
  have h₁ : (2 : ℝ) ^ (-2 * (k : ℝ) ^ (- 1 / 8 : ℝ)) ≤ 1 - (k : ℝ) ^ (-1 / 8 : ℝ),
  { refine two_approx (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) _,
    rw [neg_div],
    exact hl₈ k hlk },
  have h₂ : (2 : ℝ) ^ (-2 * (3 * (k : ℝ) ^ (-1 / 4 : ℝ) / p₀)) ≤
    1 - 3 * (k : ℝ) ^ (-1 / 4 : ℝ) / ini.p,
  { refine (two_approx (by positivity) _).trans _,
    { rw [div_le_iff' hp₀, mul_one_div, ←le_div_iff', div_div, neg_div],
      { exact hl₄ k hlk },
      { norm_num1 } },
    rw [sub_le_sub_iff_left],
    exact div_le_div_of_le_left (by positivity) hp₀ hini },
  refine (mul_le_mul h₁ h₂ (rpow_nonneg_of_nonneg two_pos.le _) _).trans_eq' _,
  { exact h₁.trans' (rpow_nonneg_of_nonneg two_pos.le _) },
  rw [←rpow_add two_pos, neg_mul _ (_ / _), ←sub_eq_add_neg],
end

end simple_graph
