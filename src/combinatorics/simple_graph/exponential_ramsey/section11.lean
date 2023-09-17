import combinatorics.simple_graph.exponential_ramsey.section10

namespace simple_graph

open_locale big_operators exponential_ramsey nat real

open filter finset nat real asymptotics

-- lemma eleven_one_start (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
--   ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
--     ∀ᶠ k : ℕ in at_top,
--     ∀ n : ℕ, 2 ≤ n →
--     ∀ χ : top_edge_labelling (fin n) (fin 2),
--     ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
--     ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
--     let s := (density_steps μ k k ini).card,
--         t := (red_steps μ k k ini).card
--     in logb 2 n ≤ k * logb 2 μ⁻¹ + t * logb 2 (1 - μ)⁻¹ + s * logb 2 (μ * (s + t) / s) + f k :=
-- begin
-- end

lemma large_X (n m : ℕ) (hn'' : 2 ≤ n) (hn' : ⌊(n / 2 : ℝ)⌋₊ ≤ m) : (2 : ℝ) ^ (-2 : ℝ) * n ≤ m :=
begin
  refine (nat.cast_le.2 hn').trans' ((ge_floor _).trans_eq' _),
  { rw one_le_div (zero_lt_two' ℝ),
    exact_mod_cast hn'' },
  rw [div_div, div_eq_mul_inv, mul_comm],
  norm_num,
end

lemma is_o_const_thing {c : ℝ} : (λ _ : ℕ, c) =o[at_top] (λ i, (i : ℝ)) :=
(is_o.comp_tendsto (is_o_const_id_at_top c) tendsto_coe_nat_at_top_at_top)

lemma eleven_two_start (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n →
    ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
    let s := (density_steps μ k k ini).card,
        t := (red_steps μ k k ini).card
    in (n : ℝ) ≤ 2 ^ f k * μ⁻¹ ^ k * (1 - μ)⁻¹ ^ t * (μ / beta μ k k ini) ^ s :=
begin
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1,
  obtain ⟨f₁, hf₁', hf₁⟩ := end_ramsey_number_pow_is_o,
  obtain ⟨f₂, hf₂', hf₂⟩ := seven_one μ hμ₁,
  specialize hf₁ μ μ (1 / 2) hμ₀ hμ₁ hp₀,
  specialize hf₂ μ (1 / 2) hμ₀ hp₀,
  refine ⟨λ k, 2 + f₁ k + -f₂ k, _, _⟩,
  { exact (is_o_const_thing.add hf₁').add hf₂'.neg_left },
  clear hf₁' hf₂',
  filter_upwards [hf₁, hf₂, beta_pos μ μ _ hμ₀ hμ₁ hp₀] with k hf₁' hf₂' hβ
    n hn'' χ hχ ini hini hn',
  clear hf₁ hf₂,
  specialize hf₁' k le_rfl μ le_rfl le_rfl n χ hχ ini hini,
  specialize hf₂' k le_rfl μ le_rfl le_rfl n χ hχ ini hini,
  specialize hβ k le_rfl μ le_rfl le_rfl n χ ini hini,
  have hμ₁' : 0 < 1 - μ := sub_pos_of_lt hμ₁,
  replace hf₂' := hf₂'.trans hf₁',
  rw [←le_div_iff', div_eq_mul_inv, mul_inv, ←inv_pow, inv_div, mul_inv, mul_inv,
    ←inv_pow, ←inv_pow, ←rpow_neg two_pos.le, mul_assoc, mul_assoc] at hf₂',
  swap, { positivity },
  replace hf₂' := (large_X _ _ hn'' hn').trans hf₂',
  rw ←le_div_iff' at hf₂',
  swap, { positivity },
  refine hf₂'.trans_eq _,
  rw [div_eq_mul_inv, mul_comm, rpow_neg two_pos.le, inv_inv, ←mul_assoc, ←rpow_add two_pos,
    ←mul_assoc, ←rpow_add two_pos, ←mul_assoc, ←mul_assoc],
end

lemma logb_pow {b x : ℝ} {k : ℕ} : logb b (x ^ k) = k * logb b x :=
by rw [logb, log_pow, mul_div_assoc, logb]

lemma is_o.max {f g h : ℕ → ℝ} (hf : f =o[at_top] h) (hg : g =o[at_top] h) :
  (λ x, max (f x) (g x)) =o[at_top] h :=
begin
  rw is_o_iff,
  intros c hc,
  filter_upwards [hf.bound hc, hg.bound hc] with n hf' hg',
  rw norm_eq_abs,
  refine abs_max_le_max_abs_abs.trans _,
  rw [←norm_eq_abs, ←norm_eq_abs, max_le_iff],
  exact ⟨hf', hg'⟩
end

lemma log_one_add_o (f : ℕ → ℝ) (hf : f =o[at_top] (λ _, (1 : ℝ))) :
  (λ k, log (1 + f k)) =o[at_top] (λ _, (1 : ℝ)) :=
begin
  rw is_o_one_iff at hf ⊢,
  rw ←log_one,
  refine (continuous_at_log one_ne_zero).tendsto.comp _,
  convert (@tendsto_const_nhds _ _ _ 1 _).add hf using 1,
  rw add_zero
end

lemma logb_is_O_log (b : ℝ) (l) : logb b =O[l] log :=
begin
  rw is_O_iff,
  refine ⟨‖(log b)⁻¹‖, _⟩,
  filter_upwards [] with k,
  rw [logb, div_eq_mul_inv, norm_mul, mul_comm],
end

-- logb (1 + o(1)) is o(1)
lemma logb_one_add_o {b : ℝ} (f : ℕ → ℝ) (hf : f =o[at_top] (λ _, (1 : ℝ))) :
  (λ k, logb b (1 + f k)) =o[at_top] (λ _, (1 : ℝ)) :=
begin
  refine (is_O.comp_tendsto (logb_is_O_log _ (nhds 1)) _).trans_is_o (log_one_add_o _ hf),
  rw is_o_one_iff at hf,
  convert (@tendsto_const_nhds _ _ _ 1 _).add hf using 1,
  rw add_zero
end


lemma is_o_logb_rpow_at_top {b r : ℝ} (hr : 0 < r) : logb b =o[at_top] (λ x, x ^ r) :=
((is_o_log_rpow_at_top hr).const_mul_left (log b)⁻¹).congr_left $ λ x, inv_mul_eq_div _ _

lemma eleven_two_aux_error_one (μ : ℝ) (hμ₀ : 0 < μ) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ k : ℕ,
      ∀ s t : ℕ,
        t ≤ k →
        (s : ℝ) ≤ k ^ (31 / 32 : ℝ) →
        (s : ℝ) * logb 2 (μ * (s + t) / s) ≤ f k :=
begin
  refine ⟨λ k, ‖(k ^ (31 / 32 : ℝ) * (logb 2 μ + 1) + k ^ (31 / 32 : ℝ) * logb 2 k : ℝ)‖, _, _⟩,
  { rw is_o_norm_left,
    suffices : (λ k : ℝ, k ^ (31 / 32 : ℝ) * (logb 2 μ + 1) + k ^ (31 / 32 : ℝ) * logb 2 k)
      =o[at_top] id,
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    refine is_o.add _ _,
    { simp_rw [mul_comm],
      refine is_o.const_mul_left _ _,
      refine (is_o_rpow_rpow (by norm_num1 : (31 / 32 : ℝ) < 1)).congr_right _,
      simp },
    have : (λ x : ℝ, x ^ (31 / 32 : ℝ)) =O[at_top] (λ x : ℝ, x ^ (31 / 32 : ℝ)) :=
      is_O_refl _ _,
    refine (is_O.mul_is_o this (is_o_logb_rpow_at_top (show (0 : ℝ) < 1 / 32,
      by norm_num1))).congr' eventually_eq.rfl _,
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk,
    rw [←rpow_add hk],
    norm_num1,
    rw [rpow_one, id.def] },
  intros k s t ht hs,
  rcases s.eq_zero_or_pos with rfl | hs₀,
  { rw [nat.cast_zero, zero_mul],
    exact norm_nonneg _ },
  have hsk : s ≤ k,
  { rw [←@nat.cast_le ℝ],
    refine hs.trans _,
    rcases k.eq_zero_or_pos with rfl | hk,
    { norm_num },
    have : 1 ≤ (k : ℝ),
    { rw [nat.one_le_cast],
      exact hk },
    exact (rpow_le_rpow_of_exponent_le this (by norm_num1)).trans_eq (rpow_one _) },
  have : 0 < k,
  { exact hs₀.trans_le hsk },
  cases le_or_lt (logb 2 (μ * (s + t) / s)) 0,
  { exact (norm_nonneg _).trans' (mul_nonpos_of_nonneg_of_nonpos (nat.cast_nonneg _) h) },
  rw [norm_eq_abs, ←mul_add, abs_mul],
  refine (mul_le_mul_of_nonneg_right (hs.trans (le_abs_self _)) h.le).trans _,
  refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
  refine (le_abs_self _).trans' _,
  rw [add_assoc, mul_div_assoc, logb_mul hμ₀.ne', add_le_add_iff_left,
    logb_le_iff_le_rpow one_lt_two, add_comm (1 : ℝ), rpow_add_one two_ne_zero,
    rpow_logb two_pos one_lt_two.ne'],
  refine (div_le_self (by positivity) _).trans _,
  { rwa nat.one_le_cast },
  rotate,
  { positivity },
  { positivity },
  { positivity },
  rw [mul_two, ←nat.cast_add, ←nat.cast_add, nat.cast_le],
  { exact add_le_add hsk ht },
end

lemma logb_coe_nonneg (b : ℝ) (hb : 1 < b) (k : ℕ) : 0 ≤ logb b k :=
begin
  cases k,
  { rw [nat.cast_zero, logb_zero] },
  refine logb_nonneg hb _,
  simp
end

lemma logb_le_logb_of_le {b x y : ℝ} (hb : 1 ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
  logb b x ≤ logb b y :=
begin
  rcases eq_or_lt_of_le hb with rfl | hb',
  { rw [logb, logb, log_one, div_zero, div_zero] },
  rwa logb_le_logb hb' hx (hx.trans_le hxy),
end

lemma eleven_two_aux_error_one' (μ : ℝ) (hμ₀ : 0 < μ) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ k s t : ℕ,
        t ≤ k →
        (s : ℝ) ≤ k ^ (31 / 32 : ℝ) →
        |(s : ℝ) * logb 2 (μ * (s + t) / s)| ≤ f k :=
begin
  refine ⟨λ k, (k : ℝ) ^ (31 / 32 : ℝ) * ((|logb 2 μ| + 1) + 2 * logb 2 k), _, _⟩,
  { suffices : (λ k : ℝ, k ^ (31 / 32 : ℝ) * ((|logb 2 μ| + 1) + 2 * logb 2 k))
      =o[at_top] id,
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    suffices : (λ (k : ℝ), |logb 2 μ| + 1 + 2 * logb 2 k) =o[at_top] (λ k : ℝ, k ^ (1 / 32 : ℝ)),
    { refine ((is_O_refl (λ k : ℝ, k ^ (31 / 32 : ℝ)) at_top).mul_is_o this).congr'
        eventually_eq.rfl _,
      filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk using by norm_num [←rpow_add hk] },
    refine is_o.add _ _,
    { rw is_o_const_left,
      exact or.inr (tendsto_norm_at_top_at_top.comp (tendsto_rpow_at_top (by norm_num1))) },
    refine is_o.const_mul_left _ _,
    exact is_o_logb_rpow_at_top (by norm_num1) },
  intros k s t htk hsk,
  rcases s.eq_zero_or_pos with rfl | hs,
  { rw [nat.cast_zero, zero_mul, abs_zero],
    have := logb_coe_nonneg 2 one_lt_two k,
    positivity },
  have : s ≤ k,
  { rw [←@nat.cast_le ℝ],
    refine hsk.trans _,
    rcases k.eq_zero_or_pos with rfl | hk,
    { norm_num },
    have : 1 ≤ (k : ℝ),
    { rw [nat.one_le_cast],
      exact hk },
    exact (rpow_le_rpow_of_exponent_le this (by norm_num1)).trans_eq (rpow_one _) },
  rw [abs_mul, nat.abs_cast, logb_div, logb_mul hμ₀.ne', add_sub_assoc, add_assoc],
  rotate,
  { positivity },
  { positivity },
  { positivity },
  refine mul_le_mul hsk ((abs_add _ _).trans (add_le_add_left _ _)) (abs_nonneg _) (by positivity),
  refine (abs_sub _ _).trans _,
  have : 1 + logb 2 k = logb 2 (2 * k),
  { rw [logb_mul, add_left_inj, logb, div_self],
    { exact log_ne_zero_of_pos_of_ne_one two_pos one_lt_two.ne' },
    { norm_num1 },
    { have : 0 < k := hs.trans_le this, positivity } },
  rw [←nat.cast_add, abs_of_nonneg (logb_coe_nonneg _ one_lt_two _), nat.cast_add,
    abs_of_nonneg (logb_coe_nonneg _ one_lt_two _), two_mul, ←add_assoc, this, two_mul],
  refine add_le_add (logb_le_logb_of_le one_lt_two.le _ _) (logb_le_logb_of_le one_lt_two.le _ _),
  any_goals { positivity },
  any_goals { norm_cast },
  { exact add_le_add ‹_› htk },
  { exact ‹s ≤ k›},
end

lemma eleven_two_aux_error_one_other (μ : ℝ) (hμ₀ : 0 < μ) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ k s : ℕ,
      ∀ β : ℝ, 0 < β → (1 : ℝ) / k ^ 2 ≤ β → (s : ℝ) ≤ k ^ (31 / 32 : ℝ) →
        (s : ℝ) * logb 2 (μ / β) ≤ f k :=
begin
  refine ⟨λ k, ‖logb 2 μ * (k : ℝ) ^ (31 / 32 : ℝ) +
    2 * ((k : ℝ) ^ (31 / 32 : ℝ) * logb 2 k)‖, _, _⟩,
  { rw is_o_norm_left,
    suffices : (λ x : ℝ, logb 2 μ * x ^ (31 / 32 : ℝ) + 2 * (x ^ (31 / 32 : ℝ) * logb 2 x))
      =o[at_top] id,
    { exact this.comp_tendsto tendsto_coe_nat_at_top_at_top },
    refine is_o.add (is_o.const_mul_left _ _) (is_o.const_mul_left _ _),
    { simpa only [rpow_one] using is_o_rpow_rpow (show (31 / 32 : ℝ) < 1, by norm_num1) },
    refine (is_O.mul_is_o (is_O_refl (λ k : ℝ, (k : ℝ) ^ (31 / 32 : ℝ)) at_top)
      (is_o_logb_rpow_at_top (show (0 : ℝ) < 1 / 32, by norm_num1))).congr' eventually_eq.rfl _,
      filter_upwards [eventually_gt_at_top (0 : ℝ)] with k hk,
    rw [←rpow_add hk],
    norm_num1,
    rw [rpow_one, id.def] },
  intros k s β hβ' hβ hs,
  cases le_or_lt (s : ℝ) 0 with hs' hs',
  { rw [←nat.cast_zero, nat.cast_le, le_zero_iff] at hs',
    rw [hs', nat.cast_zero, zero_mul],
    exact norm_nonneg _ },
  cases le_or_lt (logb 2 (μ / β)) 0 with hβ'' hβ'',
  { refine (norm_nonneg _).trans' (mul_nonpos_of_nonneg_of_nonpos (nat.cast_nonneg _) hβ'') },
  have : 0 < k,
  { rw [pos_iff_ne_zero],
    rintro rfl,
    refine hs'.not_le (hs.trans _),
    norm_num },
  refine (mul_le_mul_of_nonneg_right hs hβ''.le).trans ((le_norm_self _).trans' _),
  rw [mul_left_comm, mul_comm (logb 2 μ), ←mul_add, ←nat.cast_two, ←logb_pow, nat.cast_two,
    ←logb_mul],
  rotate,
  { positivity },
  { positivity },
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  refine logb_le_logb_of_le one_lt_two.le (div_pos hμ₀ hβ') _,
  refine (div_le_div_of_le_left hμ₀.le (by positivity) hβ).trans _,
  rw [div_div_eq_mul_div, div_one],
end

-- (1 + f k) *
--     ((density_steps μ k l ini).card / ((density_steps μ k l ini).card + (red_steps μ k l ini).card))
--     ≤ beta μ k l ini

lemma eleven_two_aux_error_two (μ : ℝ) (hμ₀ : 0 < μ) (f : ℕ → ℝ) (hf : f =o[at_top] (λ i, (1 : ℝ))) :
  ∃ g : ℕ → ℝ, g =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ᶠ k in at_top, ∀ s t : ℕ, ∀ β : ℝ,
      0 < β →
      s ≤ k →
      t ≤ k →
      (1 + f k) * (s / (s + t)) ≤ β →
      (s : ℝ) * logb 2 (μ / β) ≤ (s : ℝ) * logb 2 (μ * (s + t) / s) + g k :=
begin
  have := (is_o_one_iff _).1 hf,
  have := this.eventually (eventually_gt_nhds (show (-1 : ℝ) < 0, by norm_num1)),
  refine ⟨λ k, ‖(k * - logb 2 (1 + f k) : ℝ)‖, _, _⟩,
  { rw is_o_norm_left,
    refine ((is_O_refl (λ x : ℕ, (x : ℝ)) at_top).mul_is_o
      (logb_one_add_o _ hf).neg_left).trans_is_O _,
    simp only [mul_one],
    exact is_O_refl _ _ },
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually this] with k hk s t β hβ hsk htk hβ',
  have : 0 < 1 + f k,
  { refine (add_lt_add_left hk 1).trans_eq' (by norm_num1) },
  rcases s.eq_zero_or_pos with rfl | hs,
  { rw [nat.cast_zero, zero_mul, zero_mul, zero_add],
    exact norm_nonneg _ },
  rw [←sub_le_iff_le_add', norm_eq_abs, ←mul_sub, abs_mul, nat.abs_cast],
  refine (mul_le_mul_of_nonneg_right (nat.cast_le.2 hsk) _).trans' _,
  { exact abs_nonneg _ },
  refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans' _) (nat.cast_nonneg _),
  rw [le_neg_iff_add_nonpos_left, ←logb_div, ←logb_mul this.ne'],
  rotate,
  { positivity },
  { positivity },
  { positivity },
  refine logb_nonpos one_lt_two (by positivity) _,
  rw [div_div, mul_comm β, ←div_div, mul_div_assoc', div_le_one hβ, div_div_eq_mul_div,
    mul_div_mul_left _ _ hμ₀.ne'],
  exact hβ'
end

lemma eleven_two (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n →
    ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
    let s := (density_steps μ k k ini).card,
        t := (red_steps μ k k ini).card
    in logb 2 n ≤ k * logb 2 μ⁻¹ + t * logb 2 (1 - μ)⁻¹ + s * logb 2 (μ * (s + t) / s) + f k :=
begin
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1,
  obtain ⟨f₁, hf₁', hf₁⟩ := eleven_two_start μ hμ₀ hμ₁,
  obtain ⟨f₂, hf₂', hf₂⟩ := eight_six μ hμ₁,
  obtain ⟨f₃, hf₃', hf₃⟩ := eleven_two_aux_error_one' μ hμ₀,
  obtain ⟨f₄, hf₄', hf₄⟩ := eleven_two_aux_error_one_other μ hμ₀,
  obtain ⟨f₅, hf₅', hf₅⟩ := eleven_two_aux_error_two μ hμ₀ f₂ hf₂',
  specialize hf₂ μ (1 / 2) hμ₀ hp₀,
  refine ⟨λ k, f₁ k + max (f₄ k - -f₃ k) (f₅ k), _, _⟩,
  { exact hf₁'.add (is_o.max (hf₄'.sub hf₃'.neg_left) hf₅') },
  clear hf₁' hf₂' hf₅',
  filter_upwards [hf₁, hf₂, beta_pos μ μ _ hμ₀ hμ₁ hp₀, one_div_sq_le_beta μ μ _ hμ₀ hμ₁ hp₀,
    hf₅, eventually_gt_at_top 0] with
    k hf₁' hf₂' hβ hβ' hf₅' hk₀
    n hn'' χ hχ ini hini hn',
  clear hf₁ hf₂ hf₅,
  have hsk : (density_steps μ k k ini).card ≤ k,
  { exact (four_four_blue_density μ hk₀.ne' hk₀.ne' hχ ini).trans' le_add_self },
  have htk : (red_steps μ k k ini).card ≤ k := four_four_red μ hk₀.ne' hk₀.ne' hχ ini,
  specialize hf₁' n hn'' χ hχ ini hini hn',
  specialize hf₂' k le_rfl μ le_rfl le_rfl n χ hχ ini hini,
  specialize hβ k le_rfl μ le_rfl le_rfl n χ ini hini,
  specialize hβ' k le_rfl μ le_rfl le_rfl n χ ini hini,
  specialize hf₃ k (density_steps μ k k ini).card (red_steps μ k k ini).card htk,
  specialize hf₄ k (density_steps μ k k ini).card (beta μ k k ini) hβ hβ',
  specialize hf₅' (density_steps μ k k ini).card (red_steps μ k k ini).card _ hβ hsk htk,
  have : (0 : ℝ) < n := by positivity,
  have hμ₁' : 0 < 1 - μ := sub_pos_of_lt hμ₁,
  refine ((logb_le_logb one_lt_two this (this.trans_le hf₁')).2 hf₁').trans _,
  rw [logb_mul, logb_mul, logb_mul, logb_rpow two_pos, logb_pow, logb_pow, logb_pow, add_right_comm,
    add_right_comm _ (_ * logb _ (1 - μ)⁻¹), add_right_comm _ (_ * logb _ (1 - μ)⁻¹),
    add_le_add_iff_right, add_assoc, add_left_comm, add_assoc, add_le_add_iff_left, add_left_comm,
    add_le_add_iff_left, ←sub_le_iff_le_add'],
  rotate,
  { norm_num1 },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  { positivity },
  cases le_total ((density_steps μ k k ini).card : ℝ) (k ^ (31 / 32 : ℝ)) with hk hk,
  { refine (le_max_left _ _).trans' _,
    refine sub_le_sub (hf₄ hk) _,
    exact (abs_le.1 (hf₃ hk)).1 },
  { refine (le_max_right _ _).trans' _,
    rw sub_le_iff_le_add',
    exact hf₅' (hf₂' hk) },
end

lemma Y_small {μ k n} (hk : k ≠ 0) {χ : top_edge_labelling (fin n) (fin 2)} {ini : book_config χ}
  (hχ : ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card))
  {i : ℕ} (hi : i ≤ final_step μ k k ini) :
  (algorithm μ k k ini i).Y.card ≤
    ramsey_number ![k, k - (red_steps μ k k ini ∩ finset.range i).card] :=
begin
  rw ramsey_number_pair_swap,
  by_contra' h',
  obtain ⟨m, hm⟩ := ramsey_number_le_finset h'.le χ,
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
    tsub_le_iff_right] at hm,
  rcases hm,
  swap,
  { exact hχ ⟨m, 1, hm.2⟩ },
  refine hχ ⟨m ∪ (algorithm μ k k ini i).A, 0, _, hm.2.2.trans _⟩,
  { rw [finset.coe_union, top_edge_labelling.monochromatic_of_union],
    refine ⟨hm.2.1, (algorithm μ k k ini i).red_A, _⟩,
    refine (algorithm μ k k ini i).red_XYA.subset_left _,
    exact hm.1.trans (finset.subset_union_right _ _) },
  rw [finset.card_union_eq],
  { exact add_le_add_left (four_four_red_aux hk hk _ _ hi) _ },
  exact (algorithm μ k k ini i).hYA.mono_left hm.1,
end

lemma eleven_three (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n →
    ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card →
    ∀ i : ℕ, i ≤ final_step μ k k ini →
    let s := (density_steps μ k k ini).card,
        t := (red_steps μ k k ini ∩ finset.range i).card
    in logb 2 n ≤ logb 2 (ramsey_number ![k, k - t]) + s + t + f k :=
begin
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1,
  obtain ⟨f, hf, hf'⟩ := six_one_general _ hp₀,
  specialize hf' _ _ hμ₀ hμ₁,
  refine ⟨λ k, -(f k + -2), _, _⟩,
  { refine is_o.neg_left (is_o.add hf _),
    exact is_o_const_thing },
  filter_upwards [hf', eventually_gt_at_top 0] with k hf hk₀
    n hn χ hχ ini hini hn' i hi,
  clear hf',
  specialize hf k le_rfl μ le_rfl le_rfl n χ hχ ini hini i hi,
  replace hf := hf.trans (nat.cast_le.2 (Y_small hk₀.ne' hχ hi)),
  rw mul_right_comm at hf,
  have : 2 ^ (- ((red_steps μ k k ini ∩ finset.range i).card +
                 (density_steps μ k k ini ∩ finset.range i).card : ℝ)) ≤
    ini.p ^ ((red_steps μ k k ini ∩ finset.range i).card +
             (density_steps μ k k ini ∩ finset.range i).card),
  { rw [rpow_neg two_pos.le, ←inv_rpow two_pos.le, ←nat.cast_add, rpow_nat_cast],
    refine pow_le_pow_of_le_left (by norm_num1) _ _,
    rwa [←one_div] },
  replace hf := hf.trans' (mul_le_mul_of_nonneg_left this (by positivity)),
  rw [mul_right_comm, ←rpow_add two_pos] at hf,
  replace hf := hf.trans' (mul_le_mul_of_nonneg_left (large_X _ _ hn hn') (by positivity)),
  rw [←mul_assoc, ←rpow_add two_pos] at hf,
  replace hf := logb_le_logb_of_le one_le_two (by positivity) hf,
  rw [logb_mul, logb_rpow two_pos one_lt_two.ne', ←le_sub_iff_add_le'] at hf,
  rotate,
  { positivity },
  { positivity },
  refine hf.trans _,
  rw [add_assoc, add_left_comm, ←sub_sub, sub_neg_eq_add, ←sub_eq_add_neg _ (f k + -2), ←add_assoc,
    add_right_comm, add_sub_assoc, add_sub_assoc],
  refine add_le_add_right (add_le_add_left _ _) _,
  refine nat.cast_le.2 (finset.card_le_of_subset _),
  exact finset.inter_subset_left _ _
end

lemma eleven_three_special (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n →
    ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card →
    let s := (density_steps μ k k ini).card,
        t := (red_steps μ k k ini).card
    in logb 2 n ≤ logb 2 (ramsey_number ![k, k - t]) + s + t + f k :=
begin
  obtain ⟨f, hf, hf'⟩ := eleven_three μ hμ₀ hμ₁,
  refine ⟨f, hf, _⟩,
  filter_upwards [hf'] with k hf n hn χ hχ ini hini hn',
  specialize hf n hn χ hχ ini hini hn' _ le_rfl,
  have : red_steps μ k k ini ∩ finset.range (final_step μ k k ini) = red_steps μ k k ini,
  { rw [finset.inter_eq_left_iff_subset],
    exact red_steps_subset_red_or_density_steps.trans (finset.filter_subset _ _) },
  rwa this at hf,
end

lemma ramsey_number_diag_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ ramsey_number ![k, k] :=
begin
  refine (ramsey_number.mono_two hk le_rfl).trans' _,
  simp only [ramsey_number_cons_two, ramsey_number_singleton]
end

lemma two_le_n_of_large_k {k : ℕ} (hk : 4 ≤ k) :
  2 ≤ ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊ :=
begin
  refine nat.cast_le.1 ((nat.le_ceil _).trans' _),
  rw [nat.cast_two, le_div_iff (zero_lt_two' ℝ)],
  have : k ≤ ramsey_number ![k, k] := ramsey_number_diag_ge (hk.trans' (show 2 ≤ 4, by norm_num)),
  refine (nat.cast_le.2 (hk.trans this)).trans' _,
  norm_num1
end

lemma comp_right_label_graph_apply {V K K' : Type*} {k : K} {χ : top_edge_labelling V K}
  (f : K → K') (hf : function.injective f) :
  (χ.comp_right f).label_graph (f k) = χ.label_graph k :=
begin
  ext x y,
  simp only [top_edge_labelling.label_graph_adj, top_edge_labelling.comp_right_get, hf.eq_iff],
end

lemma comp_right_density_apply {V K K' : Type*} [fintype V] [decidable_eq V] [decidable_eq K]
  [decidable_eq K'] (k : K) {χ : top_edge_labelling V K} (f : K → K') (hf : function.injective f) :
  (χ.comp_right f).density (f k) = χ.density k :=
begin
  rw [top_edge_labelling.density],
  simp only [comp_right_label_graph_apply _ hf],
  refl
end

lemma density_sum {V : Type*} [fintype V] [decidable_eq V] (hV : 2 ≤ fintype.card V)
  (χ : top_edge_labelling V (fin 2)) :
  χ.density 0 + (χ.comp_right (equiv.swap 0 1)).density 0 = 1 :=
begin
  have : (χ.comp_right (equiv.swap 0 1)).density 0 = χ.density 1,
  { have : equiv.swap (0 : fin 2) 1 1 = 0,
    { simp only [equiv.swap_apply_right, eq_self_iff_true] },
    rw [←comp_right_density_apply 1 (equiv.swap (0 : fin 2) 1), this],
    exact equiv.injective _ },
  rwa [this, density_zero_one, sub_add_cancel],
end

lemma density_nonneg {V : Type*} [fintype V] [decidable_eq V] (G : simple_graph V)
  [decidable_rel G.adj] : 0 ≤ G.density :=
by { rw [simple_graph.density], positivity }

-- lemma top_edge_labelling.density_nonneg {V : Type*} [fintype V] [decidable_eq V] (χ : simple_graph V)
--   [decidable_rel G.adj] : 0 ≤ G.density :=
-- by { rw [simple_graph.density], positivity }

lemma some_large_density {V : Type*} [fintype V] [decidable_eq V] (hV : 2 ≤ fintype.card V)
  (χ : top_edge_labelling V (fin 2)) :
  1 / 2 ≤ χ.density 0 ∨ 1 / 2 ≤ (χ.comp_right (equiv.swap 0 1)).density 0 :=
begin
  have := density_sum hV χ,
  have : 0 ≤ χ.density 0 := rat.cast_nonneg.2 (density_nonneg _),
  have : 0 ≤ (χ.comp_right (equiv.swap 0 1)).density 0 := rat.cast_nonneg.2 (density_nonneg _),
  by_contra',
  linarith
end

lemma eleven_one_one {m : ℕ} (hm : 2 ≤ m) : ⌈(m : ℝ) / 2⌉₊ < m :=
begin
  refine nat.cast_lt.1 ((ceil_lt_two_mul _).trans_le _),
  { refine div_lt_div_of_lt two_pos _,
    rw [nat.one_lt_cast],
    exact hm },
  rw [mul_div_cancel'],
  norm_num1
end

-- lemma F_bounded_above {x y : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1) (hy : y ≤ 1) :
--   F x y ≤ 4 :=
-- begin
--   rw [F],
--   suffices : limsup (λ k : ℕ, logb 2 (ramsey_number ![k, ⌊(k : ℝ) - x * k⌋₊]) / k) at_top ≤ 2,
--   { linarith only [hx, hy, this] },
--   refine limsup_le_of_le _ _,
--   { refine is_cobounded.mk 0 _,
--     simp only [filter.mem_map, mem_at_top_sets, set.mem_preimage, exists_prop, forall_exists_index],
--     intros s k hs,
--     exact ⟨_, hs k le_rfl, div_nonneg (logb_coe_nonneg _ one_lt_two _) (nat.cast_nonneg _)⟩ },
--   filter_upwards [eventually_gt_at_top 0] with n hn,
--   cases nat.eq_zero_or_pos (ramsey_number ![n, ⌊(n - x * n : ℝ)⌋₊]) with h h,
--   { rw [h],
--     simp },
--   rw [div_le_iff, logb_le_iff_le_rpow one_lt_two],
--   rotate,
--   { positivity },
--   { positivity },
--   rw [←nat.cast_two, ←nat.cast_mul, rpow_nat_cast, ←nat.cast_pow, nat.cast_le],
--   refine ramsey_number_pair_le_two_pow'.trans _,
--   refine nat.pow_le_pow_of_le_right zero_lt_two _,
--   rw [two_mul, add_le_add_iff_left, ←@nat.cast_le ℝ],
--   refine (nat.floor_le _).trans _,
--   { rw [sub_nonneg],
--     exact mul_le_of_le_one_left (nat.cast_nonneg _) hx },
--   simp,
--   positivity
-- end

-- lemma min_F_G_bounded_above {μ x y : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1) (hy : y ≤ 1) :
--   min (F x y) (G μ x y) ≤ 4 :=
-- (min_le_left _ _).trans (F_bounded_above hx₀ hx hy)

-- lemma eleven_one_aux {μ η : ℝ} {k n : ℕ} {χ : top_edge_labelling (fin n) (fin 2)}
--   {ini : book_config χ}
--   (hx : ((red_steps μ k k ini).card : ℝ) / k ∈ set.Icc (0 : ℝ) 1)
--   (hy : ((density_steps μ k k ini).card : ℝ) / k ∈ set.Icc (0 : ℝ) 1)
--   (hy' : ((density_steps μ k k ini).card : ℝ) / k ≤
--     μ / (1 - μ) * (((red_steps μ k k ini).card) / k) + η) :
--   min
--     (F ((red_steps μ k k ini).card / k) ((density_steps μ k k ini).card / k))
--     (G μ ((red_steps μ k k ini).card / k) ((density_steps μ k k ini).card / k)) ≤
--   ⨆ (x ∈ set.Icc (0 : ℝ) 1) (y ∈ set.Icc (0 : ℝ) 1) (hy : y ≤ μ / (1 - μ) * x + η),
--     min (F x y) (G μ x y) :=
-- begin
--   refine le_csupr_of_le _ ((red_steps μ k k ini).card / k) _,
--   { refine ⟨4, _⟩,
--     rintro _ ⟨x, rfl⟩,
--     refine real.supr_le _ (by positivity),
--     rintro ⟨hx₀, hx₁⟩,
--     refine real.supr_le _ (by positivity),
--     intro y,
--     refine real.supr_le _ (by positivity),
--     rintro ⟨hi₁, hi₂⟩,
--     refine real.supr_le _ (by positivity),
--     intro hi',
--     exact min_F_G_bounded_above hx₀ hx₁ hi₂ },
--   refine le_csupr_of_le _ hx _,
--   { refine ⟨4, _⟩,
--     rintro _ ⟨hx, rfl⟩,
--     refine real.supr_le _ (by positivity),
--     intro y,
--     refine real.supr_le _ (by positivity),
--     rintro ⟨hy₁, hy₂⟩,
--     refine real.supr_le _ (by positivity),
--     rintro hy,
--     exact min_F_G_bounded_above hx.1 hx.2 hy₂ },
--   refine le_csupr_of_le _ ((density_steps μ k k ini).card / k) _,
--   { refine ⟨4, _⟩,
--     rintro _ ⟨y, rfl⟩,
--     refine real.supr_le _ (by positivity),
--     rintro ⟨hy₁, hy₂⟩,
--     refine real.supr_le _ (by positivity),
--     intro hy,
--     exact min_F_G_bounded_above hx.1 hx.2 hy₂ },
--   refine le_csupr_of_le _ hy _,
--   { refine ⟨4, _⟩,
--     rintro _ ⟨_, rfl⟩,
--     refine real.supr_le _ (by positivity),
--     intro hy',
--     exact min_F_G_bounded_above hx.1 hx.2 hy.2 },
--   refine le_csupr_of_le _ hy' _,
--   { refine ⟨4, _⟩,
--     rintro _ ⟨_, rfl⟩,
--     dsimp,
--     exact min_F_G_bounded_above hx.1 hx.2 hy.2, },
--   refl
-- end


noncomputable def G (μ x y : ℝ) : ℝ :=
  logb 2 μ⁻¹ + x * logb 2 (1 - μ)⁻¹ + y * logb 2 (μ * ((x + y) / y))

lemma eleven_two_improve (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
    ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n →
    ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.X.card →
    let s := (density_steps μ k k ini).card,
        t := (red_steps μ k k ini).card
    in logb 2 n ≤ k * G μ (t / k) (s / k) + f k :=
begin
  obtain ⟨f, hf, hf'⟩ := eleven_two μ hμ₀ hμ₁,
  refine ⟨f, hf, _⟩,
  filter_upwards [hf', eventually_gt_at_top 0] with k hf hk₀ n hn χ hχ ini hini hnX,
  clear hf',
  specialize hf n hn χ hχ ini hini hnX,
  refine hf.trans _,
  clear hf,
  rw [G, add_le_add_iff_right, mul_div_assoc, mul_add, mul_add, ←mul_assoc,
    mul_div_cancel', add_le_add_iff_left, ←mul_assoc, mul_div_cancel', ←add_div,
    div_div_div_cancel_right, add_comm],
  { positivity },
  { positivity },
  { positivity },
end

lemma Inf_mem_of_upclosed {s : set ℝ} {ε : ℝ} (hf' : s.nonempty)
  (hf'' : ∀ x ∈ s, ∀ y, x ≤ y → y ∈ s) (hε : 0 < ε) :
  Inf s + ε ∈ s :=
begin
  by_contra' hε',
  have : ∀ x ∈ s, Inf s + ε < x,
  { intros x hx,
    by_contra',
    exact hε' (hf'' _ hx _ this) },
  have : Inf s + ε ≤ Inf s,
  { exact le_cInf hf' (λ x hx, (this _ hx).le) },
  simp only [add_le_iff_nonpos_right] at this,
  exact hε.not_le this,
end

lemma le_limsup_add (f : ℕ → ℝ) (hf : bdd_above (set.range f)) (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ x in at_top, f x ≤ limsup f at_top + ε :=
begin
  suffices : limsup f at_top + ε ∈ {a : ℝ | ∀ᶠ (n : ℕ) in at_top, f n ≤ a},
  { exact this },
  simp only [limsup_eq],
  refine Inf_mem_of_upclosed _ _ hε,
  { obtain ⟨y, hy⟩ := hf,
    refine ⟨y, eventually_of_forall _⟩,
    intros z,
    exact hy ⟨z, rfl⟩ },
  intros x hx y hxy,
  filter_upwards [hx] with z hz using hz.trans hxy,
end

lemma exists_nice_χ {k n : ℕ} (hn2 : 2 ≤ n) (hnr : n < ramsey_number ![k, k]) :
  ∃ (χ : top_edge_labelling (fin n) (fin 2)), 1 / 2 ≤ χ.density 0 ∧
    ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card :=
begin
  rw [←not_le, ramsey_number_le_iff_fin, is_ramsey_valid, not_forall] at hnr,
  obtain ⟨χ : top_edge_labelling (fin n) (fin 2), hχ⟩ := hnr,
  wlog hχ' : 1 / 2 ≤ χ.density 0 generalizing χ,
  { have hd : 1 / 2 ≤ χ.density 0 ∨ 1 / 2 ≤ (χ.comp_right (equiv.swap 0 1)).density 0 :=
      some_large_density (hn2.trans_eq (fintype.card_fin _).symm) _,
    refine this (χ.comp_right (equiv.swap 0 1)) _ (hd.resolve_left hχ'),
    simp only [fin.exists_fin_two, top_edge_labelling.monochromatic_of, finset.mem_coe,
      top_edge_labelling.comp_right_get, equiv.apply_eq_iff_eq_symm_apply, ne.def, equiv.symm_swap,
      equiv.swap_apply_left, matrix.cons_val_zero, equiv.swap_apply_right, matrix.cons_val_one,
      matrix.head_cons, not_exists, not_or_distrib] at hχ ⊢,
    intros x,
    exact (hχ x).symm },
  exact ⟨χ, hχ', hχ⟩,
end

lemma exists_nicer_χ (k : ℕ) :
  ∃ (χ : top_edge_labelling (fin ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊) (fin 2)),
    4 ≤ k → 1 / 2 ≤ χ.density 0 ∧
      ¬∃ (m : finset (fin ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊)) (c : fin 2),
        χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card :=
begin
  cases lt_or_le k 4 with hk hk,
  { exact ⟨top_edge_labelling.mk (λ _ _ _, 0) (by simp), λ h, false.elim (hk.not_le h)⟩ },
  let n := ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊,
  have hn2 : 2 ≤ n := two_le_n_of_large_k hk,
  have hnr : n < ramsey_number ![k, k],
  { refine eleven_one_one _,
    have : 2 ≤ k := hk.trans' (by norm_num1),
    exact (ramsey_number_diag_ge this).trans_lt' this },
  obtain ⟨χ, hχ, hχ'⟩ := exists_nice_χ hn2 hnr,
  exact ⟨χ, λ _, ⟨hχ, hχ'⟩⟩
end

noncomputable def get_χ (k : ℕ) :
  top_edge_labelling (fin ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊) (fin 2) :=
(exists_nicer_χ k).some

lemma get_χ_density {k : ℕ} (hk : 4 ≤ k) : 1 / 2 ≤ (get_χ k).density 0 :=
((exists_nicer_χ k).some_spec hk).1

lemma get_χ_ramsey {k : ℕ} (hk : 4 ≤ k) :
  ¬∃ (m : finset (fin ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊)) (c : fin 2),
        (get_χ k).monochromatic_of m c ∧ ![k, k] c ≤ m.card  :=
((exists_nicer_χ k).some_spec hk).2

lemma exists_nicer_ini (k : ℕ) :
  ∃ (ini : book_config (get_χ k)), 4 ≤ k →
    (get_χ k).density 0 ≤ ini.p ∧
    ⌊(⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ ini.X.card ∧
    ⌊(⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ ini.Y.card :=
begin
  cases lt_or_le k 4 with hk hk,
  { refine ⟨_, λ h, false.elim (hk.not_le h)⟩,
    refine ⟨∅, ∅, ∅, ∅, _, _, _, _, _, _, _, _, _, _⟩,
    all_goals { simp } },
  set n := ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊,
  have hn2 : 2 ≤ n := two_le_n_of_large_k hk,
  obtain ⟨ini, hini, hiniX, hiniY⟩ := exists_equibipartition_col_density (get_χ k) hn2,
  exact ⟨ini, λ _, ⟨hini, hiniX, hiniY⟩⟩,
end

noncomputable def get_ini (k : ℕ) : book_config (get_χ k) := (exists_nicer_ini k).some
lemma get_ini_p {k : ℕ} (hk : 4 ≤ k) : (get_χ k).density 0 ≤ (get_ini k).p :=
((exists_nicer_ini k).some_spec hk).1
lemma get_ini_card_X {k : ℕ} (hk : 4 ≤ k) :
  ⌊(⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ (get_ini k).X.card :=
((exists_nicer_ini k).some_spec hk).2.1
lemma get_ini_card_Y {k : ℕ} (hk : 4 ≤ k) :
  ⌊(⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊ / 2 : ℝ)⌋₊ ≤ (get_ini k).Y.card :=
((exists_nicer_ini k).some_spec hk).2.2

lemma get_ini_p' {k : ℕ} (hk : 4 ≤ k) : 1 / 2 ≤ (get_ini k).p :=
(get_χ_density hk).trans ((exists_nicer_ini k).some_spec hk).1

lemma R_k_close_to_n (k : ℕ) (hk₆ : 4 ≤ k) :
  logb 2 (ramsey_number ![k, k]) - 1 ≤ logb 2 ⌈(ramsey_number ![k, k] : ℝ) / 2⌉₊ :=
begin
  have hn2 := two_le_n_of_large_k hk₆,
  rw [le_logb_iff_rpow_le one_lt_two, rpow_sub two_pos, rpow_logb two_pos one_lt_two.ne',
      rpow_one],
  { exact nat.le_ceil _ },
  { rw nat.cast_pos,
    refine (ramsey_number_diag_ge (hk₆.trans' (by norm_num1))).trans_lt' _,
    positivity },
  rw [nat.cast_pos],
  positivity
end

noncomputable def bin_ent (b p : ℝ) : ℝ := - p * logb b p - (1 - p) * logb b (1 - p)
@[simp] lemma bin_ent_zero {b : ℝ} : bin_ent b 0 = 0 := by simp [bin_ent]
lemma bin_ent_symm {b p : ℝ} : bin_ent b (1 - p) = bin_ent b p :=
  by { rw [bin_ent, sub_sub_cancel, bin_ent], ring }
@[simp] lemma bin_ent_one {b : ℝ} : bin_ent b 1 = 0 := by simp [bin_ent]

lemma bin_ent_nonneg {b p : ℝ} (hb : 1 < b) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ bin_ent b p :=
begin
  have : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ -(x * logb b x),
  { intros x hx₀ hx₁,
    rw [right.nonneg_neg_iff],
    exact mul_nonpos_of_nonneg_of_nonpos hx₀ (logb_nonpos hb hx₀ hx₁) },
  rw [bin_ent, sub_eq_add_neg, neg_mul],
  exact add_nonneg (this _ hp₀ hp₁) (this _ (sub_nonneg_of_le hp₁) (sub_le_self _ hp₀)),
end

lemma bin_ent_eq {b p : ℝ} : bin_ent b p = (- (p * log p) + -((1 - p) * log (1 - p))) / log b :=
by rw [bin_ent, logb, logb, neg_mul, sub_eq_add_neg, add_div, mul_div_assoc', mul_div_assoc',
  neg_div, neg_div]

-- exists_deriv_eq_slope

theorem convex.strict_mono_on_of_has_deriv_at_pos {D : set ℝ} (hD : convex ℝ D) {f f' : ℝ → ℝ}
  (hf : ∀ x ∈ D, has_deriv_at f (f' x) x) (hf' : ∀ x ∈ interior D, 0 < f' x) :
  strict_mono_on f D :=
begin
  refine convex.strict_mono_on_of_deriv_pos hD _ _,
  { exact has_deriv_at.continuous_on hf },
  intros x hx,
  rw has_deriv_at.deriv (hf x (interior_subset hx)),
  exact hf' x hx
end

theorem convex.strict_anti_on_of_has_deriv_at_neg {D : set ℝ} (hD : convex ℝ D) {f f' : ℝ → ℝ}
  (hf : ∀ x ∈ D, has_deriv_at f (f' x) x) (hf' : ∀ x ∈ interior D, f' x < 0) :
  strict_anti_on f D :=
begin
  refine convex.strict_anti_on_of_deriv_neg hD _ _,
  { exact has_deriv_at.continuous_on hf },
  intros x hx,
  rw has_deriv_at.deriv (hf x (interior_subset hx)),
  exact hf' x hx
end

lemma bin_ent_deriv_aux (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
  has_deriv_at (λ y, - (y * log y) + -((1 - y) * log (1 - y))) (log (1 - x) - log x) x :=
begin
  have h : ∀ x : ℝ, x ≠ 0 → has_deriv_at (λ y, - (y * log y)) (- (log x + 1)) x,
  { rintro x hx₀,
    refine has_deriv_at.neg _,
    have : 1 * log x + x * x⁻¹ = log x + 1,
    { rw [one_mul, mul_inv_cancel hx₀] },
    rw ←this,
    exact has_deriv_at.mul (has_deriv_at_id' x) (has_deriv_at_log hx₀) },
  suffices : has_deriv_at (λ y, - (y * log y) + -((1 - y) * log (1 - y)))
    (- (log x + 1) + (- (log (1 - x) + 1) * -1)) x,
  { convert this using 1,
    ring_nf },
  have : has_deriv_at (λ y : ℝ, 1 - y) (-1 : ℝ) x :=
    (has_deriv_at_id' x).const_sub 1,
  refine has_deriv_at.add (h _ hx₀) _,
  exact (h (1 - x) (sub_ne_zero_of_ne hx₁.symm)).comp x ((has_deriv_at_id' x).const_sub 1),
end

lemma bin_ent_deriv (b x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
  has_deriv_at (bin_ent b) (logb b (1 - x) - logb b x) x :=
begin
  convert has_deriv_at.div_const (bin_ent_deriv_aux x hx₀ hx₁) (log b) using 1,
  { ext y,
    rw bin_ent_eq },
  rw [logb, logb, sub_div],
end

lemma strict_mono_on_bin_ent_zero_half_aux {b : ℝ} (hb : 1 < b) :
  strict_mono_on (bin_ent b) (set.Ioc 0 (1 / 2)) :=
begin
  suffices : strict_mono_on (λ p, - (p * log p) + -((1 - p) * log (1 - p))) (set.Ioc 0 (1 / 2)),
  { intros x hx x' hx' h,
    rw [bin_ent_eq, bin_ent_eq],
    exact div_lt_div_of_lt (log_pos hb) (this hx hx' h) },
  clear hb b,
  refine convex.strict_mono_on_of_has_deriv_at_pos (convex_Ioc _ _)
    (λ x hx, bin_ent_deriv_aux x hx.1.ne' (by linarith only [hx.2])) _,
  rw [interior_Ioc],
  rintro x ⟨hx₁, hx₂⟩,
  rw [sub_pos],
  refine log_lt_log _ _;
  linarith only [hx₁, hx₂]
end

lemma strict_mono_on_bin_ent_zero_half {b : ℝ} (hb : 1 < b) :
  strict_mono_on (bin_ent b) (set.Icc 0 (1 / 2)) :=
begin
  rintro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ h,
  rcases lt_or_eq_of_le hx₁ with hx₁ | rfl,
  { exact strict_mono_on_bin_ent_zero_half_aux hb ⟨hx₁, hx₂⟩ ⟨hx₁.trans h, hy₂⟩ h },
  rw [bin_ent_zero],
  refine (strict_mono_on_bin_ent_zero_half_aux hb ⟨half_pos h, by linarith⟩ ⟨h, hy₂⟩
    (half_lt_self h)).trans_le' _,
  exact bin_ent_nonneg hb (by linarith) (by linarith),
end

lemma strict_anti_on_bin_ent_half_one {b : ℝ} (hb : 1 < b) :
  strict_anti_on (bin_ent b) (set.Icc (1 / 2) 1) :=
begin
  rintro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ h,
  have := strict_mono_on_bin_ent_zero_half hb ⟨sub_nonneg_of_le hy₂, by linarith⟩
    ⟨sub_nonneg_of_le hx₂, by linarith⟩ (sub_lt_sub_left h _),
  rw [bin_ent_symm, bin_ent_symm] at this,
  exact this,
end

lemma strict_mono_on_Icc_iff {f : ℝ → ℝ} {a b : ℝ} :
  strict_mono_on f (set.Icc a b) ↔ ∀ x y, a ≤ x → x < y → y ≤ b → f x < f y :=
begin
  split,
  { intros h x y hax hxy hyb,
    exact h ⟨hax, hxy.le.trans hyb⟩ ⟨hax.trans hxy.le, hyb⟩ hxy },
  rintro h x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ hxy,
  exact h _ _ hx₁ hxy hy₂
end

lemma strict_anti_on_Icc_iff {f : ℝ → ℝ} {a b : ℝ} :
  strict_anti_on f (set.Icc a b) ↔ ∀ x y, a ≤ x → x < y → y ≤ b → f y < f x :=
begin
  split,
  { intros h x y hax hxy hyb,
    exact h ⟨hax, hxy.le.trans hyb⟩ ⟨hax.trans hxy.le, hyb⟩ hxy },
  rintro h x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ hxy,
  exact h _ _ hx₁ hxy hy₂
end

lemma antitone_on_Icc_iff {f : ℝ → ℝ} {a b : ℝ} :
  antitone_on f (set.Icc a b) ↔ ∀ x y, a ≤ x → x ≤ y → y ≤ b → f y ≤ f x :=
begin
  split,
  { intros h x y hax hxy hyb,
    exact h ⟨hax, hxy.trans hyb⟩ ⟨hax.trans hxy, hyb⟩ hxy },
  rintro h x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ hxy,
  exact h _ _ hx₁ hxy hy₂
end

noncomputable def f1 (x y : ℝ) : ℝ := x + y + (2 - x) * bin_ent 2 (1 / (2 - x))
noncomputable def f2 (x y : ℝ) : ℝ := x + y + (2 - x) * bin_ent 2 (1 / (2 - x)) -
  1 / (log 2 * 40) * ((1 - x) / (2 - x))

noncomputable def f (x y : ℝ) : ℝ := if 3 / 4 ≤ x then f2 x y else f1 x y
noncomputable def g (x y : ℝ) : ℝ := G (2 / 5) x y

lemma f_eq (x y : ℝ) : f x y =
  f1 x y - if 3 / 4 ≤ x then 1 / (log 2 * 40) * ((1 - x) / (2 - x)) else 0 :=
begin
  rw [f, f1, f2],
  split_ifs,
  { refl },
  rw [sub_zero]
end

lemma g_eq (x y : ℝ) :
  g x y = logb 2 (5 / 2) + x * logb 2 (5 / 3) + y * logb 2 (2 / 5 * ((x + y) / y)) :=
by { rw [g, G], norm_num }
-- noncomputable def F (k : ℕ) (x y : ℝ) : ℝ :=
--   x + y + logb 2 (ramsey_number ![k, ⌊(k : ℝ) - x * k⌋₊]) / k

lemma twelve_one {b' : ℝ} (hb' : 1 < b') {a b : ℕ} (h : b ≤ a) :
  logb b' (a.choose b) ≤ a * bin_ent b' (b / a) :=
begin
  rcases b.eq_zero_or_pos with rfl | hb,
  { simp only [nat.choose_zero_right, nat.cast_one, logb_one, nat.cast_zero, zero_div, bin_ent_zero,
      mul_zero] },
  rcases eq_or_lt_of_le h with rfl | hab,
  { rw [div_self],
    { simp },
    positivity },
  have : 0 < a := hb.trans_le h,
  have : 0 < (1 - b / a : ℝ) := sub_pos_of_lt ((div_lt_one (by positivity)).2 (nat.cast_lt.2 hab)),
  have : (b / a : ℝ) ^ b * (1 - b / a) ^ (a - b) * a.choose b ≤ 1,
  { have := add_pow (b / a : ℝ) (1 - b / a) a,
    rw [add_sub_cancel'_right, one_pow] at this,
    refine this.symm.trans_ge _,
    have : b ∈ finset.range (a + 1), { rwa [finset.mem_range_succ_iff] },
    refine (finset.single_le_sum _ this).trans_eq' rfl,
    { intros i hi,
      positivity } },
  rwa [bin_ent, mul_sub, ←mul_assoc, ←mul_assoc, mul_neg, mul_one_sub, mul_div_cancel',
    le_sub_iff_add_le, neg_mul, le_neg_iff_add_nonpos_left, ←logb_pow, ←nat.cast_sub h, ←logb_pow,
    ←logb_mul, mul_comm, ←logb_mul, ←mul_assoc, logb_nonpos_iff' hb'],
  { positivity },
  { positivity },
  { exact (mul_pos (by positivity) (nat.cast_pos.2 (nat.choose_pos h))).ne' },
  { exact (nat.cast_pos.2 (nat.choose_pos h)).ne' },
  { positivity },
  { positivity },
end

-- lemma ten_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
--   ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
--   ∀ γ δ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 5 → δ = γ / 40 →
--   (ramsey_number ![k, l] : ℝ) ≤ exp (- δ * k + 2.05) * (k + l).choose l :=

-- lemma eleven_three (μ : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) :
--   ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
--     ∀ᶠ k : ℕ in at_top,
--     ∀ n : ℕ, 2 ≤ n →
--     ∀ χ : top_edge_labelling (fin n) (fin 2),
--     ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
--     ∀ (ini : book_config χ), 1 / 2 ≤ ini.p → ⌊(n / 2 : ℝ)⌋₊ ≤ ini.Y.card →
--     let s := (density_steps μ k k ini).card,
--         t := (red_steps μ k k ini).card
--     in logb 2 n ≤ logb 2 (ramsey_number ![k, k - t]) + s + t + f k :=

lemma y_le_x_mul (μ η : ℝ) (hμ₀ : 0 < μ) (hμ₁ : μ < 1) (hη : 0 < η) :
  ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n →
    ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p →
    let s := (density_steps μ k k ini).card,
        t := (red_steps μ k k ini).card
    in (s / k : ℝ) ≤ (μ / (1 - μ)) * (t / k) + η :=
begin
  have hp₀ : (0 : ℝ) < 1 / 2 := by norm_num1,
  have : (λ k : ℕ, (7 / (1 - μ)) * k ^ (15 / 16 : ℝ)) =o[at_top] (λ k : ℕ, (k : ℝ)),
  { refine is_o.const_mul_left _ _,
    suffices : (λ k : ℝ, k ^ (15 / 16 : ℝ)) =o[at_top] id,
    { exact is_o.comp_tendsto this tendsto_coe_nat_at_top_at_top },
    simpa only [rpow_one] using is_o_rpow_rpow (show (15 / 16 : ℝ) < 1, by norm_num) },
  filter_upwards [eight_five _ _ _ hμ₀ hμ₁ hp₀, beta_pos _ _ _ hμ₀ hμ₁ hp₀,
    beta_le_μ _ _ _ hμ₀ hμ₁ hp₀, this.bound hη,
    eventually_gt_at_top 0] with k h₈₅ hβ₀ hβμ hη' hk₀ n hn χ hχ ini hini,
  specialize h₈₅ k le_rfl μ le_rfl le_rfl n χ hχ ini hini,
  specialize hβ₀ k le_rfl _ le_rfl le_rfl n χ ini hini,
  specialize hβμ _ le_rfl _ le_rfl le_rfl n χ ini hini,
  rw [div_le_iff, add_mul, mul_assoc, div_mul_cancel],
  rotate,
  { positivity },
  { positivity },
  refine h₈₅.trans (add_le_add _ _),
  { refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
    rwa [div_le_div_iff, mul_one_sub, mul_one_sub, mul_comm, sub_le_sub_iff_right],
    { exact sub_pos_of_lt (hβμ.trans_lt hμ₁) },
    { exact sub_pos_of_lt hμ₁ } },
  { rw [norm_eq_abs, norm_coe_nat] at hη',
    exact (le_abs_self _).trans hη' },
end

lemma x_le_1 :
  ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n → ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p →
    let t := (red_steps (2 / 5) k k ini).card
    in t ≤ k ∧ (t / k : ℝ) ≤ 1 :=
begin
  have hμ₀ : (0 : ℝ) < 2 / 5 := by norm_num1,
  have hμ₁ : (2 / 5 : ℝ) < 1 := by norm_num1,
  filter_upwards [eventually_gt_at_top 0] with k hk₀
    n hn2 χ hχ ini hini,
  suffices : (red_steps (2 / 5) k k ini).card ≤ k,
  { refine ⟨this, div_le_one_of_le _ (nat.cast_nonneg _)⟩,
    rwa nat.cast_le },
  exact four_four_red _ hk₀.ne' hk₀.ne' hχ _
end

lemma y_le_3_4 :
  ∀ᶠ k : ℕ in at_top,
    ∀ n : ℕ, 2 ≤ n → ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, k] c ≤ m.card) →
    ∀ (ini : book_config χ), 1 / 2 ≤ ini.p →
    let s := (density_steps (2 / 5) k k ini).card
    in (s / k : ℝ) ≤ 0.75 :=
begin
  have hμ₀ : (0 : ℝ) < 2 / 5 := by norm_num1,
  have hμ₁ : (2 / 5 : ℝ) < 1 := by norm_num1,
  have hη : (0 : ℝ) < 1 / 12 := by norm_num1,
  filter_upwards [y_le_x_mul (2 / 5) (1 / 12) hμ₀ hμ₁ hη, eventually_gt_at_top 0] with k hk hk₀
    n hn2 χ hχ ini hini,
  specialize hk n hn2 χ hχ ini hini,
  refine hk.trans _,
  have : ((red_steps (2 / 5) k k ini).card : ℝ) / k ≤ 1,
  { refine div_le_one_of_le _ (nat.cast_nonneg _),
    rw nat.cast_le,
    exact four_four_red _ hk₀.ne' hk₀.ne' hχ _ },
  norm_num1,
  linarith only [this],
end

section

theorem bin_ent_hundredth_left : logb 2 (1 / 100)⁻¹ ≤ 20 / 3 :=
begin
  rw [inv_div, div_one, le_div_iff, mul_comm],
  have : logb 2 (100 ^ 3) = 3 * logb 2 100,
  { rw [logb_pow],
    norm_num },
  rw [←this, logb_le_iff_le_rpow one_lt_two],
  { norm_num1 },
  { norm_num1 },
  { norm_num1 },
end

theorem bin_ent_hundredth_right : 99 * logb 2 ((100 - 1) / 100)⁻¹ ≤ 1.5 :=
begin
  have : ((100 - 1 : ℝ) / 100)⁻¹ = 1 + 1 / 99,
  { norm_num1 },
  rw [this, logb, mul_div_assoc', div_le_iff (log_pos one_lt_two)],
  have : log (1 + 1 / 99) ≤ 1 / 99,
  { rw [add_comm, log_le_iff_le_exp],
    { exact add_one_le_exp _ },
    { norm_num1 } },
  have : 1 ≤ 3 / 2 * log 2,
  { rw [←div_le_iff'],
    refine log_two_gt_d9.le.trans' (by norm_num1),
    norm_num1 },
  linarith,
end

theorem bin_ent_hundredth : bin_ent 2 0.01 ≤ 0.1 :=
begin
  rw [bin_ent, neg_mul, ←mul_neg, ←logb_inv, sub_eq_add_neg, ←mul_neg, ←logb_inv, one_sub_div],
  linarith only [bin_ent_hundredth_left, bin_ent_hundredth_right],
  norm_num1
end

end

-- lemma eq_62 :

-- 1 - 1 / (2 - x) = ((2 - x) - 1) / (2 - x) = (1 - x) / (2 - x)
lemma F_le_f1_aux {k t : ℕ} {x : ℝ} (hx : x = t / k) (hk : 0 < k) (hx1 : x ≤ 1) :
  logb 2 ((k + (k - t)).choose k) ≤ k * ((2 - x) * bin_ent 2 (1 / (2 - x))) :=
begin
  have : t ≤ k,
  { contrapose! hx1,
    rwa [hx, one_lt_div, nat.cast_lt],
    rwa [nat.cast_pos] },
  refine (twelve_one one_lt_two le_self_add).trans _,
  have h₁ : (↑(k + (k - t)) : ℝ) = k * (2 - x),
  { rw [hx, mul_sub, mul_div_cancel', nat.cast_add, nat.cast_sub this],
    { ring_nf },
    positivity },
  rw [h₁, ←div_div, div_self, mul_assoc],
  positivity
end

lemma F_le_f1 {k t : ℕ} {x : ℝ} (hx : x = t / k) (hk : 0 < k) (hx1 : x ≤ 1) :
  logb 2 (ramsey_number ![k, k - t]) ≤ k * ((2 - x) * bin_ent 2 (1 / (2 - x))) :=
begin
  have : t ≤ k,
  { contrapose! hx1,
    rwa [hx, one_lt_div, nat.cast_lt],
    rwa [nat.cast_pos] },
  rcases eq_or_ne t k with rfl | htk,
  { rw [div_self] at hx,
    rw [hx, ramsey_number_pair_swap],
    { norm_num },
    positivity },
  have : 0 < k - t := nat.sub_pos_of_lt (lt_of_le_of_ne this htk),
  refine (F_le_f1_aux hx hk hx1).trans' (logb_le_logb_of_le one_le_two _ _),
  { rw [nat.cast_pos, ramsey_number_pos, fin.forall_fin_two],
    exact ⟨hk.ne', this.ne'⟩ },
  rw [nat.cast_le],
  exact ramsey_number_le_choose',
end

lemma eleven_one_special (η : ℝ) (hη : 0 < η) :
  ∀ᶠ k : ℕ in at_top,
    let t := (red_steps (2 / 5) k k (get_ini k)).card,
        x := (t : ℝ) / k in
    t ≤ k →
    0.75 ≤ x → x ≤ 0.99 →
    logb 2 (ramsey_number ![k, k - t]) ≤
      k * (((2 - x) * bin_ent 2 (1 / (2 - x))) - 1 / (log 2 * 40) * ((1 - x) / (2 - x)) + η) :=
begin
  have hγ₀ : (0 : ℝ) < 1 / 101 := by norm_num1,
  have q := (tendsto_nat_ceil_at_top.comp (tendsto_id.at_top_mul_const'
    (show (0 : ℝ) < 0.01, by positivity))).comp tendsto_coe_nat_at_top_at_top,
  filter_upwards [q.eventually (top_adjuster (ten_one_precise _ hγ₀)), eventually_gt_at_top 0,
    eventually_ge_at_top ⌈41 / 20 / log 2 / η⌉₊] with
    k hk hk₀ hkη htk hxl hxu,
  set t := (red_steps (2 / 5) k k (get_ini k)).card,
  set x := (t : ℝ) / k,
  have h₁ : ⌈(k : ℝ) * (1 / 100)⌉₊ ≤ k - t,
  { rw [nat.ceil_le, nat.cast_sub htk],
    rw [div_le_iff] at hxu,
    { linarith only [hxu] },
    positivity },
  have h2x : 0 < 2 - x := sub_pos_of_lt (hxu.trans_lt (by norm_num1)),
  have h₂ : (↑(k - t) : ℝ) / (↑k + ↑(k - t)) = 1 - 1 / (2 - x),
  { rw [nat.cast_sub htk, one_sub_div h2x.ne', sub_div' _ (2 : ℝ), div_sub',
      div_div_div_cancel_right, mul_one, two_mul, sub_sub, add_sub_add_right_eq_sub, add_sub_assoc],
    { positivity },
    { positivity },
    { positivity } },
  have h₃ : (↑(k - t) : ℝ) / (↑k + ↑(k - t)) ≤ 1 / 5,
  { rw [h₂, sub_le_comm, le_one_div _ h2x, sub_le_comm],
    { exact hxl.trans' (by norm_num1) },
    { norm_num1 } },
  have h₄ : (1 : ℝ) / 101 ≤ (↑(k - t) : ℝ) / (↑k + ↑(k - t)),
  { rw [h₂, le_sub_comm, one_div_le h2x, le_sub_comm],
    { exact hxu.trans (by norm_num1) },
    norm_num1 },
  specialize hk (k - t) h₁ k _ _ rfl h₄ h₃ rfl,
  rcases eq_or_ne (red_steps (2 / 5) k k (get_ini k)).card k with htk | htk',
  { have : ((red_steps (2 / 5) k k (get_ini k)).card : ℝ) / k = 1,
    { rw [htk, div_self],
      positivity },
    rw [this] at hxu,
    norm_num1 at hxu },
  have : 0 < k - t := nat.sub_pos_of_lt (lt_of_le_of_ne htk htk'),
  have h₅ : (0 : ℝ) < ramsey_number ![k, k - t],
  { rw [nat.cast_pos, ramsey_number_pos, fin.forall_fin_two],
    exact ⟨hk₀.ne', this.ne'⟩ },
  have h₆ : 1 - 1 / (2 - x) = (1 - x) / (2 - x),
  { rw [one_sub_div h2x.ne', sub_sub, add_comm, ←sub_sub],
    norm_num1,
    refl },
  refine (logb_le_logb_of_le one_le_two h₅ hk).trans _,
  have h₇ : (0 : ℝ) < (k + (k - t)).choose k,
  { rw [nat.cast_pos],
    exact nat.choose_pos le_self_add },
  rw [←nat.choose_symm_add, logb_mul (exp_pos _).ne' h₇.ne', logb, log_exp],
  refine (add_le_add_left (F_le_f1_aux rfl hk₀ (hxu.trans (by norm_num1))) _).trans _,
  rwa [mul_add, mul_sub, sub_add, neg_mul, sub_eq_add_neg (k * _ : ℝ), add_comm,
    add_le_add_iff_left, h₂, h₆, neg_add_eq_sub, sub_div, ←div_mul_eq_mul_div, div_div _ (40 : ℝ),
    neg_sub, mul_comm (k : ℝ), mul_comm (k : ℝ), mul_comm (1 / _ : ℝ), ←div_eq_mul_one_div,
    mul_comm (40 : ℝ), sub_le_sub_iff_right, ←div_le_iff' hη, ←nat.ceil_le],
end

lemma eleven_one_large_end {x y : ℝ} (hx : x ∈ set.Icc (0 : ℝ) 1) (hy : y ∈ set.Icc (0 : ℝ) 0.75)
  (hx' : 0.99 ≤ x) :
  (2 - x) * bin_ent 2 (1 / (2 - x)) + (y + x) ≤ 39 / 20 :=
begin
  rcases hx with ⟨hx₀, hx₁⟩,
  suffices : (2 - x) * bin_ent 2 (1 / (2 - x)) ≤ 0.2,
  { linarith only [this, hx₁, hy.2] },
  have : x ≤ 1 / (2 - x),
  { rw [le_div_iff],
    { nlinarith },
    linarith only [hx₁] },
  have hb := (strict_anti_on_bin_ent_half_one one_lt_two).antitone_on,
  rw antitone_on_Icc_iff at hb,
  have : (2 - x) * bin_ent 2 (1 / (2 - x)) ≤ 2 * bin_ent 2 x,
  { have h : 1 / (2 - x) ≤ 1,
    { rw [div_le_one]; linarith },
    refine mul_le_mul (by linarith [hx₀]) _ (bin_ent_nonneg one_lt_two (hx₀.trans this) h)
      two_pos.le,
    exact hb _ _ (hx'.trans' (by norm_num1)) ‹_› h },
  refine this.trans _,
  rw [←le_div_iff' (zero_lt_two' ℝ)],
  refine (bin_ent_hundredth.trans_eq (by norm_num)).trans' _,
  rw [←@bin_ent_symm _ (1 / 100)],
  refine hb _ _ (by norm_num1) _ hx₁,
  exact hx'.trans' (by norm_num1),
end

lemma eleven_one (η : ℝ) (hη : 0 < η) :
  ∀ᶠ k in at_top,
    ∃ (x ∈ set.Icc (0 : ℝ) 1) (y ∈ set.Icc (0 : ℝ) 0.75),
    logb 2 (ramsey_number ![k, k]) / k ≤ max (min (f x y) (g x y)) 1.95 + η :=
begin
  have hμ₀ : (0 : ℝ) < 2 / 5 := by norm_num1,
  have hμ₁ : (2 / 5 : ℝ) < 1 := by norm_num1,
  obtain ⟨f₁, hf₁, hf₁'⟩ := eleven_two_improve _ hμ₀ hμ₁,
  obtain ⟨f₂, hf₂, hf₂'⟩ := eleven_three_special _ hμ₀ hμ₁,
  filter_upwards [hf₁', hf₂', (hf₁.add (@is_o_const_thing 1)).bound hη,
    (hf₂.add (@is_o_const_thing 1)).bound (half_pos hη), eventually_ge_at_top 4,
    y_le_3_4, x_le_1, eleven_one_special (η / 2) (half_pos hη)] with
    k hf₁ hf₂ hη₁ hη₂ hk₆ hy₃₄ hx₁ h₁₁,
  set t := (red_steps (2 / 5) k k (get_ini k)).card,
  set s := (density_steps (2 / 5) k k (get_ini k)).card,
  set R := ramsey_number ![k, k],
  clear hf₁' hf₂',
  specialize hy₃₄ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _ (get_ini_p' hk₆),
  specialize hx₁ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _ (get_ini_p' hk₆),
  replace hf₁ : logb 2 R - 1 ≤ k * G (2 / 5) (t / k) (s / k) + _ :=
    (R_k_close_to_n k hk₆).trans (hf₁ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _
      (get_ini_p' hk₆) (get_ini_card_X hk₆)),
  replace hf₂ : logb 2 R - 1 ≤ logb 2 (ramsey_number ![_, k - t]) + s + t + _ :=
    (R_k_close_to_n k hk₆).trans (hf₂ _ (two_le_n_of_large_k hk₆) _ (get_χ_ramsey hk₆) _
      (get_ini_p' hk₆) (get_ini_card_Y hk₆)),
  rw [sub_le_iff_le_add] at hf₁ hf₂,
  specialize h₁₁ hx₁.1,
  have hk₀ : 0 < k := hk₆.trans_lt' (by norm_num1),
  have hx : (t : ℝ) / k ∈ set.Icc (0 : ℝ) 1 := ⟨by positivity, hx₁.2⟩,
  have hy : (s : ℝ) / k ∈ set.Icc (0 : ℝ) 0.75 := ⟨by positivity, hy₃₄⟩,
  have hk₀' : (0 : ℝ) < k := nat.cast_pos.2 hk₀,
  rw ←g at hf₁,
  refine ⟨_, hx, _, hy, _⟩,
  rw [←sub_le_iff_le_add, max_min_distrib_right],
  have h₁ : f₁ k + 1 ≤ k * η,
  { rw [norm_coe_nat, norm_eq_abs, mul_comm] at hη₁,
    exact (le_abs_self _).trans hη₁ },
  have h₂ : (f₂ k + 1) / k ≤ η / 2,
  { rw [norm_coe_nat, norm_eq_abs, abs_le, ←div_le_iff hk₀'] at hη₂,
    exact hη₂.2 },
  refine le_min _ _,
  swap,
  { refine le_max_of_le_left _,
    rw [sub_le_iff_le_add, div_le_iff' hk₀'],
    refine hf₁.trans _,
    rw [mul_add, add_assoc, add_le_add_iff_left],
    exact h₁ }, -- f₁ k + 1 ≤ k * η
  rw [sub_le_iff_le_add],
  refine (div_le_div_of_le hk₀'.le hf₂).trans _,
  rw [←max_add_add_right],
  cases lt_or_le 0.99 ((t : ℝ) / k) with hx99 hx99,
  { refine le_max_of_le_right _,
    rw [add_assoc, add_div, add_assoc],
    refine add_le_add _ (h₂.trans (half_le_self hη.le)), -- (f₂ k + 1) / k ≤ η
    rw [add_div, add_div],
    refine (add_le_add_right (div_le_div_of_le hk₀'.le (F_le_f1 rfl hk₀ hx.2)) _).trans _,
    rw [mul_div_cancel_left _ hk₀'.ne'],
    exact eleven_one_large_end hx hy hx99.le },
  refine le_max_of_le_left _,
  cases lt_or_le ((t : ℝ) / k) 0.75 with hx34 hx34,
  { rw [f, if_neg hx34.not_le, f1, add_assoc, add_div, add_div, add_div],
    refine add_le_add _ (h₂.trans (half_le_self hη.le)),
    rw [add_right_comm, add_rotate, add_le_add_iff_left, div_le_iff' hk₀'],
      exact F_le_f1 rfl hk₀ hx.2 },
  rw [f, if_pos hx34, f2, add_assoc, add_div, add_div, add_div, add_assoc, add_assoc],
  refine (add_le_add_right (div_le_div_of_le hk₀'.le (h₁₁ hx34 hx99)) _).trans _,
  rw [mul_div_cancel_left _ hk₀'.ne', add_sub_assoc, add_assoc, add_right_comm, add_comm,
    add_le_add_iff_right, add_assoc, add_left_comm, add_left_comm (t / k : ℝ), add_le_add_iff_left,
    add_left_comm, add_le_add_iff_left],
  have : (f₂ k + 1) / k ≤ η / 2 := h₂,
  exact (add_le_add_left this _).trans_eq (add_halves _),
end

end simple_graph
