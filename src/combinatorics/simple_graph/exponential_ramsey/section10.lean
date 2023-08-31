import combinatorics.simple_graph.exponential_ramsey.section9

namespace simple_graph

open_locale big_operators exponential_ramsey nat real

open filter finset nat real asymptotics

lemma large_gamma_part_one_aux {γ η : ℝ} (h : γ ≤ 1 / 5) (hη : η ≤ (1 / 800) * γ):
  (3199 / 4000) ^ (5 / 4 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  refine (nine_two_monotone (1 / 5) (3199 / 4000) h _ (by norm_num1) (by norm_num1)
    (by norm_num1)).trans_eq' _,
  { linarith only [h, hη] },
  norm_num1,
  refl,
end

lemma large_gamma_part_one {γ η : ℝ} (h : γ ≤ 1 / 5) (hη : η ≤ (1 / 800) * γ) :
  exp (- 1 / 3 + 1 / 20 + 1 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  refine (large_gamma_part_one_aux h hη).trans' _,
  have : (0 : ℝ) < 3199 / 4000 := by norm_num1,
  rw [←le_log_iff_exp_le (rpow_pos_of_pos this _), log_rpow this, ←div_le_iff'],
  swap, { positivity },
  norm_num1,
  rw [neg_le, ←log_inv, inv_div, le_div_iff, mul_comm, ←log_rpow, log_le_iff_le_exp, ←exp_one_rpow],
  { refine (rpow_le_rpow (by norm_num1) exp_one_gt_d9.le (by norm_num1)).trans' _,
    norm_num },
  { exact rpow_pos_of_pos (by norm_num1) _ },
  { norm_num1 },
  { norm_num1 },
end

lemma large_gamma_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 1 / 5)
  (hηγ : η ≤ (1 / 800) * γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
  (h : exp (- 1 / 3 + 1 / 20 + 1 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
  exp ((250 / 3200) * (γ * t ^ 2 / k)) ≤
    exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
begin
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ],
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le],
  refine (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
    (exp_pos _).le).trans' _,
  rw [←exp_one_rpow (_ + _), ←rpow_mul (exp_pos _).le, exp_one_rpow, ←real.exp_add, exp_le_exp,
    sq, ←mul_assoc, mul_div_assoc, mul_div_assoc, mul_left_comm, mul_comm _ (γ * t), ←mul_add,
    div_add', div_mul_div_comm],
  swap, { positivity },
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw [div_le_iff, div_mul_comm, mul_div_mul_right],
  { linarith },
  { positivity },
  { positivity },
end

lemma large_gamma_part_three {k t : ℕ} {γ : ℝ} (hγl : 3 / 20 < γ)
  (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
  exp ((-240 / 3200) * (γ * t ^ 2 / k)) ≤ exp (- (1 / 200) * k) :=
begin
  rw [exp_le_exp, neg_mul, neg_div, neg_mul, neg_le_neg_iff, mul_div_assoc', le_div_iff,
    ←mul_assoc],
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ ht 2) _).trans' _,
  { positivity },
  { positivity },
  rw [mul_pow, ←mul_assoc (_ * γ), mul_assoc, ←sq (k : ℝ)],
  { refine mul_le_mul_of_nonneg_right _ (by positivity),
    norm_num1,
    linarith only [hγl] },
  { positivity },
end

lemma small_gamma_part_one_aux {γ η : ℝ} (h : γ ≤ 3 / 20) (hη : η ≤ (1 / 800) * γ):
  (13597 / 16000) ^ (20 / 17 : ℝ) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  refine (nine_two_monotone (3 / 20) (13597 / 16000) h _ (by norm_num1) (by norm_num1)
    (by norm_num1)).trans_eq' _,
  { linarith only [h, hη] },
  norm_num1,
  refl,
end

lemma small_gamma_part_one {γ η : ℝ} (h : γ ≤ 3 / 20) (hη : η ≤ (1 / 800) * γ) :
  exp (- 1 / 3 + 37 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ)) :=
begin
  have : exp (- 1 / 3 + 37 / 480) ≤ exp (- 7 / 34),
  { rw exp_le_exp,
    norm_num },
  refine (small_gamma_part_one_aux h hη).trans' (this.trans _),
  have : (0 : ℝ) < 13597 / 16000 := by norm_num1,
  rw [←le_log_iff_exp_le (rpow_pos_of_pos this _), log_rpow this, ←div_le_iff'],
  swap, { positivity },
  norm_num1,
  rw [neg_le, ←log_inv, inv_div, le_div_iff, mul_comm, ←log_rpow, log_le_iff_le_exp, ←exp_one_rpow],
  { refine (rpow_le_rpow (by norm_num1) exp_one_gt_d9.le (by norm_num1)).trans' _,
    norm_num },
  { exact rpow_pos_of_pos (by norm_num1) _ },
  { norm_num1 },
  { norm_num1 },
end

lemma small_gamma_part_two {k t : ℕ} {γ η : ℝ} (hγl : 0 ≤ γ) (hγu : γ ≤ 3 / 20)
  (hηγ : η ≤ (1 / 800) * γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
  (h : exp (- 1 / 3 + 37 / 480) ≤ (1 - γ - η) ^ (1 / (1 - γ))) :
  exp ((370 / 3200) * (γ * t ^ 2 / k)) ≤
    exp (γ * t ^ 2 / (2 * k)) * (1 - γ - η) ^ (γ * t / (1 - γ)) :=
begin
  have : 0 < 1 - γ - η := by linarith only [hγu, hηγ],
  rw [div_eq_mul_one_div _ (1 - γ), mul_comm _ (1 / (1 - γ)), rpow_mul this.le],
  refine (mul_le_mul_of_nonneg_left (rpow_le_rpow (exp_pos _).le h (by positivity))
    (exp_pos _).le).trans' _,
  rw [←exp_one_rpow (_ + _), ←rpow_mul (exp_pos _).le, exp_one_rpow, ←real.exp_add, exp_le_exp,
    sq, ←mul_assoc, mul_div_assoc, mul_div_assoc, mul_left_comm, mul_comm _ (γ * t), ←mul_add,
    div_add', div_mul_div_comm],
  swap, { positivity },
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw [div_le_iff, div_mul_comm, mul_div_mul_right],
  { linarith },
  { positivity },
  { positivity },
end

lemma small_gamma_part_three {k t : ℕ} {γ : ℝ} (hγl : 1 / 10 ≤ γ)
  (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
  exp ((-360 / 3200) * (γ * t ^ 2 / k)) ≤ exp (- (1 / 200) * k) := -- 9 / 80
begin
  rw [exp_le_exp, neg_mul, neg_div, neg_mul, neg_le_neg_iff, mul_div_assoc', le_div_iff,
    ←mul_assoc],
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ ht 2) _).trans' _,
  { positivity },
  { positivity },
  rw [mul_pow, ←mul_assoc (_ * γ), mul_assoc, ←sq (k : ℝ)],
  { refine mul_le_mul_of_nonneg_right _ (by positivity),
    norm_num1,
    linarith only [hγl] },
  { positivity },
end

lemma ten_two_exp_approx {η γ : ℝ} (hγu : γ ≤ 1 / 5) (hγl : 0 ≤ η) (hηγ : η ≤ 1 / 800 * γ) :
  exp (- 3 * η / 2) ≤ (1 - γ - η) / (1 - γ) :=
begin
  rw [←one_sub_div, ←div_mul_eq_mul_div],
  swap, { linarith },
  have h₂ : - 1 / 5 ≤ (-3 / 2) * η := by linarith,
  refine (general_convex_thing' (by linarith) h₂ (by norm_num)).trans _,
  have : 1 + (-5 / 4) * η ≤ 1 - η / (1 - γ),
  { rw [neg_div, neg_mul, ←sub_eq_add_neg, sub_le_sub_iff_left, div_eq_mul_one_div, mul_comm],
    refine mul_le_mul_of_nonneg_right _ hγl,
    rw [div_le_iff];
    linarith },
  refine this.trans' _,
  rw [←mul_assoc, ←div_mul_eq_mul_div, add_le_add_iff_left],
  refine mul_le_mul_of_nonneg_right _ hγl,
  suffices : exp (- 1 / 5) ≤ 5 / 6,
  { rw [mul_div_assoc, ←le_div_iff, sub_le_iff_le_add],
    { exact this.trans_eq (by norm_num1) },
    { norm_num1 } },
  refine le_of_pow_le_pow 5 (by norm_num1) (by norm_num1) _,
  rw [←exp_nat_mul, nat.cast_bit1, nat.cast_two, mul_div_cancel', ←inv_div, inv_pow, real.exp_neg],
  { refine inv_le_inv_of_le (by norm_num1) (exp_one_gt_d9.le.trans' (by norm_num1)) },
  { norm_num1 },
end

lemma ten_two_exp_approx_more {k t : ℕ} {η γ : ℝ}
  (hγu : γ ≤ 1 / 5) (hγl : 0 ≤ η) (hηγ : η ≤ 1 / 800 * γ)
  (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k) :
  exp ((-9 / 3200) * (γ * t ^ 2 / k)) ≤ ((1 - γ - η) / (1 - γ)) ^ t :=
begin
  refine (pow_le_pow_of_le_left (exp_pos _).le (ten_two_exp_approx hγu hγl hηγ) _).trans' _,
  rw [←exp_nat_mul, exp_le_exp, neg_div, neg_mul, neg_mul, neg_div, mul_neg, neg_le_neg_iff, sq,
    ←div_mul_eq_mul_div, mul_div_assoc', le_div_iff, mul_comm _ η, mul_assoc, mul_assoc,
    mul_left_comm γ t, mul_left_comm (_ / _ : ℝ) t],
  swap, { positivity },
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  refine (mul_le_mul_of_nonneg_right hηγ (by positivity)).trans _,
  rw [mul_assoc, mul_left_comm, mul_left_comm _ γ],
  exact mul_le_mul_of_nonneg_left (by linarith only [ht]) (by linarith only [hγl, hηγ]),
end

lemma ten_two_end {k t : ℕ} {γ η fk : ℝ} (hγ₀' : 0 < γ) (ht : (2 / 3 : ℝ) * k ≤ t) (hk : 0 < k)
  (hγl : 1 / 10 ≤ γ) (hγu : γ ≤ 1 / 5) (hη : 0 ≤ η) (hηγ : η ≤ 1 / 800 * γ)
  (hfk : -fk ≤ 1 / 72000 * k) :
  1 ≤ real.exp (-(1 / 200) * k + fk) * (1 - γ - η) ^ (γ * t / (1 - γ)) *
    ((1 - γ - η) / (1 - γ)) ^ t * exp (γ * t ^ 2 / (2 * k)) :=
begin
  rw [mul_right_comm],
  refine (mul_le_mul_of_nonneg_left (ten_two_exp_approx_more hγu hη hηγ ht hk) _).trans' _,
  { refine mul_nonneg (mul_nonneg (exp_pos _).le _) (exp_pos _).le,
    refine rpow_nonneg_of_nonneg _ _,
    linarith only [hηγ, hγu] },
  rw [mul_right_comm (real.exp _), mul_assoc (real.exp _), mul_right_comm, add_comm, real.exp_add,
    mul_right_comm (real.exp _)],
  have : 0 ≤ fk + 1 / 3200 * (γ * t ^ 2 / k),
  { rw ←neg_le_iff_add_nonneg',
    refine hfk.trans _,
    rw [mul_div_assoc', le_div_iff, mul_assoc, ←sq],
    refine (mul_le_mul_of_nonneg_left (mul_le_mul hγl (pow_le_pow_of_le_left (by positivity) ht _)
      (sq_nonneg _) hγ₀'.le) (by norm_num1)).trans_eq' _,
    { rw [mul_pow, ←mul_assoc, ←mul_assoc],
      norm_num },
    rwa nat.cast_pos },
  cases le_or_lt γ (3 / 20),
  { refine (mul_le_mul_of_nonneg_left (small_gamma_part_two hγ₀'.le h hηγ ht hk
      (small_gamma_part_one h hηγ)) (by positivity)).trans' _,
    rw [mul_right_comm],
    refine (mul_le_mul_of_nonneg_left (small_gamma_part_three hγl ht hk) (by positivity)).trans' _,
    rw [←real.exp_add, ←real.exp_add, ←real.exp_add, one_le_exp_iff],
    linarith only [this] },
  { refine (mul_le_mul_of_nonneg_left (large_gamma_part_two hγ₀'.le hγu hηγ ht hk
      (large_gamma_part_one hγu hηγ)) (by positivity)).trans' _,
    rw [mul_right_comm],
    refine (mul_le_mul_of_nonneg_left (large_gamma_part_three h ht hk) (by positivity)).trans' _,
    rw [←real.exp_add, ←real.exp_add, ←real.exp_add, one_le_exp_iff],
    linarith only [this] },
end

open finset

lemma ten_two :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ η : ℝ, γ = l / (k + l) → 1 / 10 ≤ γ → γ ≤ 1 / 5 → 0 ≤ η → η ≤ 1 / 800 * γ →
  ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2), 1 - γ - η ≤ χ.density 0 →
  exp (- (1 / 200) * (k : ℝ)) * (k + l).choose l ≤ n →
  (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) :=
begin
  have hγ₀ : (0 : ℝ) < 1 / 10 := by norm_num1,
  obtain ⟨f, hf, hf'⟩ := nine_five,
  filter_upwards [nine_three_lower_n (1 / 10) hγ₀, nine_three _ hγ₀, hf' _ hγ₀,
    top_adjuster (eventually_gt_at_top 0),
    top_adjuster (hf.bound (by norm_num1 : (0 : ℝ) < 1 / 72000))]
    with l hn₂ h₉₃ h₉₅ hk₀ hfk
      k γ η hγ hγl hγu hη hηγ n χ hχd hn,
  clear hf',
  have hγ₁ : γ < 1 := hγu.trans_lt (by norm_num1),
  have hl₀ : 0 < l := hk₀ l le_rfl,
  have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1)),
  have hγ₀' : 0 < γ := hγ₀.trans_le hγl,
  have hγ' : 1 / 200 ≤ γ / 20, { linarith only [hγl] },
  have hδ : 1 / 200 = min (1 / 200) (γ / 20),
  { rw [min_eq_left],
    exact hγ' },
  by_contra hχ,
  have hp₀ : 1 / 2 ≤ 1 - γ - η,
  { linarith only [hγu, hηγ] },
  specialize hn₂ k γ hγ hγl hγ₁ hlk _ le_rfl n (hn.trans' _),
  { refine mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (nat.cast_nonneg _),
    refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
    exact neg_le_neg hγ' },
  obtain ⟨ini, hini, hXc, hYc⟩ := exists_equibipartition_col_density χ hn₂,
  replace hini := hχd.trans hini,
  have hini4 : 1 / 4 ≤ ini.p,
  { exact hini.trans' (hp₀.trans' (by norm_num1)) },
  specialize h₉₃ k hlk γ hγ hγl (hγu.trans (by norm_num1)) _ hδ n χ hχ ini hini4 hXc hn,
  specialize h₉₅ k hlk γ (1 / 200) η hγ hγl (by norm_num1) hγ' hη hp₀ n χ hχ ini hini hYc hn,
  specialize hfk k hlk,
  rw [norm_eq_abs, abs_le', norm_coe_nat] at hfk,
  have := ten_two_end hγ₀' h₉₃ (hl₀.trans_le hlk) hγl hγu hη hηγ hfk.2,
  replace h₉₅ := h₉₅.trans' (mul_le_mul_of_nonneg_right this (nat.cast_nonneg _)),
  rw [one_mul, nat.cast_le, ←nat.choose_symm_add] at h₉₅,
  have := ramsey_number_le_finset (ramsey_number_le_choose'.trans h₉₅) χ,
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, tsub_le_iff_left,
    matrix.head_cons] at this hχ,
  obtain ⟨m, (⟨hm₀, hm₁, hm₂⟩ | ⟨hm₀, hm₁, hm₂⟩)⟩ := this,
  swap,
  { exact hχ ⟨m, or.inr ⟨hm₁, hm₂⟩⟩ },
  refine hχ ⟨(end_state γ k l ini).A ∪ m, or.inl ⟨_, hm₂.trans _⟩⟩,
  { rw [finset.coe_union, top_edge_labelling.monochromatic_of_union],
    refine ⟨(end_state γ k l ini).red_A, hm₁, _⟩,
    exact (end_state γ k l ini).red_XYA.symm.subset_right (hm₀.trans (finset.subset_union_right _ _)) },
  rwa [finset.card_union_eq, add_le_add_iff_right],
  { exact t_le_A_card γ (hk₀ k hlk).ne' (hk₀ l le_rfl).ne' ini },
  exact (end_state γ k l ini).hYA.symm.mono_right hm₀,
end

lemma ten_two_variant :
  ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
  ∀ γ η : ℝ, γ = l / (k + l) → 1 / 10 ≤ γ → γ ≤ 1 / 5 → 0 ≤ η → η ≤ 1 / 800 * γ →
  ∀ V : Type*, decidable_eq V → fintype V → ∀ χ : top_edge_labelling V (fin 2), by exactI
  1 - γ - η ≤ χ.density 0 →
  exp (- (1 / 200 : ℝ) * k) * (k + l).choose l ≤ fintype.card V →
  (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) :=
begin
  filter_upwards [ten_two] with l hl
    k γ η hγ hγl hγu hη hηγ V _inst_1 _inst_2 χ hχ hn,
  resetI,
  obtain ⟨e⟩ := fintype.trunc_equiv_fin V,
  let χ' : top_edge_labelling (fin (fintype.card V)) (fin 2) := χ.pullback e.symm.to_embedding,
  have : 1 - γ - η ≤ χ'.density 0,
  { refine hχ.trans_eq _,
    rw [top_edge_labelling.density, top_edge_labelling.density, rat.cast_inj],
    refine density_graph_iso _,
    exact (label_graph_iso _ _).symm },
  obtain ⟨m, c, hm, hmc⟩ := hl k γ η hγ hγl hγu hη hηγ (fintype.card V) χ' this hn,
  exact ⟨m.map e.symm.to_embedding, c, hm.map, hmc.trans_eq (finset.card_map _).symm⟩,
end

-- lemma nine_one_part_one {m : ℝ} (hm : 1 < m) :
--   (⌈(m / exp 1 : ℝ)⌉₊ : ℝ) < m :=

lemma gamma'_lt_one_tenth_iff {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) :
  (l - m : ℝ) / (k + l - m) < 1 / 10 ↔ (l - k / 9 : ℝ) < m :=
begin
  rw [add_sub_assoc, div_lt_div_iff, one_mul, ←sub_lt_iff_lt_add, ←mul_sub_one, ←lt_div_iff,
    sub_lt_comm],
  { norm_num1, refl },
  { norm_num1 },
  { rw [←nat.cast_sub h],
    positivity },
  { norm_num1 }
end

lemma gamma'_lt_one_tenth_iff' {k l m : ℕ} (h : m ≤ l) (h' : 0 < k) (hkl : k ≤ 9 * l) :
  (l - m : ℝ) / (k + l - m) < 1 / 10 ↔ ⌊(l - k / 9 : ℝ)⌋₊ < m :=
begin
  rw [gamma'_lt_one_tenth_iff h h', ←nat.floor_lt],
  rw [sub_nonneg, div_le_iff'],
  { exact_mod_cast hkl },
  { positivity },
end

lemma big_m_le_l {k l m : ℕ} (hm : m = ⌊(l - k / 9 : ℝ)⌋₊ + 1) (hkl : k ≤ 9 * l) (hk : 0 < k) :
  m ≤ l :=
begin
  rw [hm, nat.add_one_le_iff, nat.floor_lt, sub_lt_self_iff],
  { positivity },
  rw [sub_nonneg, div_le_iff'],
  { exact_mod_cast hkl },
  { positivity }
end

lemma small_gap_for_next {k l m : ℕ} (hm : m = ⌊(l - k / 9 : ℝ)⌋₊ + 1)
  (hkl : k ≤ 9 * l) (hk : 0 < k) :
  (1 / 10 : ℝ) - 1 / k ≤ (l - m : ℝ) / (k + l - m) :=
begin
  have hml : m ≤ l := big_m_le_l hm hkl hk,
  have h₃ : (l - m : ℝ) / (k + l - m) < 1 / 10,
  { rw [gamma'_lt_one_tenth_iff' hml hk hkl, hm],
    simp },
  have hm1 : 1 ≤ m,
  { rw [hm],
    simp },
  have habove : 1 / 10 ≤ (l - (m - 1) : ℝ) / (k + l - (m - 1)),
  { rw [←nat.cast_one, ←nat.cast_sub hm1, nat.cast_one, ←not_lt,
      gamma'_lt_one_tenth_iff' (hml.trans' (nat.sub_le _ _)) hk hkl, hm, nat.add_sub_cancel,
      not_lt] },
  rw [add_sub_assoc, ←nat.cast_sub hml] at h₃ ⊢,
  rw [add_sub_assoc, ←sub_add, ←nat.cast_sub hml] at habove,
  set b := l - m with hb,
  clear_value b,
  have h₁ : (0 : ℝ) < k + b,
  { positivity },
  have h₂ : (0 : ℝ) < k + b + 1,
  { exact add_pos h₁ zero_lt_one },
  have : (b + 1 : ℝ) / (k + b + 1) - b / (k + b) ≤ 1 / k,
  { rw [div_sub_div _ _ h₂.ne' h₁.ne', div_le_div_iff (mul_pos h₂ h₁), ←sub_nonneg],
    { ring_nf,
      positivity },
    positivity },
  rw ←add_assoc at habove,
  linarith only [habove, this]
end

-- lemma gamma_mul_k_le_m_of {k l m : ℕ} (h : m ≤ l) (h' : 0 < k)
--   (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2) :
--   (l / (k + l) : ℝ) * k ≤ m :=
-- begin
--   rw [gamma'_le_gamma_iff h h'] at hg,
--   refine hg.le.trans' _,
--   rw [div_mul_eq_mul_div, div_le_div_iff, ←sub_nonneg],
--   { ring_nf,
--     positivity },
--   { positivity },
--   { positivity },
-- end

-- lemma U_lower_bound_ratio_lower_bound_aux_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m ≤ l) (hk₀ : 0 < k)
--   (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
--   (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
--   (hn : exp (- δ * k) * (k + l).choose l ≤ n) :
--   ((k + l - m).choose k : ℝ) ≤ n * U_lower_bound_ratio (1 / 16) k l m :=
-- begin
--   have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml,
--   rw [U_lower_bound_ratio, add_comm (k : ℝ), ←this],
--   refine (mul_le_mul_of_nonneg_right hn _).trans' _,
--   { positivity },
--   rw [mul_div_assoc', mul_assoc, ←nat.choose_symm_add, add_comm l, mul_div_cancel',
--     add_tsub_assoc_of_le hml, nat.choose_symm_add, ←mul_assoc],
--   swap,
--   { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
--     exact nat.choose_pos (by simp) },
--   refine le_mul_of_one_le_left (nat.cast_nonneg _) _,
--   rw [neg_mul, real.exp_neg, inv_mul_eq_div, one_le_div (exp_pos _), hδ, div_mul_eq_mul_div, hγ],
--   refine (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le m).trans' _,
--   rw [←exp_nat_mul, mul_one_div, exp_le_exp],
--   exact div_le_div_of_le (by norm_num1) (gamma_mul_k_le_m_of hml hk₀ hg),
-- end

-- lemma U_lower_bound_ratio_lower_bound_aux {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
--   (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
--   (hg : (l - m : ℝ) / (k + l - m) < (l / (k + l)) ^ 2)
--   (hn : exp (- δ * k) * (k + l).choose l ≤ n) :
--   (k : ℝ) ≤ n * U_lower_bound_ratio (1 / 16) k l m :=
-- begin
--   refine (U_lower_bound_ratio_lower_bound_aux_aux hml.le hk₀ hγ hδ hg hn).trans' _,
--   rw [nat.cast_le, add_tsub_assoc_of_le hml.le],
--   have : 1 ≤ l - m,
--   { rw [nat.succ_le_iff],
--     exact nat.sub_pos_of_lt hml },
--   refine (nat.choose_le_choose k (add_le_add_left this k)).trans' _,
--   rw [nat.choose_symm_add, nat.choose_one_right],
--   simp
-- end

-- lemma U_lower_bound_ratio_lower_bound' {k l m n : ℕ} {γ δ : ℝ} (hml : m < l) (hk₀ : 0 < k)
--   (hlk : l ≤ k) (hγ : γ = l / (k + l)) (hδ : δ = γ / 20)
--   (hn : exp (- δ * k) * (k + l).choose l ≤ n) (h : (k : ℝ) < (l - 2) * l) :
--   (k : ℝ) ≤ n * U_lower_bound_ratio (1 / 16) k l m :=
-- begin
--   cases lt_or_le ((l - m : ℝ) / (k + l - m)) ((l / (k + l)) ^ 2) with h' h',
--   { exact U_lower_bound_ratio_lower_bound_aux hml hk₀ hγ hδ h' hn },
--   let mst := ⌊(l * (k + l) : ℝ) / (k + 2 * l)⌋₊ + 1,
--   have hm : m < mst,
--   { rw [←not_lt, gamma'_le_gamma_iff hml.le hk₀, not_lt] at h',
--     rw [←@nat.cast_lt ℝ],
--     refine h'.trans_lt _,
--     rw nat.cast_add_one,
--     exact nat.lt_floor_add_one _ },
--   rw ←sub_pos at h,
--   have : mst < l,
--   { rw [←@nat.cast_lt ℝ, nat.cast_add_one, ←lt_sub_iff_add_lt],
--     refine (nat.floor_le (by positivity)).trans_lt _,
--     rw [div_lt_iff, ←sub_pos],
--     { ring_nf, exact h },
--     { positivity } },
--   refine (U_lower_bound_ratio_lower_bound_aux this hk₀ hγ hδ _ hn).trans (mul_le_mul_of_nonneg_left
--     (U_lower_bound_decreasing k l (by norm_num1) (by norm_num1) hlk hk₀ hm.le) (nat.cast_nonneg _)),
--   rw [gamma'_le_gamma_iff this.le hk₀, nat.cast_add_one],
--   exact nat.lt_floor_add_one _
-- end

-- lemma small_k {k l : ℕ} {γ γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγl : γ₀ ≤ γ) (hγ : γ = l / (k + l))
--   (hk₀ : 0 < k) : (k : ℝ) ≤ l * (γ₀⁻¹ - 1) :=

lemma big_U' {U : ℕ} (hU : 801 ≤ U) : (U : ℝ) / (U - 1) * (1 + 0) ≤ 1 + 1 / 800 :=
begin
  have : (801 : ℝ) ≤ U, { exact (nat.cast_le.2 hU).trans_eq' (by norm_num1) },
  rw [div_mul_eq_mul_div, div_le_iff];
  linarith,
end

lemma exists_good_clique {n k l : ℕ} {χ : top_edge_labelling (fin n) (fin 2)} :
  ∃ x : finset (fin n), is_good_clique 0 k l χ x ∧
    ((x.card ≤ ⌊(l - k / 9 : ℝ)⌋₊ ∧ ∀ i ∉ x, is_good_clique 0 k l χ (insert i x) → false) ∨
     x.card = ⌊(l - k / 9 : ℝ)⌋₊ + 1) :=
begin
  classical,
  let s := finset.univ.filter
    (λ x, is_good_clique 0 k l χ x ∧ x.card ≤ ⌊(l - k / 9 : ℝ)⌋₊ + 1),
  have : s.nonempty,
  { refine ⟨∅, _⟩,
    simp [empty_is_good] },
  obtain h := finset.exists_maximal s this,
  simp only [finset.mem_filter, finset.mem_univ, true_and, finset.lt_eq_subset, and_imp,
    exists_prop] at h,
  obtain ⟨x, ⟨hx, hx₁⟩, hx₂⟩ := h,
  rw [le_iff_eq_or_lt, nat.lt_add_one_iff] at hx₁,
  refine ⟨x, hx, _⟩,
  cases hx₁,
  { exact or.inr hx₁ },
  refine or.inl ⟨hx₁, _⟩,
  intros i hi hi',
  refine hx₂ _ hi' _ (finset.ssubset_insert hi),
  rwa [finset.card_insert_of_not_mem hi, add_le_add_iff_right],
end

-- -- here
-- lemma maximally_good_clique {n k l : ℕ} {ξ ξ' : ℝ} {χ : top_edge_labelling (fin n) (fin 2)}
--   (hξ : 0 ≤ ξ)
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
--   {x : finset (fin n)}
--   (hU : ((common_blues χ x).card : ℝ) / ((common_blues χ x).card - 1) * (1 + ξ) ≤ 1 + ξ')
--   (hU' : 2 ≤ (common_blues χ x).card)
--   (hx : is_good_clique ξ k l χ x)
--   (h : ∀ y : finset (fin n), is_good_clique ξ k l χ y → ¬ x ⊂ y) :
--   1 - (1 + ξ') * ((l - x.card : ℝ) / (k + l - x.card)) ≤
--     (χ.pullback (function.embedding.subtype _ : common_blues χ x ↪ fin n)).density 0 :=

-- lemma nine_one_end {k l n : ℕ} {χ : top_edge_labelling (fin n) (fin 2)} {x : finset (fin n)}
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
--   (hx : is_good_clique (1 / 16) k l χ x)
--   (h : ∃ (m : finset (fin n)) (c : fin 2), m ⊆ common_blues χ x ∧ χ.monochromatic_of ↑m c ∧
--     ![k, l - x.card] c ≤ m.card) :
--   false :=
-- begin
--   simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
--     tsub_le_iff_right] at h,
--   obtain ⟨m, (hm | ⟨hm, hm', hm''⟩)⟩ := h,
--   { exact hχ ⟨m, 0, hm.2⟩ },
--   have : disjoint m x,
--   { refine disjoint.mono_left hm _,
--     simp only [disjoint_right, common_blues, mem_filter, mem_col_neighbors, mem_univ, true_and,
--       not_forall, not_exists],
--     intros i hi,
--     exact ⟨i, hi, λ q, (q rfl).elim⟩ },
--   refine hχ ⟨m ∪ x, 1, _, by simpa [this] using hm''⟩,
--   rw [coe_union, top_edge_labelling.monochromatic_of_union],
--   exact ⟨hm', hx.1, monochromatic_between_common_blues.symm.subset_left hm⟩,
-- end

-- lemma nine_one_part_two {k l n : ℕ} {γ δ : ℝ} {χ : top_edge_labelling (fin n) (fin 2)}
--   {x : finset (fin n)}
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
--   (hml : x.card < l) (hl₀ : 0 < l) (hlk : l ≤ k)
--   (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hm : exp (-δ * k) * (k + l).choose l ≤ n)
--   (hx : is_good_clique (1 / 16) k l χ x)
--   (hγ' : (l - x.card : ℝ) / (k + l - x.card) < (l / (k + l)) ^ 2) :
--   false :=
-- begin
--   have := nat.cast_le.1 ((U_lower_bound_ratio_lower_bound_aux_aux hml.le (hl₀.trans_le hlk) hγ hδ
--     hγ' hm).trans hx.2),
--   rw add_tsub_assoc_of_le hml.le at this,
--   have := ramsey_number_le_finset (ramsey_number_le_choose'.trans this) χ,
--   exact nine_one_end hχ hx this
-- end

-- lemma nine_one_part_three {k l m n : ℕ} {γ γ' δ : ℝ} {χ : top_edge_labelling (fin n) (fin 2)}
--   (hχ : ¬∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of ↑m c ∧ ![k, l] c ≤ m.card)
--   (hml : m < l) (hk₀ : 0 < k)
--   (hγ : γ = l / (k + l)) (hδ : δ = γ / 20) (hγ' : γ' = (l - m) / (k + l - m))
--   (h : exp (-δ * k) * ((k + l).choose l) * U_lower_bound_ratio (1 / 16) k l m <
--     exp (-(γ' / 20) * k) * ↑((k + (l - m)).choose (l - m))) :
--   false :=
-- begin
--   have : ((l + k - m).choose _ : ℝ) / _ = _ := choose_ratio hml.le,
--   rw [←nat.cast_add, add_comm l, add_tsub_assoc_of_le hml.le, nat.choose_symm_add] at this,
--   rw [←not_le] at h,
--   refine h _,
--   rw [U_lower_bound_ratio, ←nat.cast_add, ←this, nat.choose_symm_add, mul_assoc, mul_div_assoc',
--     mul_div_cancel', ←mul_assoc],
--   swap,
--   { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
--     exact nat.choose_pos (by simp) },
--   refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
--   refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (exp_pos _).le xi_numeric.le _)
--     (exp_pos _).le).trans' _,
--   rw [←exp_nat_mul, ←real.exp_add, exp_le_exp, hδ, neg_mul, neg_mul, neg_add_eq_sub,
--     le_sub_iff_add_le, neg_add_eq_sub, mul_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
--     ←sub_div, hγ, hγ', ←sub_mul],
--   refine div_le_div_of_le (by norm_num1) _,
--   rw [←le_div_iff],
--   swap,
--   { rw [nat.cast_pos], exact hk₀ },
--   refine (sub_le_sub_left (div_le_div_of_le_left _ _ (sub_le_self _ _)) _).trans _,
--   { rw [sub_nonneg, nat.cast_le], exact hml.le },
--   { rw [add_sub_assoc, ←nat.cast_sub hml.le], positivity },
--   { exact nat.cast_nonneg _ },
--   rw [←sub_div, sub_sub_self],
--   exact div_le_div_of_le_left (nat.cast_nonneg _) (by positivity) (by simp),
-- end

-- lemma gamma'_le_gamma {k l m : ℕ} (hk : 0 < k) (h : m ≤ l) :
--   (l - m : ℝ) / (k + l - m) ≤ l / (k + l) :=
-- begin
--   rw [div_le_div_iff, ←sub_nonneg],
--   { ring_nf,
--     positivity },
--   { rw [add_sub_assoc, ←nat.cast_sub h], positivity },
--   { positivity },
-- end

-- lemma l_minus_m_big (γ₀ : ℝ) (hγ₀ : 0 < γ₀) {k l m : ℕ} (hml : m ≤ l) (hl₀ : 0 < l)
--   (hkl : (k : ℝ) ≤ l * (γ₀⁻¹ - 1))
--   (h₁ : 0 < γ₀⁻¹ - 1 + 2)
--   (h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹)
--   (hγ' : (m : ℝ) ≤ l * (k + ↑l) / (k + 2 * l)) :
--   ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m :=
-- begin
--   rw [nat.ceil_le, nat.cast_sub hml, le_sub_comm, ←mul_one_sub],
--   refine hγ'.trans _,
--   rw mul_div_assoc,
--   refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
--   rw [div_le_iff, one_sub_mul, le_sub_comm, add_sub_add_left_eq_sub],
--   swap,
--   { positivity },
--   refine (mul_le_mul_of_nonneg_left (add_le_add_right hkl _) h₂.le).trans _,
--   rw [mul_comm (2 : ℝ), ←mul_add, mul_left_comm, inv_mul_cancel h₁.ne'],
--   linarith
-- end

-- lemma nine_one_precise (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
--   ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
--   ∀ γ δ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 10 → δ = γ / 20 →
--   (ramsey_number ![k, l] : ℝ) ≤ exp (- δ * k + 1) * (k + l).choose l :=
-- begin
--   have h₁ : 0 < γ₀⁻¹ - 1 + 2 := by { rw [sub_add], norm_num, positivity },
--   have h₂ : 0 < (γ₀⁻¹ - 1 + 2)⁻¹ := by positivity,
--   have q := (tendsto_nat_ceil_at_top.comp (tendsto_id.at_top_mul_const' h₂)).comp
--     tendsto_coe_nat_at_top_at_top,
--   filter_upwards [top_adjuster (eventually_ge_at_top 2), eventually_gt_at_top 0,
--     eventually_ge_at_top 256, eventually_gt_at_top (⌊γ₀⁻¹ - 1 + 2⌋₊),
--     q.eventually (top_adjuster (nine_two_variant (γ₀ ^ 2) (pow_pos hγ₀ _)))] with
--       l hk₂ hl₀ hk₂₅₆ hlγ₀ hk₉₂
--     k γ δ hγ hγl hγu hδ,
--   let n := ⌈(ramsey_number ![k, l] / exp 1 : ℝ)⌉₊,
--   have hlk := le_of_gamma_le_half hγ hl₀ (hγu.trans (by norm_num1)),
--   have hnr : n < ramsey_number ![k, l],
--   { rw [←@nat.cast_lt ℝ],
--     refine nine_one_part_one _,
--     simp only [nat.one_lt_cast],
--     refine ramsey_number_ge_min _ _,
--     simp only [fin.forall_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons],
--     exact ⟨hk₂ _ hlk, hk₂ _ le_rfl⟩ },
--   rw [←not_le, ramsey_number_le_iff_fin, is_ramsey_valid, not_forall] at hnr,
--   obtain ⟨χ : top_edge_labelling (fin n) (fin 2), hχ⟩ := hnr,
--   suffices : (n : ℝ) ≤ exp (- δ * k) * (k + l).choose l,
--   { rw [add_comm, real.exp_add, mul_assoc, ←div_le_iff' (exp_pos _)],
--     exact this.trans' (nat.le_ceil _) },
--   by_contra' hm,
--   classical,
--   have : (univ.filter (is_good_clique (1 / 16) k l χ)).nonempty :=
--     ⟨∅, by simp only [mem_filter, empty_is_good, mem_univ, true_and]⟩,
--   obtain ⟨x, hx, hxy⟩ := exists_maximal _ this,
--   simp only [mem_filter, mem_univ, true_and] at hx hxy,
--   have hml := good_clique_bound hχ hx,
--   let U := common_blues χ x,
--   have hkl := small_k hγ₀ hγl hγ (hl₀.trans_le hlk),
--   have : 256 ≤ U.card,
--   { refine (hk₂₅₆.trans hlk).trans _,
--     rw ←@nat.cast_le ℝ,
--     refine hx.2.trans' _,
--     refine U_lower_bound_ratio_lower_bound' hml (hl₀.trans_le hlk) hlk hγ hδ hm.le _,
--     rw mul_comm,
--     refine hkl.trans_lt _,
--     refine mul_lt_mul_of_pos_left _ (nat.cast_pos.2 hl₀),
--     rwa [lt_sub_iff_add_lt, ←nat.floor_lt' hl₀.ne'] },
--   let m := x.card,
--   let γ' : ℝ := (l - m) / (k + l - m),
--   cases lt_or_le γ' ((l / (k + l)) ^ 2) with hγ' hγ',
--   { exact nine_one_part_two hχ hml hl₀ hlk hγ hδ hm.le hx hγ' },
--   have hγ'γ : γ' ≤ γ := (gamma'_le_gamma (hl₀.trans_le hlk) hml.le).trans_eq hγ.symm,
--   have hlm : ⌈(l : ℝ) * (γ₀⁻¹ - 1 + 2)⁻¹⌉₊ ≤ l - m,
--   { rw [←not_lt, gamma'_le_gamma_iff hml.le (hl₀.trans_le hlk), not_lt] at hγ',
--     exact l_minus_m_big _ hγ₀ hml.le hl₀ hkl h₁ h₂ hγ' },
--   have hγ'_eq : γ' = ↑(l - m) / (↑k + ↑(l - m)),
--   { rw [nat.cast_sub hml.le, add_sub_assoc'] },
--   have hγ'₀ : 0 ≤ γ',
--   { rw hγ'_eq,
--     positivity },
--   have := maximally_good_clique (by norm_num1) hχ (big_U this) (this.trans' (by norm_num1)) hx hxy,
--   rw [one_add_mul, mul_comm (1 / 15 : ℝ), mul_one_div, ←sub_sub] at this,
--   specialize hk₉₂ (l - m) hlm k γ' (γ' / 20) (γ' / 15) hγ'_eq (hγ'.trans' (pow_le_pow_of_le_left
--     hγ₀.le (hγl.trans_eq hγ) _)) (hγ'γ.trans hγu) rfl (div_nonneg hγ'₀ (by norm_num1)) le_rfl _ _ _
--     _ this,
--   replace hk₉₂ := λ z, nine_one_end hχ hx (ramsey_number_le_finset_aux _ (hk₉₂ z)),
--   rw [imp_false, not_le, fintype.subtype_card, filter_mem_eq_inter, univ_inter] at hk₉₂,
--   replace hk₉₂ := hx.2.trans hk₉₂.le,
--   replace hk₉₂ := (mul_lt_mul_of_pos_right hm (U_lower_bound_ratio_pos (by norm_num1)
--     hml.le)).trans_le hk₉₂,
--   exact nine_one_part_three hχ hml (hl₀.trans_le hlk) hγ hδ rfl hk₉₂,
-- end

-- lemma nine_one_o_filter (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
--   ∃ f : ℕ → ℝ, f =o[at_top] (λ i, (i : ℝ)) ∧
--   ∀ᶠ l : ℕ in at_top, ∀ k : ℕ,
--   ∀ γ δ : ℝ, γ = l / (k + l) → γ₀ ≤ γ → γ ≤ 1 / 10 → δ = γ / 20 →
--   (ramsey_number ![k, l] : ℝ) ≤ exp (- δ * k + f k) * (k + l).choose l :=
-- begin
--   refine ⟨λ i, 1, _, nine_one_precise _ hγ₀⟩,
--   exact is_o.comp_tendsto (is_o_const_id_at_top _) tendsto_coe_nat_at_top_at_top,
-- end

-- lemma nine_one_nine : ∀ᶠ l in at_top, ∀ k, k = 9 * l →
--   (ramsey_number ![k, l] : ℝ) ≤ exp (- l / 25) * (k + l).choose l :=
-- begin
--   filter_upwards [nine_one_precise (1 / 10) (by norm_num1), eventually_ge_at_top 200] with l hl hl'
--     k hk,
--   subst hk,
--   refine (hl (9 * l) (1 / 10) (1 / 10 / 20) _ le_rfl le_rfl rfl).trans _,
--   { rw [nat.cast_mul, ←add_one_mul, mul_comm, ←div_div, div_self],
--     { norm_num1 },
--     { positivity } },
--   refine mul_le_mul_of_nonneg_right (exp_le_exp.2 _) (nat.cast_nonneg _),
--   have : (200 : ℝ) ≤ l := by exact_mod_cast hl',
--   rw [nat.cast_mul],
--   norm_num1,
--   linarith
-- end

-- end simple_graph
