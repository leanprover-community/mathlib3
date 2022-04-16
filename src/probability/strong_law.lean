import probability.martingale
import probability.independence
import probability.integration
import measure_theory.function.l2_space

open measure_theory filter finset

noncomputable theory

open_locale topological_space big_operators measure_theory probability_theory ennreal nnreal

/-- The Cesaro average of a converging sequence converges to the same limit. -/
lemma filter.tendsto.cesaro_smul {E : Type*} [normed_group E] [normed_space ℝ E]
  {u : ℕ → E} {l : E} (h : tendsto u at_top (𝓝 l)) :
  tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) • (∑ i in range n, u i)) at_top (𝓝 l) :=
begin
  refine metric.tendsto_nhds.2 (λ ε εpos, _),
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (b : ℕ), N ≤ b → dist (u b) l < ε / 2,
    by simpa only [eventually_at_top] using metric.tendsto_nhds.1 h (ε / 2) (half_pos εpos),
  have L : ∀ᶠ (n : ℕ) in at_top, ∥∑ i in range N, (u i - l)∥ < n * (ε / 2),
  { have : tendsto (λ (n : ℕ), (n : ℝ) * (ε / 2)) at_top at_top,
      by apply tendsto_coe_nat_at_top_at_top.at_top_mul (half_pos εpos) tendsto_const_nhds,
    filter_upwards [tendsto_at_top.1 this (∥∑ i in range N, (u i - l)∥ + 1)] with n hn,
    exact (lt_add_one _).trans_le hn },
  filter_upwards [Ici_mem_at_top N, Ioi_mem_at_top 0, L] with n Nn npos hnL,
  have nposℝ : (0 : ℝ) < n := nat.cast_pos.2 npos,
  suffices : ∥(range n).sum u - n • l∥ < ε * n,
  { have A : l = (n ⁻¹ : ℝ) • ((n : ℝ) • l), by rw [smul_smul, inv_mul_cancel nposℝ.ne', one_smul],
    rwa [dist_eq_norm, A, ← smul_sub, norm_smul, norm_inv, real.norm_coe_nat, ← div_eq_inv_mul,
      div_lt_iff nposℝ, ← nsmul_eq_smul_cast] },
  calc ∥(range n).sum u - n • l∥ = ∥∑ i in range n, (u i - l)∥ :
    by simp only [sum_sub_distrib, sum_const, card_range]
  ... = ∥∑ i in range N, (u i - l) + ∑ i in Ico N n, (u i - l)∥ :
    by rw sum_range_add_sum_Ico _ Nn
  ... ≤ ∥∑ i in range N, (u i - l)∥ + ∥∑ i in Ico N n, (u i - l)∥ :
    norm_add_le _ _
  ... ≤ ∥∑ i in range N, (u i - l)∥ + ∑ i in Ico N n, ε / 2 :
    begin
      refine add_le_add le_rfl (norm_sum_le_of_le _ (λ i hi, _)),
      rw ← dist_eq_norm,
      exact (hN _ (mem_Ico.1 hi).1).le,
    end
  ... ≤ ∥∑ i in range N, (u i - l)∥ + n * (ε / 2) :
    begin
      refine add_le_add le_rfl _,
      simp only [sum_const, nat.card_Ico, nsmul_eq_mul],
      apply mul_le_mul _ le_rfl (half_pos εpos).le nposℝ.le,
      simp only [nat.cast_le, tsub_le_self]
    end
  ... < n * (ε / 2) + n * (ε / 2) : (add_lt_add_iff_right _).2 hnL
  ... = ε * n : by ring
end

lemma filter.tendsto.cesaro
  {u : ℕ → ℝ} {l : ℝ} (h : tendsto u at_top (𝓝 l)) :
  tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, u i)) at_top (𝓝 l) :=
h.cesaro_smul

namespace probability_theory

def variance {Ω : Type*} {m : measurable_space Ω} (f : Ω → ℝ) (μ : measure Ω) :=
μ[(f - (λ x, μ[f])) ^ 2]

@[simp] lemma variance_zero {Ω : Type*} {m : measurable_space Ω} (μ : measure Ω) :
  variance 0 μ = 0 :=
by simp [variance]

lemma variance_nonneg {Ω : Type*} {m : measurable_space Ω} (f : Ω → ℝ) (μ : measure Ω) :
  0 ≤ variance f μ :=
integral_nonneg (λ x, sq_nonneg _)

localized "notation `Var[` X `]` := probability_theory.variance X volume" in probability_theory
localized "notation `ℙ` := volume" in probability_theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

lemma variance_def' {X : Ω → ℝ} (hX : mem_ℒp X 2) :
  Var[X] = 𝔼[X^2] - 𝔼[X]^2 :=
begin
  rw [variance, sub_sq', integral_sub', integral_add'], rotate,
  { exact hX.integrable_sq },
  { convert integrable_const (𝔼[X] ^ 2),
    apply_instance },
  { apply hX.integrable_sq.add,
    convert integrable_const (𝔼[X] ^ 2),
    apply_instance },
  { apply integrable.mul_const',
    apply integrable.const_mul _ 2,
    exact hX.integrable ennreal.one_le_two },
  simp only [integral_mul_right, pi.pow_apply, pi.mul_apply, pi.bit0_apply, pi.one_apply,
    integral_const (integral ℙ X ^ 2), integral_mul_left (2 : ℝ), one_mul,
    variance, pi.pow_apply, measure_univ, ennreal.one_to_real, algebra.id.smul_eq_mul],
  ring,
end

lemma variance_le_expectation_sq {X : Ω → ℝ} :
  Var[X] ≤ 𝔼[X^2] :=
begin
  by_cases h_int : integrable X, swap,
  { simp only [variance, integral_undef h_int, pi.pow_apply, pi.sub_apply, sub_zero] },
  by_cases hX : mem_ℒp X 2,
  { rw variance_def' hX,
    simp only [sq_nonneg, sub_le_self_iff] },
  { rw [variance, integral_undef],
    { apply integral_nonneg,
      assume a,
      exact sq_nonneg _ },
    { assume h,
      have A : mem_ℒp (X - λ (x : Ω), 𝔼[X]) 2 ℙ := (mem_ℒp_two_iff_integrable_sq
        (h_int.ae_strongly_measurable.sub ae_strongly_measurable_const)).2 h,
      have B : mem_ℒp (λ (x : Ω), 𝔼[X]) 2 ℙ := mem_ℒp_const _,
      apply hX,
      convert A.add B,
      simp } }
end

theorem meas_ge_le_mul_variance {X : Ω → ℝ} (hX : mem_ℒp X 2) {c : ℝ} (hc : 0 < c) :
  ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2) :=
begin
  have A : (ennreal.of_real c : ℝ≥0∞) ≠ 0,
    by simp only [hc, ne.def, ennreal.of_real_eq_zero, not_le],
  have B : ae_strongly_measurable (λ (ω : Ω), 𝔼[X]) ℙ := ae_strongly_measurable_const,
  convert meas_ge_le_mul_pow_snorm ℙ ennreal.two_ne_zero ennreal.two_ne_top
    (hX.ae_strongly_measurable.sub B) A,
  { ext ω,
    set d : ℝ≥0 := ⟨c, hc.le⟩ with hd,
    have cd : c = d, by simp only [subtype.coe_mk],
    simp only [pi.sub_apply, ennreal.coe_le_coe, ← real.norm_eq_abs, ← coe_nnnorm,
      nnreal.coe_le_coe, cd, ennreal.of_real_coe_nnreal] },
  { rw (hX.sub (mem_ℒp_const _)).snorm_eq_rpow_integral_rpow_norm
      ennreal.two_ne_zero ennreal.two_ne_top,
    simp only [pi.sub_apply, ennreal.to_real_bit0, ennreal.one_to_real],
    rw ennreal.of_real_rpow_of_nonneg _ zero_le_two, rotate,
    { apply real.rpow_nonneg_of_nonneg,
      apply integral_nonneg (λ x, _),
      apply real.rpow_nonneg_of_nonneg (norm_nonneg _) },
    rw [variance, ← real.rpow_mul, inv_mul_cancel], rotate,
    { exact two_ne_zero },
    { apply integral_nonneg (λ x, _),
      apply real.rpow_nonneg_of_nonneg (norm_nonneg _) },
    simp only [pi.pow_apply, pi.sub_apply, real.rpow_two, real.rpow_one, real.norm_eq_abs,
      pow_bit0_abs, ennreal.of_real_inv_of_pos hc, ennreal.rpow_two],
    rw [← ennreal.of_real_pow (inv_nonneg.2 hc.le), ← ennreal.of_real_mul (sq_nonneg _),
      div_eq_inv_mul, inv_pow₀] }
end

theorem indep_fun.Var_add {X Y : Ω → ℝ} (hX : mem_ℒp X 2) (hY : mem_ℒp Y 2) (h : indep_fun X Y) :
  Var[X + Y] = Var[X] + Var[Y] :=
calc
Var[X + Y] = 𝔼[λ a, (X a)^2 + (Y a)^2 + 2 * X a * Y a] - 𝔼[X+Y]^2 :
  by simp [variance_def' (hX.add hY), add_sq']
... = (𝔼[X^2] + 𝔼[Y^2] + 2 * 𝔼[X * Y]) - (𝔼[X] + 𝔼[Y])^2 :
begin
  simp only [pi.add_apply, pi.pow_apply, pi.mul_apply, mul_assoc],
  rw [integral_add, integral_add, integral_add, integral_mul_left],
  { exact hX.integrable ennreal.one_le_two },
  { exact hY.integrable ennreal.one_le_two },
  { exact hX.integrable_sq },
  { exact hY.integrable_sq },
  { exact hX.integrable_sq.add hY.integrable_sq },
  { apply integrable.const_mul,
    exact h.integrable_mul (hX.integrable ennreal.one_le_two) (hY.integrable ennreal.one_le_two) }
end
... = (𝔼[X^2] + 𝔼[Y^2] + 2 * (𝔼[X] * 𝔼[Y])) - (𝔼[X] + 𝔼[Y])^2 :
begin
  congr,
  exact h.integral_mul_of_integrable
    (hX.integrable ennreal.one_le_two) (hY.integrable ennreal.one_le_two),
end
... = Var[X] + Var[Y] :
  by { simp only [variance_def', hX, hY, pi.pow_apply], ring }

theorem indep_fun.Var_sum {ι : Type*} {X : ι → Ω → ℝ} {s : finset ι}
  (hs : ∀ i ∈ s, mem_ℒp (X i) 2) (h : set.pairwise ↑s (λ i j, indep_fun (X i) (X j))) :
  Var[∑ i in s, X i] = ∑ i in s, Var[X i] :=
begin
  classical,
  induction s using finset.induction_on with k s ks IH,
  { simp only [finset.sum_empty, variance_zero] },
  rw [variance_def' (mem_ℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks],
  simp only [add_sq'],
  calc 𝔼[X k ^ 2 + (∑ i in s, X i) ^ 2 + 2 * X k * ∑ i in s, X i] - 𝔼[X k + ∑ i in s, X i] ^ 2
  = (𝔼[X k ^ 2] + 𝔼[(∑ i in s, X i) ^ 2] + 𝔼[2 * X k * ∑ i in s, X i])
    - (𝔼[X k] + 𝔼[∑ i in s, X i]) ^ 2 :
  begin
    rw [integral_add', integral_add', integral_add'],
    { exact mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_self _ _)) },
    { apply integrable_finset_sum' _ (λ i hi, _),
      exact mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_of_mem hi)) },
    { exact mem_ℒp.integrable_sq (hs _ (mem_insert_self _ _)) },
    { apply mem_ℒp.integrable_sq,
      exact mem_ℒp_finset_sum' _ (λ i hi, (hs _ (mem_insert_of_mem hi))) },
    { apply integrable.add,
      { exact mem_ℒp.integrable_sq (hs _ (mem_insert_self _ _)) },
      { apply mem_ℒp.integrable_sq,
        exact mem_ℒp_finset_sum' _ (λ i hi, (hs _ (mem_insert_of_mem hi))) } },
    { rw mul_assoc,
      apply integrable.const_mul _ 2,
      simp only [mul_sum, sum_apply, pi.mul_apply],
      apply integrable_finset_sum _ (λ i hi, _),
      apply indep_fun.integrable_mul _
        (mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_self _ _)))
        (mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_of_mem hi))),
      apply h (mem_insert_self _ _) (mem_insert_of_mem hi),
      assume hki,
      rw hki at ks,
      exact ks hi }
  end
  ... = Var[X k] + Var[∑ i in s, X i] +
    (𝔼[2 * X k * ∑ i in s, X i] - 2 * 𝔼[X k] * 𝔼[∑ i in s, X i]) :
  begin
    rw [variance_def' (hs _ (mem_insert_self _ _)),
        variance_def' (mem_ℒp_finset_sum' _ (λ i hi, (hs _ (mem_insert_of_mem hi))))],
    ring,
  end
  ... = Var[X k] + Var[∑ i in s, X i] :
  begin
    simp only [mul_assoc, integral_mul_left, pi.mul_apply, pi.bit0_apply, pi.one_apply, sum_apply,
      add_right_eq_self, mul_sum],
    rw integral_finset_sum s (λ i hi, _), swap,
    { apply integrable.const_mul _ 2,
      apply indep_fun.integrable_mul _
        (mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_self _ _)))
        (mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_of_mem hi))),
      apply h (mem_insert_self _ _) (mem_insert_of_mem hi),
      assume hki,
      rw hki at ks,
      exact ks hi },
    rw [integral_finset_sum s
      (λ i hi, (mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_of_mem hi)))),
      mul_sum, mul_sum, ← sum_sub_distrib],
    apply finset.sum_eq_zero (λ i hi, _),
    rw [integral_mul_left, indep_fun.integral_mul_of_integrable', sub_self],
    { apply h (mem_insert_self _ _) (mem_insert_of_mem hi),
      assume hki,
      rw hki at ks,
      exact ks hi },
    { exact mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_self _ _)) },
    { exact mem_ℒp.integrable ennreal.one_le_two (hs _ (mem_insert_of_mem hi)) }
  end
  ... = Var[X k] + ∑ i in s, Var[X i] :
    by rw IH (λ i hi, hs i (mem_insert_of_mem hi))
      (h.mono (by simp only [coe_insert, set.subset_insert]))
end

open set (indicator)

section truncation

variables {α : Type*}

def truncation {α : Type*} (f : α → ℝ) (A : ℝ) :=
(indicator (set.Ioc (-A) A) id) ∘ f

variables {m : measurable_space α} {μ : measure α} {f : α → ℝ}

lemma _root_.measure_theory.ae_strongly_measurable.truncation
  (hf : ae_strongly_measurable f μ) {A : ℝ} :
  ae_strongly_measurable (truncation f A) μ :=
begin
  apply ae_strongly_measurable.comp_ae_measurable _ hf.ae_measurable,
  exact (strongly_measurable_id.indicator measurable_set_Ioc).ae_strongly_measurable,
end

lemma neg_abs_le_neg (a : ℝ) : -|a| ≤ -a :=
by simp [le_abs_self]

lemma abs_truncation_le_bound (f : α → ℝ) (A : ℝ) (x : α) :
  abs (truncation f A x) ≤ |A| :=
begin
  simp only [truncation, set.indicator, set.mem_Icc, id.def, function.comp_app],
  split_ifs,
  { simp only [real.norm_eq_abs, abs_le],
    split,
    { linarith [neg_abs_le_neg A, h.1] },
    { linarith [le_abs_self A, h.2] } },
  { simp [abs_nonneg] }
end

lemma abs_truncation_le_abs_self (f : α → ℝ) (A : ℝ) (x : α) :
  |truncation f A x| ≤ |f x| :=
begin
  simp only [truncation, indicator, set.mem_Icc, id.def, function.comp_app],
  split_ifs,
  { exact le_rfl },
  { simp [abs_nonneg] },
end

lemma truncation_eq_self {f : α → ℝ} {A : ℝ} {x : α} (h : |f x| < A) :
  truncation f A x = f x :=
begin
  simp only [truncation, indicator, set.mem_Icc, id.def, function.comp_app, ite_eq_left_iff,
    not_le],
  assume H,
  apply H.elim,
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le],
end

lemma _root_.measure_theory.ae_strongly_measurable.mem_ℒp_truncation [is_finite_measure μ]
  (hf : ae_strongly_measurable f μ) {A : ℝ} {p : ℝ≥0∞} :
  mem_ℒp (truncation f A) p μ :=
begin
  refine mem_ℒp.mem_ℒp_of_exponent_le _ le_top,
  apply mem_ℒp_top_of_bound hf.truncation _
    (eventually_of_forall (λ x, abs_truncation_le_bound _ _ _)),
end

/-- If a function is integrable, then the integral of its truncated versions converges to the
integral of the whole function. -/
lemma tendsto_integral_truncation {f : α → ℝ} (hf : integrable f μ) :
  tendsto (λ A, ∫ x, truncation f A x ∂μ) at_top (𝓝 (∫ x, f x ∂μ)) :=
begin
  refine tendsto_integral_filter_of_dominated_convergence (λ x, abs (f x)) _ _ _ _,
  { exact eventually_of_forall (λ A, hf.ae_strongly_measurable.truncation) },
  { apply eventually_of_forall (λ A, _),
    apply eventually_of_forall (λ x, _),
    rw real.norm_eq_abs,
    exact abs_truncation_le_abs_self _ _ _ },
  { apply hf.abs },
  { apply eventually_of_forall (λ x, _),
    apply tendsto_const_nhds.congr' _,
    filter_upwards [Ioi_mem_at_top (abs (f x))] with A hA,
    exact (truncation_eq_self hA).symm },
end

end truncation

lemma geom_sum_Ico_le_of_lt_one {a b : ℕ} {c : ℝ} (hc : 0 ≤ c) (h'c : c < 1) :
  ∑ i in Ico a b, c ^ i ≤ c ^ a / (1 - c) :=
begin
  rcases le_or_lt a b with hab | hab, swap,
  { rw [Ico_eq_empty, sum_empty],
    { apply div_nonneg (pow_nonneg hc _),
      simpa using h'c.le },
    { simpa using hab.le } },
  rw geom_sum_Ico' h'c.ne hab,
  apply div_le_div (pow_nonneg hc _) _ (sub_pos.2 h'c) le_rfl,
  simpa using pow_nonneg hc _
end

lemma aux_sum_horrible (N : ℕ) (j : ℝ) (hj : 0 < j) (c : ℝ) (hc : 1 < c) :
  ∑ i in (range N).filter (λ i, j < c ^ i), 1 / (c ^ i) ^ 2 ≤ (c^2 * (1 - c⁻¹ ^ 2) ⁻¹) / j ^ 2 :=
begin
  have A : 0 < (c⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.2 (zero_lt_one.trans hc)),
  calc
  ∑ i in (range N).filter (λ i, j < c ^ i), 1/ (c ^ i) ^ 2
    ≤ ∑ i in Ico (⌊real.log j / real.log c⌋₊) N, 1 / (c ^ i) ^ 2 :
  begin
    refine sum_le_sum_of_subset_of_nonneg _ (λ i hi h'i, div_nonneg zero_le_one (sq_nonneg _)),
    assume i hi,
    simp only [mem_filter, mem_range] at hi,
    simp only [hi.1, mem_Ico, and_true],
    apply nat.floor_le_of_le,
    apply le_of_lt,
    rw [div_lt_iff (real.log_pos hc), ← real.log_pow],
    exact real.log_lt_log hj hi.2
  end
  ... = ∑ i in Ico (⌊real.log j / real.log c⌋₊) N, ((c⁻¹) ^ 2) ^ i :
  begin
    congr' 1 with i,
    simp [← pow_mul, mul_comm],
  end
  ... ≤ ((c⁻¹) ^ 2) ^ (⌊real.log j / real.log c⌋₊) / (1 - (c⁻¹) ^ 2) :
  begin
    apply geom_sum_Ico_le_of_lt_one (sq_nonneg _),
    rw sq_lt_one_iff (inv_nonneg.2 (zero_le_one.trans hc.le)),
    exact inv_lt_one hc
  end
  ... ≤ ((c⁻¹) ^ 2) ^ (real.log j / real.log c - 1) / (1 - (c⁻¹) ^ 2) :
  begin
    apply div_le_div _ _ _ le_rfl,
    { apply real.rpow_nonneg_of_nonneg (sq_nonneg _) },
    { rw ← real.rpow_nat_cast,
      apply real.rpow_le_rpow_of_exponent_ge A,
      { exact pow_le_one _ (inv_nonneg.2 (zero_le_one.trans hc.le)) (inv_le_one hc.le) },
      { exact (nat.sub_one_lt_floor _).le } },
    { simpa only [inv_pow₀, sub_pos] using inv_lt_one (one_lt_pow hc two_ne_zero) }
  end
  ... = (c^2 * (1 - c⁻¹ ^ 2) ⁻¹) / j ^ 2 :
  begin
    have I : (c ⁻¹ ^ 2) ^ (real.log j / real.log c) = 1 / j ^ 2,
    { apply real.log_inj_on_pos (real.rpow_pos_of_pos A _),
      { rw [one_div], exact inv_pos.2 (sq_pos_of_pos hj) },
      rw real.log_rpow A,
      simp only [one_div, real.log_inv, real.log_pow, nat.cast_bit0, nat.cast_one, mul_neg,
        neg_inj],
      field_simp [(real.log_pos hc).ne'],
      ring },
    rw [real.rpow_sub A, I],
    have : c^2 - 1 ≠ 0 := (sub_pos.2 (one_lt_pow hc two_ne_zero)).ne',
    field_simp [hj.ne', (zero_lt_one.trans hc).ne'],
    ring,
  end
end

lemma glouk (N : ℕ) (j : ℝ) (hj : 0 < j) (c : ℝ) (hc : 1 < c) :
  ∑ i in (range N).filter (λ i, j < ⌊c ^ i⌋₊), (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2 ≤ 1 / j ^ 2 :=
begin
  have : ∀ (i : ℕ), (1 : ℝ) / ⌊c ^ i⌋₊  ≤ (c/(c-1)) / (c ^ i),
  { assume i,
    rcases nat.eq_zero_or_pos i with rfl|hi,
    { simp only [pow_zero, nat.floor_one, nat.cast_one, div_one],
      rw le_div_iff (sub_pos.2 hc),
      simp only [one_mul, sub_le_self_iff, zero_le_one] },
    rw div_le_div_iff, rotate,
    { refine zero_lt_one.trans_le _,
      simp only [one_le_sq_iff_one_le_abs, nat.abs_cast, nat.one_le_cast],
      apply nat.le_floor,
      rw nat.cast_one,
      apply one_le_pow_of_one_le hc.le },
    { apply pow_pos,
      apply zero_lt_one.trans hc },
    have h'i : 1 ≤ i := hi,
    simp only [← mul_pow, one_mul, div_eq_inv_mul, mul_assoc],
    rw [← div_eq_inv_mul, le_div_iff (sub_pos.2 hc)],
    calc c ^ i * (c - 1) = c ^ (i + 1) - c ^ i : by ring_exp
    ... ≤ c ^ (i + 1) - c : by simpa using pow_le_pow hc.le h'i
    ... = c * (c ^ i - 1) : by ring_exp
    ... ≤ c * ⌊c ^ i⌋₊ :
      (mul_le_mul_left (zero_lt_one.trans hc)).2 (nat.sub_one_lt_floor _).le },
  sorry,
end

#exit

theorem
  strong_law1
  (X : ℕ → Ω → ℝ) (hint : ∀ i, integrable (X i))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (h'i : ∀ i, measure.map (X i) ℙ = measure.map (X 0) ℙ)
  (h''i : ∀ i ω, 0 ≤ X i ω) :
  ∀ᵐ ω, tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, X i ω)) at_top (𝓝 (𝔼[X 0])) :=
begin
  have A : ∀ i, strongly_measurable (indicator (set.Ioc (-i : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Ioc,
  let Y := λ (n : ℕ), truncation (X n) n,
  set S := λ n, ∑ i in range n, Y i with hS,
  have : tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, 𝔼[Y i])) at_top (𝓝 (𝔼[X 0])),
  sorry { apply filter.tendsto.cesaro,
    convert (tendsto_integral_truncation (hint 0)).comp tendsto_coe_nat_at_top_at_top,
    ext i,
    calc 𝔼[Y i] = ∫ x, (indicator (set.Ioc (-i : ℝ) i) id) x ∂(measure.map (X i) ℙ) :
      by { rw integral_map (hint i).ae_measurable (A i).ae_strongly_measurable, refl }
    ... = ∫ x, (indicator (set.Ioc (-i : ℝ) i) id) x ∂(measure.map (X 0) ℙ) : by rw h'i i
    ... = 𝔼[truncation (X 0) i] :
    by { rw integral_map (hint 0).ae_measurable (A i).ae_strongly_measurable, refl } },
  have c : ℝ := sorry,
  have c_one : 1 < c := sorry;
  let u : ℕ → ℕ := λ n, ⌊c ^ n⌋₊,
  have u_mono : monotone u := sorry,
  have ε : ℝ := sorry,
  have εpos : 0 < ε := sorry,
  have : ∀ N, ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)] ≤ 10,
  { assume N,
    calc
    ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)]
        = ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * (∑ j in range (u i), Var[Y j]) :
      begin
        congr' 1 with i,
        congr' 1,
        rw [hS, indep_fun.Var_sum],
        { assume j hj,
          exact (hint j).1.mem_ℒp_truncation },
        { assume k hk l hl hkl,
          exact (hindep k l hkl).comp (A k).measurable (A l).measurable }
      end
    ... ≤ ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * (∑ j in range (u i), 𝔼[Y j ^ 2]) :
      begin
        apply sum_le_sum (λ i hi, _),
        apply mul_le_mul le_rfl, rotate,
        { exact sum_nonneg (λ j hj, variance_nonneg (Y j) _) },
        { exact inv_nonneg.2 (sq_nonneg _) },
        exact sum_le_sum (λ i hi, variance_le_expectation_sq),
      end
    ... = ∑ j in range (u (N - 1)),
            (∑ i in (range N).filter (λ i, j < u i), ((u i : ℝ) ^ 2) ⁻¹) * 𝔼[Y j ^ 2] :
      begin
        simp_rw [mul_sum, sum_mul, sum_sigma'],
        refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
          (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range] at hij,
          simp only [hij.1, hij.2, mem_sigma, mem_range, mem_filter, and_true],
          exact hij.2.trans_le (u_mono (nat.le_pred_of_lt hij.1)) },
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range, mem_filter] at hij,
          simp only [hij.2.1, hij.2.2, mem_sigma, mem_range, and_self] },
        { rintros ⟨i, j⟩ hij, refl },
        { rintros ⟨i, j⟩ hij, refl },
      end

    ... ≤ 10 : sorry

  }
end

#exit
  have : ∀ N, ∑ i in range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} ≤ 10,
  { assume N,
    calc ∑ i in range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|}
    ≤ ∑ i in range N, ennreal.of_real (Var[S (u i)] / (u i * ε) ^ 2) :
    begin
      refine sum_le_sum (λ i hi, _),
      apply meas_ge_le_mul_variance,
      { exact mem_ℒp_finset_sum' _ (λ j hj, (hint j).1.mem_ℒp_truncation) },
      { apply mul_pos (nat.cast_pos.2 _) εpos,
        refine zero_lt_one.trans_le _,
        apply nat.le_floor,
        rw nat.cast_one,
        apply one_le_pow_of_one_le c_one.le }
    end
    ... = ennreal.of_real (∑ i in range N, Var[S (u i)] / (u i * ε) ^ 2) :
    begin
      rw ennreal.of_real_sum_of_nonneg (λ i hi, _),
      exact div_nonneg (variance_nonneg _ _) (sq_nonneg _),
    end
    ... ≤ 10 : sorry

  }
end

end probability_theory
