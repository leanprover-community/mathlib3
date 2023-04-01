/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import measure_theory.function.lp_space
import measure_theory.integral.set_integral
import order.upper_lower.locally_finite

/-!
# Bergelson's intersectivity lemma

This file proves the Bergelson intersectivity lemma.

## References

[Bergelson, *Sets of recurrence of `ℤᵐ`-actions and properties of sets of differences in `ℤᵐ`][bergelson1985]

## TODO

Restate the theorem using the upper density of a set of naturals, once we have it.

Use the ergodic theorem to deduce the refinement of the Poincaré recurrence theorem proved by
Bergelson.
-/

attribute [measurability] measurable_one

section
open filter function measure_theory set
open_locale ennreal
variables {α : Type*} [measurable_space α] {μ : measure α} {s N : set α} {f : α → ℝ} {r : ℝ}

attribute [simp] integrable_const

@[simp] lemma integral_indicator_one (hs : measurable_set s) :
  ∫ a, s.indicator 1 a ∂μ = (μ s).to_real :=
(integral_indicator_const 1 hs).trans $ mul_one _

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_set_integral_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ⊤) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | f x ≤ ∫ a in s, f a ∂μ / (μ s).to_real} :=
begin
  obtain ⟨t, hts, ht, hμts⟩ := hs.exists_measurable_subset_ae_eq,
  replace hf := hf.mono_set hts,
  simp_rw [←set_of_inter_eq_sep, ←set_integral_congr_set_ae hμts, ←measure_congr hμts,
    ←measure_congr ((eventually_eq.refl _ _).inter hμts)],
  rw ←measure_congr hμts at hμ hμ₁,
  haveI : fact (μ t < ⊤) := ⟨lt_top_iff_ne_top.2 hμ₁⟩,
  refine pos_iff_ne_zero.2 (λ H, _),
  have : 0 < μ (support (f - const _ (∫ a in t, f a ∂μ / (μ t).to_real)) ∩ t),
  { rwa [pos_iff_ne_zero, inter_comm, ←diff_compl, ←diff_inter_self_eq_diff, measure_diff_null],
    exact eq_bot_mono (measure_mono $ inter_subset_inter_left _ $ λ a ha,
      (sub_eq_zero.1 $ of_not_not ha).le) H },
  rw [←set_integral_pos_iff_support_of_nonneg_ae _ (hf.sub $ integrable_const _)] at this,
  replace hμ := (ennreal.to_real_pos hμ hμ₁).ne',
  simpa [hμ, integral_sub hf, integrable_const, set_integral_const, smul_eq_mul, mul_div_cancel']
    using this,
  change _ = _,
  simp only [compl_set_of, ht, pi.zero_apply, pi.sub_apply, sub_nonneg, not_le,
    measure.restrict_apply'],
  refine eq_bot_mono (measure_mono $ inter_subset_inter_left _ $ λ a ha, _) H,
  dsimp at ha,
  exact ha.le,
end

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_set_integral_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ⊤) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | ∫ a in s, f a ∂μ / (μ s).to_real ≤ f x} :=
by simpa [integral_neg, neg_div] using measure_le_set_integral_pos hμ hμ₁ hf.neg hs

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_set_le_integral (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ⊤) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, f x ≤ ∫ a in s, f a ∂μ / (μ s).to_real :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_integral_pos hμ hμ₁ hf hs).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_set_integral_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ⊤) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, ∫ a in s, f a ∂μ / (μ s).to_real ≤ f x :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_integral_le_pos hμ hμ₁ hf hs).ne'
  in ⟨x, hx, h⟩

variables [is_finite_measure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_integral_pos (hμ : μ ≠ 0) (hf : integrable f μ) :
  0 < μ {x | f x ≤ ∫ a, f a ∂μ / (μ univ).to_real} :=
by simpa using measure_le_set_integral_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.integrable_on null_measurable_set_univ

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_integral_le_pos (hμ : μ ≠ 0) (hf : integrable f μ) :
  0 < μ {x | ∫ a, f a ∂μ / (μ univ).to_real ≤ f x} :=
by simpa using measure_set_integral_le_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.integrable_on null_measurable_set_univ

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_le_integral (hμ : μ ≠ 0) (hf : integrable f μ) :
  ∃ x, f x ≤ ∫ a, f a ∂μ / (μ univ).to_real :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_integral_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_integral_le (hμ : μ ≠ 0) (hf : integrable f μ) :
  ∃ x, ∫ a, f a ∂μ / (μ univ).to_real ≤ f x :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_integral_le_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The minimum of an integrable function is smaller than its mean, while
avoiding a null set. -/
lemma exists_not_mem_le_integral (hμ : μ ≠ 0) (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, f x ≤ ∫ a, f a ∂μ / (μ univ).to_real :=
begin
  have := measure_le_integral_pos hμ hf,
  rw ←measure_diff_null hN at this,
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne',
  exact ⟨x, hxN, hx⟩,
end

/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
lemma exists_not_mem_integral_le (hμ : μ ≠ 0) (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, ∫ a, f a ∂μ / (μ univ).to_real ≤ f x :=
by simpa [integral_neg, neg_div] using exists_not_mem_le_integral hμ hf.neg hN

end

section
open ennreal filter function measure_theory set
open_locale ennreal
variables {α : Type*} [measurable_space α] {μ : measure α} {s N : set α} {f : α → ℝ≥0∞} {r : ℝ≥0∞}

@[simp] lemma lintegral_indicator_one (hs : measurable_set s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
(lintegral_indicator_const hs _).trans $ one_mul _

lemma set_lintegral_eq_top_of_measure_eq_top_pos (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) (hμf : 0 < μ {x ∈ s | f x = ⊤}) :
  ∫⁻ x in s, f x ∂μ = ⊤ :=
lintegral_eq_top_of_measure_eq_top_pos hf $
  by rwa [measure.restrict_apply₀' hs, set_of_inter_eq_sep]

--TODO: Rename `measure_theory.ae_lt_top'`

lemma measure_lintegral_eq_top (hf : ae_measurable f μ) (hμf : ∫⁻ x, f x ∂μ ≠ ⊤) :
  μ {x | f x = ⊤} = 0 :=
of_not_not $ λ h, hμf $ lintegral_eq_top_of_measure_eq_top_pos hf $ pos_iff_ne_zero.2 h

lemma measure_set_lintegral_eq_top (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) (hμf : ∫⁻ x in s, f x ∂μ ≠ ⊤) : μ {x ∈ s | f x = ⊤} = 0 :=
of_not_not $ λ h, hμf $ set_lintegral_eq_top_of_measure_eq_top_pos hf hs $ pos_iff_ne_zero.2 h

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_set_lintegral_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ⊤)
  (hf : ae_measurable f (μ.restrict s)) (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | f x ≤ ∫⁻ a in s, f a ∂μ / μ s} :=
begin
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ⊤,
  { simpa [h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ },
  have := measure_le_set_integral_pos hμ hμ₁ (integrable_to_real_of_lintegral_ne_top hf h) hs,
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs],
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs,
    ←measure_diff_null (measure_lintegral_eq_top hf h)] at this,
  refine this.trans_le (measure_mono _),
  rintro x ⟨hfx, hx⟩,
  dsimp at hfx,
  rwa [integral_to_real hf, ←to_real_div, to_real_le_to_real hx (div_eq_top.not.2 $ λ H, H.elim
    (λ H, hμ H.2) $ λ H, h H.1)] at hfx,
  simp_rw [ae_iff, lt_top_iff_ne_top, not_ne_iff],
  exact measure_lintegral_eq_top hf h,
end

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
lemma measure_set_lintegral_le_pos (hμ : μ s ≠ 0) (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) (hint : ∫⁻ a in s, f a ∂μ ≠ ⊤) :
  0 < μ {x ∈ s | ∫⁻ a in s, f a ∂μ / μ s ≤ f x} :=
begin
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ⊤,
  { simp [hμ₁] },
  have := measure_set_integral_le_pos hμ hμ₁ (integrable_to_real_of_lintegral_ne_top hf hint) hs,
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs],
  rw [←set_of_inter_eq_sep, ←measure.restrict_apply₀' hs,
    ←measure_diff_null (measure_lintegral_eq_top hf hint)] at this,
  refine this.trans_le (measure_mono _),
  rintro x ⟨hfx, hx⟩,
  dsimp at hfx,
  rwa [integral_to_real hf, ←to_real_div, to_real_le_to_real (div_eq_top.not.2 $ λ H, H.elim
    (λ H, hμ H.2) $ λ H, hint H.1) hx] at hfx,
  simp_rw [ae_iff, lt_top_iff_ne_top, not_ne_iff],
  exact measure_lintegral_eq_top hf hint,
end

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
lemma exists_set_le_lintegral (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ⊤) (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, f x ≤ ∫⁻ a in s, f a ∂μ / μ s :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_lintegral_pos hμ hμ₁ hf hs).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
lemma exists_set_lintegral_le (hμ : μ s ≠ 0) (hf : ae_measurable f (μ.restrict s))
  (hs : null_measurable_set s μ) (hint : ∫⁻ a in s, f a ∂μ ≠ ⊤) :
  ∃ x ∈ s, ∫⁻ a in s, f a ∂μ / μ s ≤ f x :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_lintegral_le_pos hμ hf hs hint).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
lemma measure_lintegral_le_pos (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ⊤) :
  0 < μ {x | ∫⁻ a, f a ∂μ / μ univ ≤ f x} :=
by simpa [hint] using measure_set_lintegral_le_pos (measure.measure_univ_ne_zero.2 hμ) hf.restrict
  null_measurable_set_univ

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
lemma exists_lintegral_le (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hint : ∫⁻ a, f a ∂μ ≠ ⊤) :
  ∃ x, ∫⁻ a, f a ∂μ / μ univ ≤ f x :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_lintegral_le_pos hμ hf hint).ne' in ⟨x, hx⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean, while
avoiding a null set. -/
lemma exists_not_mem_lintegral_le (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hN : μ N = 0)
  (hint : ∫⁻ a, f a ∂μ ≠ ⊤) :
  ∃ x ∉ N, ∫⁻ a, f a ∂μ / μ univ ≤ f x :=
begin
  have := measure_lintegral_le_pos hμ hf hint,
  rw ←measure_diff_null hN at this,
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne',
  exact ⟨x, hxN, hx⟩,
end

variables [is_finite_measure μ]

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_lintegral_pos (hμ : μ ≠ 0) (hf : ae_measurable f μ) :
  0 < μ {x | f x ≤ ∫⁻ a, f a ∂μ / μ univ} :=
by simpa using measure_le_set_lintegral_pos (measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
  hf.restrict null_measurable_set_univ

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
lemma exists_le_lintegral (hμ : μ ≠ 0) (hf : ae_measurable f μ) :
  ∃ x, f x ≤ ∫⁻ a, f a ∂μ / μ univ :=
let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_lintegral_pos hμ hf).ne' in ⟨x, hx⟩

/-- **First moment method**. The minimum of a measurable function is smaller than its mean, while
avoiding a null set. -/
lemma exists_not_mem_le_lintegral (hμ : μ ≠ 0) (hf : ae_measurable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, f x ≤ ∫⁻ a, f a ∂μ / μ univ :=
begin
  have := measure_le_lintegral_pos hμ hf,
  rw ←measure_diff_null hN at this,
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne',
  exact ⟨x, hxN, hx⟩,
end

end

open filter measure_theory set
open_locale big_operators ennreal nnreal

section
variables {α M : Type*} [measurable_space α] {μ : measure α} [has_one M] {f : α → M} {s : set α}

@[to_additive]
lemma mul_indicator_ae_eq_one : s.mul_indicator f =ᵐ[μ] 1 ↔ μ (s ∩ f.mul_support) = 0 :=
by simpa [eventually_eq, eventually_iff, measure.ae, compl_set_of]

end

variables {α : Type*} [measurable_space α] {μ : measure α} [is_finite_measure μ] {s : ℕ → set α}
  {r : ℝ≥0∞}

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume. -/
lemma bergelson (hs : ∀ n, measurable_set (s n)) (hr₀ : r ≠ 0) (hr : ∀ n, r ≤ μ (s n)) :
  ∃ t : set ℕ, t.infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.finite → 0 < μ (⋂ n ∈ u, s n) :=
begin
  let M : (α → ℝ) → set α := λ f, {x | snorm_ess_sup f μ < ‖f x‖₊},
  let N : set α := ⋃ u : finset ℕ, M (set.indicator (⋂ n ∈ u, s n) 1),
  have hN₀ : μ N = 0 := measure_Union_null (λ u, meas_lt_of_snorm_ess_sup_le le_rfl
    ⟨1, eventually_map.2 $ eventually_of_forall $ _⟩),
  have hN₁ : ∀ u : finset ℕ, ((⋂ n ∈ u, s n) \ N).nonempty → 0 < μ (⋂ n ∈ u, s n),
  { simp_rw pos_iff_ne_zero,
    rintro u ⟨x, hx⟩ hu,
    refine hx.2 (mem_Union.2 ⟨u, (_ : _ < _)⟩),
    rw [indicator_of_mem hx.1, snorm_ess_sup_eq_zero_iff.2],
    simp,
    rwa [_root_.indicator_ae_eq_zero, function.support_one, inter_univ] },
  swap,
  { rintro x,
    rw indicator,
    split_ifs; simp },
  let f : ℕ → α → ℝ≥0∞ := λ n, (↑(n + 1) : ℝ≥0∞)⁻¹ • ∑ k in finset.range (n + 1), (s k).indicator 1,
  have hfapply : ∀ n a, f n a = (↑(n + 1))⁻¹ * ∑ k in finset.range (n + 1), (s k).indicator 1 a,
  { simp only [f, pi.coe_nat, pi.smul_apply, pi.inv_apply, finset.sum_apply, eq_self_iff_true,
    forall_const, implies_true_iff, smul_eq_mul] },
  have hf₀ : 0 ≤ f,
  { exact zero_le _ },
  have hf' : ∀ n, measurable (∑ k in finset.range n, (s k).indicator 1 : α → ℝ≥0∞),
  { exact λ n, (finset.measurable_sum' _ $ λ i _, measurable_one.indicator $ hs i) },
  have hf : ∀ n, measurable (f n),
  { refine λ n, measurable.mul' _
      (finset.measurable_sum' _ $ λ i _, measurable_one.indicator $ hs i),
    exact @measurable_const ℝ≥0∞ _ _ _ (↑(n + 1))⁻¹ },
  have hf₁ : ∀ n, f n ≤ 1,
  { rintro n a,
    rw [hfapply, ←ennreal.div_eq_inv_mul],
    refine (ennreal.div_le_iff_le_mul (or.inl $ nat.cast_ne_zero.2 n.succ_ne_zero) $
      or.inr one_ne_zero).2 _,
    rw [mul_comm, ←nsmul_eq_mul, ←finset.card_range n.succ],
    exact finset.sum_le_card_nsmul _ _ _ (λ _ _, indicator_le (λ _ _, le_rfl) _) },
  have hf₂ : ∀ n, r ≤ ∫⁻ a, f n a ∂μ,
  { rintro n,
    simp_rw hfapply,
    rw [lintegral_const_mul, lintegral_finset_sum],
    simp only [lintegral_indicator_one (hs _)],
    rw ←ennreal.div_eq_inv_mul,
    refine (ennreal.le_div_iff_mul_le (or.inl $ nat.cast_ne_zero.2 n.succ_ne_zero) $ or.inl $
      ennreal.nat_ne_top _).2 _,
    refine le_trans _ (finset.card_nsmul_le_sum _ _ _ $ λ _ _, hr _),
    { simp [mul_comm] },
    { exact λ _ _, measurable_one.indicator (hs _) },
    { exact finset.measurable_sum _ (λ _ _, measurable_one.indicator $ hs _) } },
  have hμ : μ ≠ 0,
  { unfreezingI { rintro rfl },
    exact hr₀ (le_bot_iff.1 $ hr 0) },
  obtain ⟨x, hxN, hx⟩ := exists_not_mem_lintegral_le hμ (measurable_limsup hf).ae_measurable hN₀
    (ne_top_of_le_ne_top (measure_ne_top μ univ) _),
  replace hx := (ennreal.div_le_div_right ((le_limsup_of_le ⟨μ univ, eventually_map.2 _⟩ $ λ b hb,
    _).trans $ limsup_lintegral_le hf (λ n, ae_of_all μ $ hf₁ n) $
    ne_of_eq_of_ne lintegral_one is_finite_measure.measure_univ_lt_top.ne) _).trans hx,
  refine ⟨{n | x ∈ s n}, λ hxs, _, λ u hux hu, _⟩,
  -- This next block proves that a set of strictly positive natural density is infinite, mixed with
  -- the fact that `{n | x ∈ s n}` has strictly positive natural density.
  -- TODO: Separate it out to a lemma once we have a natural density API.
  { refine ((ennreal.div_pos_iff.2 ⟨hr₀, (measure_lt_top _ _).ne⟩).trans_le hx).ne'
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      _ _ $
        λ n, _).limsup_eq,
    exact λ n, (↑(n + 1)) ⁻¹ * hxs.to_finset.card,
    simpa using ennreal.tendsto.mul_const (ennreal.tendsto_inv_nat_nhds_zero.comp $ tendsto_add_at_top_nat 1) (or.inr $ ennreal.nat_ne_top _),
    exact (λ n, hf₀ n x),
    refine mul_le_mul_left' _ _,
    classical,
    simp_rw [finset.sum_apply, indicator_apply, pi.one_apply, finset.sum_boole],
    exact nat.cast_le.2 (finset.card_le_of_subset $ λ m hm, hxs.mem_to_finset.2
      (finset.mem_filter.1 hm).2) },
  { simp_rw ←hu.mem_to_finset,
    exact hN₁ _ ⟨x, mem_Inter₂.2 $ λ n hn, hux $ hu.mem_to_finset.1 hn, hxN⟩ },
  { refine eventually_of_forall (λ n, _),
    rw [←one_mul (μ univ), ←lintegral_const],
    exact lintegral_mono (hf₁ _) },
  { obtain ⟨n, hn⟩ := hb.exists,
    exact (hf₂ _).trans hn },
  { rw ←lintegral_one,
    refine lintegral_mono (λ a, limsup_le_of_le ⟨0, λ R hR, _⟩ $
      eventually_of_forall $ λ n, hf₁ _ _),
    obtain ⟨r', hr'⟩ := (eventually_map.1 hR).exists,
    exact (hf₀ _ _).trans hr' }
end
