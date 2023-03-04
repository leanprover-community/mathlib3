/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import measure_theory.function.lp_space
import measure_theory.integral.set_integral

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

namespace set
variables {α : Type*}

lemma inter_diff_distrib_left (s t u : set α) : s ∩ (t \ u) = (s ∩ t) \ (s ∩ u) :=
inf_sdiff_distrib_left _ _ _

lemma inter_diff_distrib_right (s t u : set α) : s \ t ∩ u = (s ∩ u) \ (t ∩ u) :=
inf_sdiff_distrib_right _ _ _

lemma inter_set_of (s : set α) (p : α → Prop) : s ∩ {a | p a} = {a ∈ s | p a} := rfl
lemma set_of_inter (p : α → Prop) (s : set α) : {a | p a} ∩ s = {a ∈ s | p a} := inter_comm _ _

end set

attribute [measurability] measurable_one

section
variables {α β : Type*} [measurable_space α] [measurable_space β]

@[measurability] lemma measurable_nat_cast [has_nat_cast α] (n : ℕ) : measurable (n : β → α) :=
@measurable_const α _ _ _ n

@[measurability] lemma measurable_int_cast [has_int_cast α] (n : ℤ) : measurable (n : β → α) :=
@measurable_const α _ _ _ n

end

namespace pi
variables {ι : Type*} {α : ι → Type*} [Π i, preorder (α i)]

lemma apply_monotone (i : ι) : monotone (λ f : Π i, α i, f i) := λ f g h, h _

end pi

namespace measure_theory
namespace measure
variables {α : Type*} {m0 : measurable_space α} {μ : measure_theory.measure α}

open set

lemma measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 := measure_univ_eq_zero.not

@[simp] lemma measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 := pos_iff_ne_zero.trans measure_univ_ne_zero

end measure
end measure_theory

section
open filter function measure_theory set
open_locale ennreal
variables {α : Type*} [measurable_space α] {μ : measure α} {s N : set α} {f : α → ℝ} {r : ℝ}
  [is_finite_measure μ]

attribute [simp] integrable_const

@[simp] lemma integral_indicator_one (hs : measurable_set s) :
  ∫ a, s.indicator 1 a ∂μ = (μ s).to_real :=
(integral_indicator_const 1 hs).trans $ mul_one _

lemma ae_restrict_iff_subtype' (hs : null_measurable_set s μ) {p : α → Prop} :
  (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ (x : s) ∂μ.comap coe, p x :=
begin
  obtain ⟨t, ht, hst⟩ := hs,
  rw [ae_restrict_congr_set hst, ae_restrict_iff_subtype ht],
  sorry
end

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_set_integral_pos (hμ : μ s ≠ 0) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | f x ≤ ∫ a in s, f a ∂μ / (μ s).to_real} :=
begin
  obtain ⟨t, hts, ht, hμts⟩ := hs.exists_measurable_subset_ae_eq,
  replace hf := hf.mono_set hts,
  simp_rw [←set_of_inter, ←set_integral_congr_set_ae hμts, ←measure_congr hμts,
    ←measure_congr ((eventually_eq.refl _ _).inter hμts)],
  rw ←measure_congr hμts at hμ,
  refine pos_iff_ne_zero.2 (λ H, _),
  have : 0 < μ (support (f - const _ (∫ a in t, f a ∂μ / (μ t).to_real)) ∩ t),
  { rwa [pos_iff_ne_zero, inter_comm, ←diff_compl, ←diff_inter_self_eq_diff, measure_diff_null],
    exact eq_bot_mono (measure_mono $ inter_subset_inter_left _ $ λ a ha,
      (sub_eq_zero.1 $ of_not_not ha).le) H },
  rw [←set_integral_pos_iff_support_of_nonneg_ae _ (hf.sub $ integrable_const _)] at this,
  replace hμ := (ennreal.to_real_pos hμ $ measure_ne_top _ _).ne',
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
lemma measure_set_integral_le_pos (hμ : μ s ≠ 0) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  0 < μ {x ∈ s | ∫ a in s, f a ∂μ / (μ s).to_real ≤ f x} :=
by simpa [integral_neg, neg_div] using measure_le_set_integral_pos hμ hf.neg hs

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
lemma measure_le_integral_pos (hμ : μ ≠ 0) (hf : integrable f μ) :
  0 < μ {x | f x ≤ ∫ a, f a ∂μ / (μ univ).to_real} :=
by simpa using measure_le_set_integral_pos (measure.measure_univ_ne_zero.2 hμ) hf.integrable_on
  null_measurable_set_univ

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
lemma measure_integral_le_pos (hμ : μ ≠ 0) (hf : integrable f μ) :
  0 < μ {x | ∫ a, f a ∂μ / (μ univ).to_real ≤ f x} :=
by simpa using measure_set_integral_le_pos (measure.measure_univ_ne_zero.2 hμ) hf.integrable_on
  null_measurable_set_univ

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_set_le_integral (hμ : μ s ≠ 0) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, f x ≤ ∫ a in s, f a ∂μ / (μ s).to_real :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_set_integral_pos hμ hf hs).ne'
  in ⟨x, hx, h⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_set_integral_le (hμ : μ s ≠ 0) (hf : integrable_on f s μ)
  (hs : null_measurable_set s μ) :
  ∃ x ∈ s, ∫ a in s, f a ∂μ / (μ s).to_real ≤ f x :=
let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_set_integral_le_pos hμ hf hs).ne'
  in ⟨x, hx, h⟩

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
  rw ←ae_eq_empty at hN,
  have hμN : Nᶜ =ᵐ[μ] univ,
  { simpa only [compl_empty] using hN.compl },
  have hN' : null_measurable_set N μ := ⟨∅, measurable_set.empty, hN⟩,
  simpa [measure.restrict_congr_set hμN, measure_congr hμN]
    using exists_set_le_integral _ hf.integrable_on hN'.compl,
  rwa [measure_congr hμN, measure.measure_univ_ne_zero],
end

/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
lemma exists_not_mem_integral_le (hμ : μ ≠ 0) (hf : integrable f μ) (hN : μ N = 0) :
  ∃ x ∉ N, ∫ a, f a ∂μ / (μ univ).to_real ≤ f x :=
by simpa [integral_neg, neg_div] using exists_not_mem_le_integral hμ hf.neg hN

end

section
open filter function measure_theory set
open_locale ennreal
variables {α : Type*} [measurable_space α] {μ : measure α} {s : set α} {f : α → ℝ≥0∞} {r : ℝ≥0∞}

@[simp] lemma lintegral_indicator_one (hs : measurable_set s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
(lintegral_indicator_const hs _).trans $ one_mul _

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_set_le_lintegral (hμ : μ s ≠ 0) (hf : measurable f) (hs : measurable_set s) :
  ∃ x ∈ s, f x ≤ ∫⁻ a in s, f a ∂μ / μ s :=
sorry

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
lemma exists_set_lintegral_le (hμ : μ s ≠ 0) (hf : measurable f) (hs : measurable_set s) :
  ∃ x ∈ s, ∫⁻ a in s, f a ∂μ / μ s ≤ f x :=
sorry

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
lemma exists_le_lintegral [is_finite_measure μ] (hμ : μ ≠ 0) (hf : measurable f) :
  ∃ x, f x ≤ ∫⁻ a, f a ∂μ / μ univ :=
sorry

lemma exists_lintegral_le [is_finite_measure μ] (hf : measurable f) :
  ∃ x, ∫⁻ a, f a ∂μ / μ univ ≤ f x :=
sorry

lemma exists_le_lintegral_of_le [is_finite_measure μ] (hf : measurable f) (hr : ∫⁻ a, f a ∂μ ≤ r) :
  ∃ x, f x ≤ r / μ univ :=
sorry

lemma exists_lintegral_le_of_le [is_finite_measure μ] (hf : measurable f) (hr : r ≤ ∫⁻ a, f a ∂μ) :
  ∃ x, r / μ univ ≤ f x :=
sorry

end

open filter measure_theory set
open_locale big_operators ennreal nnreal

namespace with_top
variables {α : Type*} [preorder α] {s : set (with_top α)}

open_locale classical

lemma Sup_eq [has_Sup α] (hs : ⊤ ∉ s) (hs' : bdd_above (coe ⁻¹' s : set α)) :
  Sup s = ↑(Sup (coe ⁻¹' s) : α) :=
(if_neg hs).trans $ if_pos hs'

lemma Inf_eq [has_Inf α] (hs : ¬ s ⊆ {⊤}) : Inf s = ↑(Inf (coe ⁻¹' s) : α) := if_neg hs

end with_top

namespace function
variables {α β : Type*} [has_zero β] [has_one β] [ne_zero (1 : β)]

@[simp] lemma support_one : support (1 : α → β) = univ := support_const one_ne_zero
@[simp] lemma mul_support_zero : mul_support (0 : α → β) = univ := mul_support_const zero_ne_one

end function

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
  let N : set α := ⋃ u : finset ℕ, M (set.indicator (u.inf s) 1),
  have hN₀ : μ N = 0 := measure_Union_null (λ u, meas_lt_of_snorm_ess_sup_le le_rfl
    ⟨1, eventually_map.2 $ eventually_of_forall $ _⟩),
  have hN₁ : ∀ u : finset ℕ, (u.inf s \ N).nonempty → 0 < μ (u.inf s),
  sorry { simp_rw pos_iff_ne_zero,
    rintro u ⟨x, hx⟩ hu,
    refine hx.2 (mem_Union.2 ⟨u, (_ : _ < _)⟩),
    rw [indicator_of_mem hx.1, snorm_ess_sup_eq_zero_iff.2],
    simp,
    rwa [_root_.indicator_ae_eq_zero, function.support_one, inter_univ] },
  swap,
  sorry { rintro x,
    rw indicator,
    split_ifs; simp },
  let f : ℕ → α → ℝ≥0∞ := λ n, (↑(n + 1) : ℝ≥0∞)⁻¹ • ∑ k in finset.range (n + 1), (s k).indicator 1,
  have hfapply : ∀ n a, f n a = (↑(n + 1))⁻¹ * ∑ k in finset.range (n + 1), (s k).indicator 1 a,
  { simp only [f, pi.coe_nat, pi.smul_apply, pi.inv_apply, finset.sum_apply, eq_self_iff_true,
    forall_const, implies_true_iff, smul_eq_mul] },
  have : 0 ≤ f,
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
  obtain ⟨x, hx⟩ := exists_lintegral_le_of_le (measurable_limsup hf)
    ((le_limsup_of_le ⟨μ univ, eventually_map.2 _⟩ $ λ b hb, _).trans $ limsup_lintegral_le hf
    (λ n, ae_of_all μ $ hf₁ n) $
    ne_of_eq_of_ne lintegral_one is_finite_measure.measure_univ_lt_top.ne),
  refine ⟨{n | x ∈ s n}, λ hxs, _, λ u hux hu, _⟩,
  { refine ((ennreal.div_pos_iff.2 ⟨hr₀, (measure_lt_top _ _).ne⟩).trans_le hx).ne' _,
    dsimp,
    rw limsup_eq,
    sorry },
  { simp_rw [←hu.mem_to_finset, ←finset.inf_set_eq_bInter],
    refine hN₁ _ _,
    sorry },
  { refine eventually_of_forall (λ n, _),
    rw [←one_mul (μ univ), ←lintegral_const],
    exact lintegral_mono (hf₁ _) },
  { obtain ⟨n, hn⟩ := hb.exists,
    exact (hf₂ _).trans hn }
end
