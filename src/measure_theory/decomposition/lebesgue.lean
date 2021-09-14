/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.jordan
import measure_theory.measure.with_density_vector_measure

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a finite measure `ξ` and a measurable function
`f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `measure_theory.measure.have_lebesgue_decomposition` : A pair of measures `μ` and `ν` is said
  to `have_lebesgue_decomposition` if there exists a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f`
* `measure_theory.measure.singular_part` : If a pair of measures `have_lebesgue_decomposition`,
  then `singular_part` chooses the measure from `have_lebesgue_decomposition`, otherwise it
  returns the zero measure.
* `measure_theory.measure.radon_nikodym_deriv` : If a pair of measures
  `have_lebesgue_decomposition`, then `radon_nikodym_deriv` chooses the measurable function from
  `have_lebesgue_decomposition`, otherwise it returns the zero function.

## Main results

* `measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite` :
  the Lebesgue decomposition theorem.
* `measure_theory.measure.eq_singular_part` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = singular_part μ ν`.
* `measure_theory.measure.eq_radon_nikodym_deriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = radon_nikodym_deriv μ ν`.
* `measure_theory.signed_measure.singular_part_add_with_density_radon_nikodym_deriv_eq` :
  tthe Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

# Tags

Lebesgue decomposition theorem
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace measure

/-- A pair of measures `μ` and `ν` is said to `have_lebesgue_decomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.with_density f`. -/
class have_lebesgue_decomposition (μ ν : measure α) : Prop :=
(lebesgue_decomposition :
  ∃ (p : measure α × (α → ℝ≥0∞)), measurable p.2 ∧ p.1 ⊥ₘ ν ∧ μ = p.1 + ν.with_density p.2)

/-- If a pair of measures `have_lebesgue_decomposition`, then `singular_part` chooses the
measure from `have_lebesgue_decomposition`, otherwise it returns the zero measure. -/
@[irreducible]
def singular_part (μ ν : measure α) : measure α :=
if h : have_lebesgue_decomposition μ ν then (classical.some h.lebesgue_decomposition).1 else 0

/-- If a pair of measures `have_lebesgue_decomposition`, then `radon_nikodym_deriv` chooses the
measurable function from `have_lebesgue_decomposition`, otherwise it returns the zero function. -/
@[irreducible]
def radon_nikodym_deriv (μ ν : measure α) : α → ℝ≥0∞ :=
if h : have_lebesgue_decomposition μ ν then (classical.some h.lebesgue_decomposition).2 else 0

lemma have_lebesgue_decomposition_spec (μ ν : measure α) [h : have_lebesgue_decomposition μ ν] :
  measurable (radon_nikodym_deriv μ ν) ∧ (singular_part μ ν) ⊥ₘ ν ∧
  μ = (singular_part μ ν) + ν.with_density (radon_nikodym_deriv μ ν) :=
begin
  rw [singular_part, radon_nikodym_deriv, dif_pos h, dif_pos h],
  exact classical.some_spec h.lebesgue_decomposition,
end

lemma have_lebesgue_decomposition_add (μ ν : measure α) [have_lebesgue_decomposition μ ν] :
  μ = (singular_part μ ν) + ν.with_density (radon_nikodym_deriv μ ν) :=
(have_lebesgue_decomposition_spec μ ν).2.2

@[measurability]
lemma measurable_radon_nikodym_deriv (μ ν : measure α) :
  measurable $ radon_nikodym_deriv μ ν :=
begin
  by_cases h : have_lebesgue_decomposition μ ν,
  { exactI (have_lebesgue_decomposition_spec μ ν).1 },
  { rw [radon_nikodym_deriv, dif_neg h],
    exact measurable_zero }
end

lemma mutually_singular_singular_part (μ ν : measure α) :
  singular_part μ ν ⊥ₘ ν :=
begin
  by_cases h : have_lebesgue_decomposition μ ν,
  { exactI (have_lebesgue_decomposition_spec μ ν).2.1 },
  { rw [singular_part, dif_neg h],
    exact mutually_singular.zero.symm }
end

lemma singular_part_le (μ ν : measure α) : singular_part μ ν ≤ μ :=
begin
  by_cases hl : have_lebesgue_decomposition μ ν,
  { casesI (have_lebesgue_decomposition_spec μ ν).2 with _ h,
    conv_rhs { rw h },
    exact measure.le_add_right (le_refl _) },
  { rw [singular_part, dif_neg hl],
    exact measure.zero_le μ }
end

lemma with_density_radon_nikodym_deriv_le (μ ν : measure α) :
  ν.with_density (radon_nikodym_deriv μ ν) ≤ μ :=
begin
  by_cases hl : have_lebesgue_decomposition μ ν,
  { casesI (have_lebesgue_decomposition_spec μ ν).2 with _ h,
    conv_rhs { rw h },
    exact measure.le_add_left (le_refl _) },
  { rw [radon_nikodym_deriv, dif_neg hl, with_density_zero],
    exact measure.zero_le μ }
end

instance {μ ν : measure α} [is_finite_measure μ] :
  is_finite_measure (singular_part μ ν) :=
is_finite_measure_of_le μ $ singular_part_le μ ν

instance {μ ν : measure α} [sigma_finite μ] :
  sigma_finite (singular_part μ ν) :=
sigma_finite_of_le μ $ singular_part_le μ ν

instance {μ ν : measure α} [is_finite_measure μ] :
  is_finite_measure (ν.with_density $ radon_nikodym_deriv μ ν) :=
is_finite_measure_of_le μ $ with_density_radon_nikodym_deriv_le μ ν

instance {μ ν : measure α} [sigma_finite μ] :
  sigma_finite (ν.with_density $ radon_nikodym_deriv μ ν) :=
sigma_finite_of_le μ $ with_density_radon_nikodym_deriv_le μ ν

lemma lintegral_radon_nikodym_deriv_lt_top
  (μ ν : measure α) [is_finite_measure μ] :
  ∫⁻ x, μ.radon_nikodym_deriv ν x ∂ν < ∞ :=
begin
  by_cases hl : have_lebesgue_decomposition μ ν,
  { haveI := hl,
    obtain ⟨-, -, hadd⟩ := have_lebesgue_decomposition_spec μ ν,
    rw [← set_lintegral_univ, ← with_density_apply _ measurable_set.univ],
    refine lt_of_le_of_lt
      (le_add_left (le_refl _) : _ ≤ μ.singular_part ν set.univ +
        ν.with_density (μ.radon_nikodym_deriv ν) set.univ) _,
    rw [← measure.add_apply, ← hadd],
    exact measure_lt_top _ _ },
  { erw [measure.radon_nikodym_deriv, dif_neg hl, lintegral_zero],
    exact with_top.zero_lt_top },
end

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = singular_part μ ν`.

This theorem provides the uniqueness of the `singular_part` in the Lebesgue decomposition theorem,
while `measure_theory.measure.eq_radon_nikodym_deriv` provides the uniqueness of the
`radon_nikodym_deriv`. -/
theorem eq_singular_part
  {μ ν : measure α} {s : measure α} {f : α → ℝ≥0∞} (hf : measurable f)
  (hs : s ⊥ₘ ν) (hadd : μ = s + ν.with_density f) :
  s = μ.singular_part ν :=
begin
  haveI : have_lebesgue_decomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩,
  obtain ⟨hmeas, hsing, hadd'⟩ := have_lebesgue_decomposition_spec μ ν,
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := ⟨hs, hsing⟩,
  rw hadd' at hadd,
  have hνinter : ν (S ∩ T)ᶜ = 0,
  { rw set.compl_inter,
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _),
    rw [hT₃, hS₃, add_zero],
    exact le_refl _ },
  have heq : s.restrict (S ∩ T)ᶜ = (μ.singular_part ν).restrict (S ∩ T)ᶜ,
  { ext1 A hA,
    have hf : ν.with_density f (A ∩ (S ∩ T)ᶜ) = 0,
    { refine with_density_absolutely_continuous ν _ _,
      rw ← nonpos_iff_eq_zero,
      exact hνinter ▸ measure_mono (set.inter_subset_right _ _) },
    have hrn : ν.with_density (μ.radon_nikodym_deriv ν) (A ∩ (S ∩ T)ᶜ) = 0,
    { refine with_density_absolutely_continuous ν _ _,
      rw ← nonpos_iff_eq_zero,
      exact hνinter ▸ measure_mono (set.inter_subset_right _ _) },
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (s (A ∩ (S ∩ T)ᶜ)), ← hf,
        ← add_apply, ← hadd, add_apply, hrn, add_zero] },
  have heq' : ∀ A : set α, measurable_set A → s A = s.restrict (S ∩ T)ᶜ A,
  { intros A hA,
    have hsinter : s (A ∩ (S ∩ T)) = 0,
    { rw ← nonpos_iff_eq_zero,
      exact hS₂ ▸ measure_mono
        (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_left _ _)) },
    rw [restrict_apply hA, ← add_zero (s (A ∩ (S ∩ T)ᶜ)), ← hsinter, ← measure_union,
        ← set.inter_union_distrib_left, set.compl_union_self, set.inter_univ],
    { exact disjoint.inter_left' _ ( disjoint.inter_right' _ disjoint_compl_left) },
    { measurability },
    { measurability } },
  ext1 A hA,
  have hμinter : μ.singular_part ν (A ∩ (S ∩ T)) = 0,
  { rw ← nonpos_iff_eq_zero,
    exact hT₂ ▸ measure_mono
      (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_right _ _)) },
  rw [heq' A hA, heq, ← add_zero ((μ.singular_part ν).restrict (S ∩ T)ᶜ A), ← hμinter,
      restrict_apply hA, ← measure_union, ← set.inter_union_distrib_left,
      set.compl_union_self, set.inter_univ],
  { exact disjoint.inter_left' _ ( disjoint.inter_right' _ disjoint_compl_left) },
  { measurability },
  { measurability }
end

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = radon_nikodym_deriv μ ν`.

This theorem provides the uniqueness of the `radon_nikodym_deriv` in the Lebesgue decomposition
theorem, while `measure_theory.measure.eq_singular_part` provides the uniqueness of the
`singular_part`. -/
theorem eq_radon_nikodym_deriv
  {μ ν : measure α} {s : measure α} {f : α → ℝ≥0∞} (hf : measurable f)
  (hs : s ⊥ₘ ν) (hadd : μ = s + ν.with_density f) :
  ν.with_density f = ν.with_density (μ.radon_nikodym_deriv ν) :=
begin
  haveI : have_lebesgue_decomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩,
  obtain ⟨hmeas, hsing, hadd'⟩ := have_lebesgue_decomposition_spec μ ν,
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := ⟨hs, hsing⟩,
  rw hadd' at hadd,
  have hνinter : ν (S ∩ T)ᶜ = 0,
  { rw set.compl_inter,
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _),
    rw [hT₃, hS₃, add_zero],
    exact le_refl _ },
  have heq : (ν.with_density f).restrict (S ∩ T) =
              (ν.with_density (radon_nikodym_deriv μ ν)).restrict (S ∩ T),
  { ext1 A hA,
    have hs : s (A ∩ (S ∩ T)) = 0,
    { rw ← nonpos_iff_eq_zero,
      exact hS₂ ▸ measure_mono
        (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_left _ _)) },
    have hsing : μ.singular_part ν (A ∩ (S ∩ T)) = 0,
    { rw ← nonpos_iff_eq_zero,
      exact hT₂ ▸ measure_mono
        (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_right _ _)) },
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (ν.with_density f (A ∩ (S ∩ T))),
        ← hs, ← add_apply, add_comm, ← hadd, add_apply, hsing, zero_add] },
  have heq' : ∀ A : set α, measurable_set A →
    ν.with_density f A = (ν.with_density f).restrict (S ∩ T) A,
  { intros A hA,
    have hνfinter : ν.with_density f (A ∩ (S ∩ T)ᶜ) = 0,
    { rw ← nonpos_iff_eq_zero,
      exact with_density_absolutely_continuous ν f hνinter ▸
        measure_mono (set.inter_subset_right _ _) },
    rw [restrict_apply hA, ← add_zero (ν.with_density f (A ∩ (S ∩ T))), ← hνfinter,
        ← measure_union, ← set.inter_union_distrib_left, set.union_compl_self, set.inter_univ],
    { exact disjoint.inter_left' _ (disjoint.inter_right' _ disjoint_compl_right) },
    { measurability },
    { measurability } },
  ext1 A hA,
  have hνrn : ν.with_density (μ.radon_nikodym_deriv ν) (A ∩ (S ∩ T)ᶜ) = 0,
  { rw ← nonpos_iff_eq_zero,
    exact with_density_absolutely_continuous ν (μ.radon_nikodym_deriv ν) hνinter ▸
      measure_mono (set.inter_subset_right _ _) },
  rw [heq' A hA, heq, ← add_zero ((ν.with_density (μ.radon_nikodym_deriv ν)).restrict (S ∩ T) A),
      ← hνrn, restrict_apply hA, ← measure_union, ← set.inter_union_distrib_left,
      set.union_compl_self, set.inter_univ],
  { exact disjoint.inter_left' _ (disjoint.inter_right' _ disjoint_compl_right) },
  { measurability },
  { measurability }
end

open vector_measure signed_measure

/-- If two finite measures `μ` and `ν` are not mutually singular, there exists some `ε > 0` and
a measurable set `E`, such that `ν(E) > 0` and `E` is positive with respect to `μ - εν`.

This lemma is useful for the Lebesgue decomposition theorem. -/
lemma exists_positive_of_not_mutually_singular
  (μ ν : measure α) [is_finite_measure μ] [is_finite_measure ν] (h : ¬ μ ⊥ₘ ν) :
  ∃ ε : ℝ≥0, 0 < ε ∧ ∃ E : set α, measurable_set E ∧ 0 < ν E ∧
  0 ≤[E] μ.to_signed_measure - (ε • ν).to_signed_measure :=
begin
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have : ∀ n : ℕ, ∃ i : set α, measurable_set i ∧
    0 ≤[i] (μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).to_signed_measure) ∧
    (μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).to_signed_measure) ≤[iᶜ] 0,
  { intro, exact exists_compl_positive_negative _ },
  choose f hf₁ hf₂ hf₃ using this,
  -- set `A` to be the intersection of all the negative parts of obtained Hahn decompositions
  -- and we show that `μ A = 0`
  set A := ⋂ n, (f n)ᶜ with hA₁,
  have hAmeas : measurable_set A,
  { exact measurable_set.Inter (λ n, (hf₁ n).compl) },
  have hA₂ : ∀ n : ℕ, (μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).to_signed_measure) ≤[A] 0,
  { intro n, exact restrict_le_restrict_subset _ _ (hf₁ n).compl (hf₃ n) (set.Inter_subset _ _) },
  have hA₃ : ∀ n : ℕ, μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A,
  { intro n,
    have := nonpos_of_restrict_le_zero _ (hA₂ n),
    rwa [to_signed_measure_sub_apply hAmeas, sub_nonpos, ennreal.to_real_le_to_real] at this,
    exacts [ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)] },
  have hμ : μ A = 0,
  { lift μ A to ℝ≥0 using ne_of_lt (measure_lt_top _ _) with μA,
    lift ν A to ℝ≥0 using ne_of_lt (measure_lt_top _ _) with νA,
    rw ennreal.coe_eq_zero,
    by_cases hb : 0 < νA,
    { suffices : ∀ b, 0 < b → μA ≤ b,
      { by_contra,
        have h' := this (μA / 2) (nnreal.half_pos (zero_lt_iff.2 h)),
        rw ← @not_not (μA ≤ μA / 2) at h',
        exact h' (not_le.2 (nnreal.half_lt_self h)) },
      intros c hc,
      have : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c * νA⁻¹, refine exists_nat_one_div_lt _,
      { refine mul_pos hc _,
        rw _root_.inv_pos, exact hb },
      rcases this with ⟨n, hn⟩,
      have hb₁ : (0 : ℝ) < νA⁻¹, { rw _root_.inv_pos, exact hb },
      have h' : 1 / (↑n + 1) * νA < c,
      { rw [← nnreal.coe_lt_coe, ← mul_lt_mul_right hb₁, nnreal.coe_mul, mul_assoc,
            ← nnreal.coe_inv, ← nnreal.coe_mul, _root_.mul_inv_cancel, ← nnreal.coe_mul,
            mul_one, nnreal.coe_inv],
        { convert hn, simp },
        { exact ne.symm (ne_of_lt hb) } },
      refine le_trans _ (le_of_lt h'),
      rw [← ennreal.coe_le_coe, ennreal.coe_mul],
      exact hA₃ n },
    { rw [not_lt, le_zero_iff] at hb,
      specialize hA₃ 0,
      simp [hb, le_zero_iff] at hA₃,
      assumption } },
  -- since `μ` and `ν` are not mutually singular, `μ A = 0` implies `ν Aᶜ > 0`
  rw mutually_singular at h, push_neg at h,
  have := h _ hAmeas hμ,
  simp_rw [hA₁, set.compl_Inter, compl_compl] at this,
  -- as `Aᶜ = ⋃ n, f n`, `ν Aᶜ > 0` implies there exists some `n` such that `ν (f n) > 0`
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_Union_null this,
  -- thus, choosing `f n` as the set `E` suffices
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩,
end

namespace lebesgue_decomposition

/-- Given two measures `μ` and `ν`, `measurable_le μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`.

This is useful for the Lebesgue decomposition theorem. -/
def measurable_le (μ ν : measure α) : set (α → ℝ≥0∞) :=
{ f | measurable f ∧ ∀ (A : set α) (hA : measurable_set A), ∫⁻ x in A, f x ∂μ ≤ ν A }

variables {μ ν : measure α}

lemma zero_mem_measurable_le : (0 : α → ℝ≥0∞) ∈ measurable_le μ ν :=
⟨measurable_zero, λ A hA, by simp⟩

lemma max_measurable_le (f g : α → ℝ≥0∞)
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) (A : set α) (hA : measurable_set A) :
  ∫⁻ a in A, max (f a) (g a) ∂μ ≤
  ∫⁻ a in A ∩ { a | f a ≤ g a }, g a ∂μ + ∫⁻ a in A ∩ { a | g a < f a }, f a ∂μ :=
begin
  rw [← lintegral_indicator _ hA, ← lintegral_indicator f,
      ← lintegral_indicator g, ← lintegral_add],
  { refine lintegral_mono (λ a, _),
    by_cases haA : a ∈ A,
    { by_cases f a ≤ g a,
      { simp only,
        rw [set.indicator_of_mem haA, set.indicator_of_mem, set.indicator_of_not_mem, add_zero],
        simp only [le_refl, max_le_iff, and_true, h],
        { rintro ⟨_, hc⟩, exact false.elim ((not_lt.2 h) hc) },
        { exact ⟨haA, h⟩ } },
      { simp only,
        rw [set.indicator_of_mem haA, set.indicator_of_mem _ f,
            set.indicator_of_not_mem, zero_add],
        simp only [true_and, le_refl, max_le_iff, le_of_lt (not_le.1 h)],
        { rintro ⟨_, hc⟩, exact false.elim (h hc) },
        { exact ⟨haA, not_le.1 h⟩ } } },
    { simp [set.indicator_of_not_mem haA] } },
  { exact measurable.indicator hg.1 (hA.inter (measurable_set_le hf.1 hg.1)) },
  { exact measurable.indicator hf.1 (hA.inter (measurable_set_lt hg.1 hf.1)) },
  { exact hA.inter (measurable_set_le hf.1 hg.1) },
  { exact hA.inter (measurable_set_lt hg.1 hf.1) },
end

lemma sup_mem_measurable_le {f g : α → ℝ≥0∞}
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) :
  (λ a, f a ⊔ g a) ∈ measurable_le μ ν :=
begin
  simp_rw ennreal.sup_eq_max,
  refine ⟨measurable.max hf.1 hg.1, λ A hA, _⟩,
  have h₁ := hA.inter (measurable_set_le hf.1 hg.1),
  have h₂ := hA.inter (measurable_set_lt hg.1 hf.1),
  refine le_trans (max_measurable_le f g hf hg A hA) _,
  refine le_trans (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)) _,
  { rw [← measure_union _ h₁ h₂],
    { refine le_of_eq _,
      congr, convert set.inter_union_compl A _,
      ext a, simpa },
    rintro x ⟨⟨-, hx₁⟩, -, hx₂⟩,
    exact (not_le.2 hx₂) hx₁ }
end

lemma supr_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
  (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) = f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a :=
begin
  ext x,
  simp only [option.mem_def, ennreal.some_eq_coe],
  split; intro h; rw ← h, symmetry,
  all_goals {
    set c := (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) with hc,
    set d := (f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a) with hd,
    suffices : c ≤ d ∧ d ≤ c,
    { change c = d, -- removing this line breaks
      exact le_antisymm this.1 this.2 },
    rw [hc, hd],
    refine ⟨_, _⟩,
    { refine bsupr_le (λ n hn, _),
      rcases nat.of_le_succ hn with (h | h),
      { exact le_sup_of_le_right (le_bsupr n h) },
      { exact h ▸ le_sup_left } },
    { refine sup_le _ _,
      { convert @le_bsupr _ _ _ (λ i, i ≤ m + 1) _ m.succ (le_refl _), refl },
      { refine bsupr_le (λ n hn, _),
        have := (le_trans hn (nat.le_succ m)), -- replacing `this` below with the proof breaks
        exact (le_bsupr n this) } } },
end

lemma supr_mem_measurable_le
  (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) :
  (λ x, ⨆ k (hk : k ≤ n), f k x) ∈ measurable_le μ ν :=
begin
  induction n with m hm,
  { refine ⟨_, _⟩,
    { simp [(hf 0).1] },
    { intros A hA, simp [(hf 0).2 A hA] } },
  { have : (λ (a : α), ⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) =
      (λ a, f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a),
    { exact funext (λ _, supr_succ_eq_sup _ _ _) },
    refine ⟨measurable_supr (λ n, measurable.supr_Prop _ (hf n).1), λ A hA, _⟩,
    rw this, exact (sup_mem_measurable_le (hf m.succ) hm).2 A hA }
end

lemma supr_mem_measurable_le'
  (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) :
  (⨆ k (hk : k ≤ n), f k) ∈ measurable_le μ ν :=
begin
  convert supr_mem_measurable_le f hf n,
  ext, simp
end

lemma supr_monotone {α : Type*} (f : ℕ → α → ℝ≥0∞) :
  monotone (λ n x, ⨆ k (hk : k ≤ n), f k x) :=
begin
  intros n m hnm x,
  simp only,
  refine bsupr_le (λ k hk, _),
  have : k ≤ m := le_trans hk hnm, -- replacing `this` below with the proof breaks
  exact le_bsupr k this,
end

lemma supr_monotone' {α : Type*} (f : ℕ → α → ℝ≥0∞) (x : α) :
  monotone (λ n, ⨆ k (hk : k ≤ n), f k x) :=
λ n m hnm, supr_monotone f hnm x

lemma supr_le_le {α : Type*} (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
  f k ≤ λ x, ⨆ k (hk : k ≤ n), f k x :=
λ x, le_bsupr k hk

/-- `measurable_le_eval μ ν` is the set of `∫⁻ x, f x ∂μ` for all `f ∈ measurable_le μ ν`. -/
def measurable_le_eval (μ ν : measure α) : set ℝ≥0∞ :=
(λ f : α → ℝ≥0∞, ∫⁻ x, f x ∂μ) '' measurable_le μ ν

end lebesgue_decomposition

open lebesgue_decomposition

/-- Any pair of finite measures `μ` and `ν`, `have_lebesgue_decomposition`. That is to say,
there exist a measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular
with respect to `ν` and `μ = ξ + ν.with_density f`.

This is not an instance since this is also shown for the more general σ-finite measures with
`measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite`. -/
theorem have_lebesgue_decomposition_of_finite_measure
  {μ ν : measure α} [is_finite_measure μ] [is_finite_measure ν] :
  have_lebesgue_decomposition μ ν :=
⟨begin
  have h := @exists_seq_tendsto_Sup _ _ _ _ _ (measurable_le_eval ν μ)
    ⟨0, 0, zero_mem_measurable_le, by simp⟩ (order_top.bdd_above _),
  choose g hmono hg₂ f hf₁ hf₂ using h,
  -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
  set ξ := ⨆ n k (hk : k ≤ n), f k with hξ,
  -- we see that `ξ` has the largest integral among all functions in `measurable_le`
  have hξ₁ : Sup (measurable_le_eval ν μ) = ∫⁻ a, ξ a ∂ν,
  { have := @lintegral_tendsto_of_tendsto_of_monotone _ _ ν
      (λ n, ⨆ k (hk : k ≤ n), f k) (⨆ n k (hk : k ≤ n), f k) _ _ _,
    { refine tendsto_nhds_unique _ this,
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds _ _,
      { intro n, rw ← hf₂ n,
        apply lintegral_mono,
        simp only [supr_apply, supr_le_le f n n (le_refl _)] },
      { intro n,
        exact le_Sup ⟨⨆ (k : ℕ) (hk : k ≤ n), f k, supr_mem_measurable_le' _ hf₁ _, rfl⟩ } },
    { intro n,
      refine measurable.ae_measurable _,
      convert (supr_mem_measurable_le _ hf₁ n).1,
      ext, simp },
    { refine filter.eventually_of_forall (λ a, _),
      simp [supr_monotone' f _] },
    { refine filter.eventually_of_forall (λ a, _),
      simp [tendsto_at_top_supr (supr_monotone' f a)] } },
  have hξm : measurable ξ,
  { convert measurable_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1),
    ext, simp [hξ] },
  -- `ξ` is the `f` in the theorem statement and we set `μ₁` to be `μ - ν.with_density ξ`
  -- since we need `μ₁ + ν.with_density ξ = μ`
  set μ₁ := μ - ν.with_density ξ with hμ₁,
  have hle : ν.with_density ξ ≤ μ,
  { intros B hB,
    rw [hξ, with_density_apply _ hB],
    simp_rw [supr_apply],
    rw lintegral_supr (λ i, (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _),
    exact supr_le (λ i, (supr_mem_measurable_le _ hf₁ i).2 B hB) },
  haveI : is_finite_measure (ν.with_density ξ),
  { refine is_finite_measure_with_density _,
    have hle' := hle set.univ measurable_set.univ,
    rw [with_density_apply _ measurable_set.univ, measure.restrict_univ] at hle',
    exact lt_of_le_of_lt hle' (measure_lt_top _ _) },
  refine ⟨⟨μ₁, ξ⟩, hξm, _, _⟩,
  { by_contra,
  -- if they are not mutually singular, then from `exists_positive_of_not_mutually_singular`,
  -- there exists some `ε > 0` and a measurable set `E`, such that `μ(E) > 0` and `E` is
  -- positive with respect to `ν - εμ`
    obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_not_mutually_singular μ₁ ν h,
    simp_rw hμ₁ at hE₃,
    have hξle : ∀ A, measurable_set A → ∫⁻ a in A, ξ a ∂ν ≤ μ A,
    { intros A hA, rw hξ,
      simp_rw [supr_apply],
      rw lintegral_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1) (supr_monotone _),
      exact supr_le (λ n, (supr_mem_measurable_le _ hf₁ n).2 A hA) },
  -- since `E` is positive, we have `∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E)` for all `A`
    have hε₂ : ∀ A : set α, measurable_set A → ∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E),
    { intros A hA,
      have := subset_le_of_restrict_le_restrict _ _ hE₁ hE₃ (set.inter_subset_right A E),
      rwa [zero_apply, to_signed_measure_sub_apply (hA.inter hE₁),
            measure.sub_apply (hA.inter hE₁) hle,
            ennreal.to_real_sub_of_le _ (ne_of_lt (measure_lt_top _ _)), sub_nonneg,
            le_sub_iff_add_le, ← ennreal.to_real_add, ennreal.to_real_le_to_real,
            measure.coe_nnreal_smul, pi.smul_apply, with_density_apply _ (hA.inter hE₁),
            show ε • ν (A ∩ E) = (ε : ℝ≥0∞) * ν (A ∩ E), by refl,
            ← set_lintegral_const, ← lintegral_add measurable_const hξm] at this,
      { rw [ne.def, ennreal.add_eq_top, not_or_distrib],
        exact ⟨ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)⟩ },
      { exact ne_of_lt (measure_lt_top _ _) },
      { exact ne_of_lt (measure_lt_top _ _) },
      { exact ne_of_lt (measure_lt_top _ _) },
      { rw with_density_apply _ (hA.inter hE₁),
        exact hξle (A ∩ E) (hA.inter hE₁) },
      { apply_instance } },
  -- from this, we can show `ξ + ε * E.indicator` is a function in `measurable_le` with
  -- integral greater than `ξ`
    have hξε : ξ + E.indicator (λ _, ε) ∈ measurable_le ν μ,
    { refine ⟨measurable.add hξm (measurable.indicator measurable_const hE₁), λ A hA, _⟩,
      have : ∫⁻ a in A, (ξ + E.indicator (λ _, ε)) a ∂ν =
            ∫⁻ a in A ∩ E, ε + ξ a ∂ν + ∫⁻ a in A ∩ Eᶜ, ξ a ∂ν,
      { rw [lintegral_add measurable_const hξm, add_assoc,
            ← lintegral_union (hA.inter hE₁) (hA.inter (hE₁.compl))
              (disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _)
              disjoint_compl_right), set.inter_union_compl],
        simp_rw [pi.add_apply],
        rw [lintegral_add hξm (measurable.indicator measurable_const hE₁), add_comm],
        refine congr_fun (congr_arg has_add.add _) _,
        rw [set_lintegral_const, lintegral_indicator _ hE₁, set_lintegral_const,
            measure.restrict_apply hE₁, set.inter_comm] },
      conv_rhs { rw ← set.inter_union_compl A E },
      rw [this, measure_union _ (hA.inter hE₁) (hA.inter hE₁.compl)],
      { exact add_le_add (hε₂ A hA)
          (hξle (A ∩ Eᶜ) (hA.inter hE₁.compl)) },
      { exact disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _)
          disjoint_compl_right } },
      have : ∫⁻ a, ξ a + E.indicator (λ _, ε) a ∂ν ≤ Sup (measurable_le_eval ν μ) :=
        le_Sup ⟨ξ + E.indicator (λ _, ε), hξε, rfl⟩,
  -- but this contradicts the maximality of `∫⁻ x, ξ x ∂ν`
      refine not_lt.2 this _,
      rw [hξ₁, lintegral_add hξm (measurable.indicator (measurable_const) hE₁),
          lintegral_indicator _ hE₁, set_lintegral_const],
      refine ennreal.lt_add_right _ (ennreal.mul_pos.2 ⟨ennreal.coe_pos.2 hε₁, hE₂⟩),
      have := measure_ne_top (ν.with_density ξ) set.univ,
      rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ] at this },
  -- since `ν.with_density ξ ≤ μ`, it is clear that `μ = μ₁ + ν.with_density ξ`
  { rw hμ₁, ext1 A hA,
    rw [measure.coe_add, pi.add_apply, measure.sub_apply hA hle,
        add_comm, ennreal.add_sub_cancel_of_le (hle A hA)] },
end⟩

local attribute [instance] have_lebesgue_decomposition_of_finite_measure

instance {μ : measure α} {S : μ.finite_spanning_sets_in {s : set α | measurable_set s}} (n : ℕ) :
  is_finite_measure (μ.restrict $ S.set n) :=
⟨by { rw [restrict_apply measurable_set.univ, set.univ_inter], exact S.finite _ }⟩

/-- **The Lebesgue decomposition theorem**: Any pair of σ-finite measures `μ` and `ν`
`have_lebesgue_decomposition`. That is to say, there exist a measure `ξ` and a measurable function
`f`, such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f` -/
@[priority 100] -- see Note [lower instance priority]
instance have_lebesgue_decomposition_of_sigma_finite
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  have_lebesgue_decomposition μ ν :=
⟨begin
  -- Since `μ` and `ν` are both σ-finite, there exists a sequence of pairwise disjoint spanning
  -- sets which are finite with respect to both `μ` and `ν`
  obtain ⟨S, T, h₁, h₂⟩ := exists_eq_disjoint_finite_spanning_sets_in μ ν,
  have h₃ : pairwise (disjoint on T.set) := h₁ ▸ h₂,
  -- We define `μn` and `νn` as sequences of measures such that `μn n = μ ∩ S n` and
  -- `νn n = ν ∩ S n` where `S` is the aforementioned finite spanning set sequence.
  -- Since `S` is spanning, it is clear that `sum μn = μ` and `sum νn = ν`
  set μn : ℕ → measure α := λ n, μ.restrict (S.set n) with hμn,
  have hμ : μ = sum μn,
    { rw [hμn, ← restrict_Union h₂ S.set_mem, S.spanning, restrict_univ] },
  set νn : ℕ → measure α := λ n, ν.restrict (T.set n) with hνn,
  have hν : ν = sum νn,
    { rw [hνn, ← restrict_Union h₃ T.set_mem, T.spanning, restrict_univ] },
  -- As `S` is finite with respect to both `μ` and `ν`, it is clear that `μn n` and `νn n` are
  -- finite measures for all `n : ℕ`. Thus, we may apply the finite Lebesgue decomposition theorem
  -- to `μn n` and `νn n`. We define `ξ` as the sum of the singular part of the Lebesgue
  -- decompositions of `μn n` and `νn n`, and `f` as the sum of the Radon-Nikodym derviatives of
  -- `μn n` and `νn n` restricted on `S n`
  set ξ := sum (λ n, singular_part (μn n) (νn n)) with hξ,
  set f := ∑' n, (S.set n).indicator (radon_nikodym_deriv (μn n) (νn n)) with hf,
  -- I claim `ξ` and `f` form a Lebesgue decomposition of `μ` and `ν`
  refine ⟨⟨ξ, f⟩, _, _, _⟩,
  { exact measurable.ennreal_tsum' (λ n, measurable.indicator
      (measurable_radon_nikodym_deriv (μn n) (νn n)) (S.set_mem n)) },
  -- We show that `ξ` is mutually singular with respect to `ν`
  { choose A hA₁ hA₂ hA₃ using λ n, mutually_singular_singular_part (μn n) (νn n),
    simp only [hξ],
  -- We use the set `B := ⋃ j, (S.set j) ∩ A j` where `A n` is the set provided as
  -- `singular_part (μn n) (νn n) ⊥ₘ νn n`
    refine ⟨⋃ j, (S.set j) ∩ A j,
      measurable_set.Union (λ n, (S.set_mem n).inter (hA₁ n)), _, _⟩,
  -- `ξ B = 0` since `ξ B = ∑ i j, singular_part (μn j) (νn j) (S.set i ∩ A i)`
  --                     `= ∑ i, singular_part (μn i) (νn i) (S.set i ∩ A i)`
  --                     `≤ ∑ i, singular_part (μn i) (νn i) (A i) = 0`
  -- where the second equality follows as `singular_part (μn j) (νn j) (S.set i ∩ A i)` vanishes
  -- for all `i ≠ j`
    { rw [measure_Union],
      { have : ∀ i, (sum (λ n, (μn n).singular_part (νn n))) (S.set i ∩ A i) =
          (μn i).singular_part (νn i) (S.set i ∩ A i),
        { intro i, rw [sum_apply _ ((S.set_mem i).inter (hA₁ i)), tsum_eq_single i],
          { intros j hij,
            rw [hμn, ← nonpos_iff_eq_zero],
            refine le_trans ((singular_part_le _ _) _ ((S.set_mem i).inter (hA₁ i))) (le_of_eq _),
            rw [restrict_apply ((S.set_mem i).inter (hA₁ i)), set.inter_comm, ← set.inter_assoc],
            have : disjoint (S.set j) (S.set i) := h₂ j i hij,
            rw set.disjoint_iff_inter_eq_empty at this,
            rw [this, set.empty_inter, measure_empty] },
          { apply_instance } },
        simp_rw [this, tsum_eq_zero_iff ennreal.summable],
        intro n, exact measure_mono_null (set.inter_subset_right _ _) (hA₂ n) },
      { exact h₂.mono (λ i j, disjoint.mono inf_le_left inf_le_left) },
      { exact λ n, (S.set_mem n).inter (hA₁ n) } },
  -- We will now show `ν Bᶜ = 0`. This follows since `Bᶜ = ⋃ n, S.set n ∩ (A n)ᶜ` and thus,
  -- `ν Bᶜ = ∑ i, ν (S.set i ∩ (A i)ᶜ) = ∑ i, (νn i) (A i)ᶜ = 0`
    { have hcompl : is_compl (⋃ n, (S.set n ∩ A n)) (⋃ n, S.set n ∩ (A n)ᶜ),
      { split,
        { rintro x ⟨hx₁, hx₂⟩, rw set.mem_Union at hx₁ hx₂,
          obtain ⟨⟨i, hi₁, hi₂⟩, ⟨j, hj₁, hj₂⟩⟩ := ⟨hx₁, hx₂⟩,
          have : i = j,
          { by_contra hij, exact h₂ i j hij ⟨hi₁, hj₁⟩ },
          exact hj₂ (this ▸ hi₂) },
        { intros x hx,
          simp only [set.mem_Union, set.sup_eq_union, set.mem_inter_eq,
                    set.mem_union_eq, set.mem_compl_eq, or_iff_not_imp_left],
          intro h, push_neg at h,
          rw [set.top_eq_univ, ← S.spanning, set.mem_Union] at hx,
          obtain ⟨i, hi⟩ := hx,
          exact ⟨i, hi, h i hi⟩ } },
      rw [hcompl.compl_eq, measure_Union, tsum_eq_zero_iff ennreal.summable],
      { intro n, rw [set.inter_comm, ← restrict_apply (hA₁ n).compl, ← hA₃ n, hνn, h₁] },
      { exact h₂.mono (λ i j, disjoint.mono inf_le_left inf_le_left) },
      { exact λ n, (S.set_mem n).inter (hA₁ n).compl } } },
  -- Finally, it remains to show `μ = ξ + ν.with_density f`. Since `μ = sum μn`, and
  -- `ξ + ν.with_density f = ∑ n, singular_part (μn n) (νn n)`
  --                        `+ ν.with_density (radon_nikodym_deriv (μn n) (νn n)) ∩ (S.set n)`,
  -- it suffices to show that the individual summands are equal. This follows by the
  -- Lebesgue decomposition properties on the individual `μn n` and `νn n`
  { simp only [hξ, hf, hμ],
    rw [with_density_tsum _, sum_add_sum],
    { refine sum_congr (λ n, _),
      conv_lhs { rw have_lebesgue_decomposition_add (μn n) (νn n) },
      suffices heq : (νn n).with_density ((μn n).radon_nikodym_deriv (νn n)) =
        ν.with_density ((S.set n).indicator ((μn n).radon_nikodym_deriv (νn n))),
      { rw heq },
      rw [hν, with_density_indicator (S.set_mem n), restrict_sum _ (S.set_mem n)],
      suffices hsumeq : sum (λ (i : ℕ), (νn i).restrict (S.set n)) = νn n,
      { rw hsumeq },
      ext1 s hs,
      rw [sum_apply _ hs, tsum_eq_single n, hνn, h₁,
          restrict_restrict (T.set_mem n), set.inter_self],
      { intros m hm,
        rw [hνn, h₁, restrict_restrict (T.set_mem n), set.inter_comm,
            set.disjoint_iff_inter_eq_empty.1 (h₃ m n hm), restrict_empty,
            coe_zero, pi.zero_apply] },
      { apply_instance } },
    { exact λ n, measurable.indicator (measurable_radon_nikodym_deriv _ _) (S.set_mem n) } },
end⟩

end measure

namespace signed_measure

open measure

/-- Given a signed measure `s` and a measure `μ`, `singular_part s μ` is the signed measure
such that ... -/
def singular_part (s : signed_measure α) (μ : measure α) : signed_measure α :=
(s.to_jordan_decomposition.pos_part.singular_part μ).to_signed_measure -
(s.to_jordan_decomposition.neg_part.singular_part μ).to_signed_measure

section

variables (s : signed_measure α) (μ : measure α) [sigma_finite μ]

lemma singular_part_mutually_singular :
  s.to_jordan_decomposition.pos_part.singular_part μ ⊥ₘ
  s.to_jordan_decomposition.neg_part.singular_part μ :=
begin
  obtain ⟨i, hi, hpos, hneg⟩ := s.to_jordan_decomposition.mutually_singular,
  rw s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition_add μ at hpos,
  rw s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition_add μ at hneg,
  rw [add_apply, add_eq_zero_iff] at hpos hneg,
  exact ⟨i, hi, hpos.1, hneg.1⟩
end

lemma singular_part_total_variation :
  (s.singular_part μ).total_variation =
  s.to_jordan_decomposition.pos_part.singular_part μ +
  s.to_jordan_decomposition.neg_part.singular_part μ :=
begin
  have : (s.singular_part μ).to_jordan_decomposition =
    ⟨s.to_jordan_decomposition.pos_part.singular_part μ,
     s.to_jordan_decomposition.neg_part.singular_part μ, singular_part_mutually_singular s μ⟩,
  { refine jordan_decomposition.to_signed_measure_injective _,
    rw to_signed_measure_to_jordan_decomposition,
    refl },
  { rw [total_variation, this] },
end

lemma mutually_singular_singular_part :
  singular_part s μ ⊥ᵥ μ.to_ennreal_vector_measure :=
begin
  rw [mutually_singular_ennreal_iff, singular_part_total_variation],
  change _ ⊥ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ),
  rw vector_measure.equiv_measure.right_inv μ,
  exact measure.mutually_singular.add
    (mutually_singular_singular_part _ _) (mutually_singular_singular_part _ _),
end

end

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`radon_nikodym_deriv s μ` satisfies `μ.with_densityᵥ (s.radon_nikodym_deriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`measure_theory.signed_measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq`
and can be found in `measure_theory.decomposition.radon_nikodym`. -/
def radon_nikodym_deriv (s : signed_measure α) (μ : measure α) : α → ℝ := λ x,
(s.to_jordan_decomposition.pos_part.radon_nikodym_deriv μ x).to_real -
(s.to_jordan_decomposition.neg_part.radon_nikodym_deriv μ x).to_real

variables {s : signed_measure α} {μ : measure α} [sigma_finite μ]

section move

lemma has_finite_integral_to_real_of_lintegral_ne_top
  {μ : measure α} {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
  has_finite_integral (λ x, (f x).to_real) μ :=
begin
  have : ∀ x, (∥(f x).to_real∥₊ : ℝ≥0∞) =
    @coe ℝ≥0 ℝ≥0∞ _ (⟨(f x).to_real, ennreal.to_real_nonneg⟩ : ℝ≥0),
  { intro x, rw real.nnnorm_of_nonneg },
  simp_rw [has_finite_integral, this],
  refine lt_of_le_of_lt (lintegral_mono (λ x, _)) (lt_top_iff_ne_top.2 hf),
  by_cases hfx : f x = ∞,
  { simp [hfx] },
  { lift f x to ℝ≥0 using hfx with fx,
    simp [← h] }
end

lemma is_finite_measure_with_density {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
  is_finite_measure (μ.with_density f) :=
⟨by { rwa [with_density_apply f measurable_set.univ, set_lintegral_univ, lt_top_iff_ne_top] }⟩

lemma integrable_to_real_of_lintegral_ne_top
  {μ : measure α} {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
  integrable (λ x, (f x).to_real) μ :=
⟨ae_measurable.ennreal_to_real hfm, has_finite_integral_to_real_of_lintegral_ne_top hfi⟩

lemma with_densityᵥ_sub_eq_with_density {f g : α → ℝ≥0∞}
  (hfm : ae_measurable f μ) (hgm : ae_measurable g μ)
  (hf : ∫⁻ x, f x ∂μ ≠ ∞) (hg : ∫⁻ x, g x ∂μ ≠ ∞) :
  μ.with_densityᵥ (λ x, (f x).to_real - (g x).to_real) =
  @to_signed_measure α _ (μ.with_density f) (is_finite_measure_with_density hf) -
  @to_signed_measure α _ (μ.with_density g) (is_finite_measure_with_density hg) :=
begin
  have hfi := integrable_to_real_of_lintegral_ne_top hfm hf,
  have hgi := integrable_to_real_of_lintegral_ne_top hgm hg,
  ext i hi,
  rw [with_densityᵥ_apply _ hi, vector_measure.sub_apply,
      to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi,
      with_density_apply _ hi, with_density_apply _ hi, integral_sub,
      integral_to_real hfm.restrict, integral_to_real hgm.restrict],
  { refine ae_lt_top' hgm.restrict (lt_of_le_of_lt _ (lt_top_iff_ne_top.2 hg)),
    conv_rhs { rw ← set_lintegral_univ },
    exact lintegral_mono_set (set.subset_univ _) },
  { refine ae_lt_top' hfm.restrict (lt_of_le_of_lt _ (lt_top_iff_ne_top.2 hf)),
    conv_rhs { rw ← set_lintegral_univ },
    exact lintegral_mono_set (set.subset_univ _) },
  { rw ← integrable_on,
    rw ← integrable_on_univ at hfi,
    exact integrable_on.mono hfi (set.subset_univ _) (le_refl _) },
  { rw ← integrable_on,
    rw ← integrable_on_univ at hgi,
    exact integrable_on.mono hgi (set.subset_univ _) (le_refl _) },
  { exact hfi.sub hgi }
end

end move

@[measurability]
lemma measurable_radon_nikodym_deriv (s : signed_measure α) (μ : measure α) :
  measurable (radon_nikodym_deriv s μ) :=
begin
  rw [radon_nikodym_deriv],
  measurability,
end

lemma integrable_radon_nikodym_deriv (s : signed_measure α) (μ : measure α) :
  integrable (radon_nikodym_deriv s μ) μ :=
begin
  refine integrable.sub _ _;
  { split, measurability,
    exact has_finite_integral_to_real_of_lintegral_ne_top
      (lintegral_radon_nikodym_deriv_lt_top _ μ).ne }
end

/-- The Lebesgue Decomposition theorem between a signed measure and a σ-finite positive measure. -/
theorem singular_part_add_with_density_radon_nikodym_deriv_eq :
  s.singular_part μ + μ.with_densityᵥ (s.radon_nikodym_deriv μ) = s :=
begin
  conv_rhs { rw [← to_signed_measure_to_jordan_decomposition s,
                 jordan_decomposition.to_signed_measure] },
  rw [singular_part, radon_nikodym_deriv, with_densityᵥ_sub_eq_with_density,
      sub_eq_add_neg, sub_eq_add_neg,
      add_comm (s.to_jordan_decomposition.pos_part.singular_part μ).to_signed_measure, ← add_assoc,
      add_assoc (-(s.to_jordan_decomposition.neg_part.singular_part μ).to_signed_measure),
      ← to_signed_measure_add, add_comm, ← add_assoc, ← neg_add, ← to_signed_measure_add,
      add_comm, ← sub_eq_add_neg],
  congr,
  { exact (s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition_add μ).symm },
  { rw add_comm,
    exact (s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition_add μ).symm },
  { exact ((to_jordan_decomposition s).pos_part.measurable_radon_nikodym_deriv μ).ae_measurable },
  { exact ((to_jordan_decomposition s).neg_part.measurable_radon_nikodym_deriv μ).ae_measurable },
  { exact (lintegral_radon_nikodym_deriv_lt_top _ _).ne },
  { exact (lintegral_radon_nikodym_deriv_lt_top _ _).ne },
end

end signed_measure

end measure_theory
