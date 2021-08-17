/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.jordan

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two finite measures `μ` and `ν`, there exists a finite measure `ξ` and a measurable function
`f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `measure_theory.measure.have_lebesgue_decomposition` : A pair of measures `μ` and `ν` is said
  to `have_lebesgue_decomposition` if there exists a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f`
* `measure_theory.measure.singular_part` : If a pair of measures `have_lebesgue_decomposition`,
  then `singular_part` chooses the measure from `have_lebesgue_decomposition`, otherwise it
  returns the zero measure.
* ``measure_theory.measure.radon_nikodym_deriv` : If a pair of measures
  `have_lebesgue_decomposition`, then `radon_nikodym_deriv` chooses the measurable function from
  `have_lebesgue_decomposition`, otherwise it returns the zero function.

## Main results

* `measure_theory.measure.have_lebesgue_decomposition_of_finite_measure` :
  the Lebesgue decomposition theorem.
* `measure_theory.measure.eq_singular_part` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = singular_part μ ν`.
* `measure_theory.measure.eq_radon_nikodym_deriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = radon_nikodym_deriv μ ν`.

## To do

The Lebesgue decomposition theorem can be generalized to σ-finite measures from the finite version.

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
def have_lebesgue_decomposition (μ ν : measure α) : Prop :=
∃ (p : measure α × (α → ℝ≥0∞)), measurable p.2 ∧ p.1 ⊥ₘ ν ∧ μ = p.1 + ν.with_density p.2

/-- If a pair of measures `have_lebesgue_decomposition`, then `singular_part` chooses the
measure from `have_lebesgue_decomposition`, otherwise it returns the zero measure. -/
@[irreducible]
def singular_part (μ ν : measure α) : measure α :=
if h : have_lebesgue_decomposition μ ν then (classical.some h).1 else 0

/-- If a pair of measures `have_lebesgue_decomposition`, then `radon_nikodym_deriv` chooses the
measurable function from `have_lebesgue_decomposition`, otherwise it returns the zero function. -/
@[irreducible]
def radon_nikodym_deriv (μ ν : measure α) : α → ℝ≥0∞ :=
if h : have_lebesgue_decomposition μ ν then (classical.some h).2 else 0

lemma have_lebesgue_decomposition_spec {μ ν : measure α} (h : have_lebesgue_decomposition μ ν) :
  measurable (radon_nikodym_deriv μ ν) ∧ (singular_part μ ν) ⊥ₘ ν ∧
  μ = (singular_part μ ν) + ν.with_density (radon_nikodym_deriv μ ν) :=
begin
  rw [singular_part, radon_nikodym_deriv, dif_pos h, dif_pos h],
  exact classical.some_spec h,
end

lemma have_lebesgue_decomposition_add {μ ν : measure α} (h : have_lebesgue_decomposition μ ν) :
  μ = (singular_part μ ν) + ν.with_density (radon_nikodym_deriv μ ν) :=
(have_lebesgue_decomposition_spec h).2.2

@[measurability]
lemma measurable_radon_nikodym_deriv (μ ν : measure α) :
  measurable $ radon_nikodym_deriv μ ν :=
begin
  by_cases h : have_lebesgue_decomposition μ ν,
  { exact (have_lebesgue_decomposition_spec h).1 },
  { rw [radon_nikodym_deriv, dif_neg h],
    exact measurable_zero }
end

lemma mutually_singular_singular_part (μ ν : measure α) :
  singular_part μ ν ⊥ₘ ν :=
begin
  by_cases h : have_lebesgue_decomposition μ ν,
  { exact (have_lebesgue_decomposition_spec h).2.1 },
  { rw [singular_part, dif_neg h],
    exact mutually_singular.zero.symm }
end

lemma singular_part_le (μ ν : measure α) : singular_part μ ν ≤ μ :=
begin
  by_cases h : have_lebesgue_decomposition μ ν,
  { obtain ⟨-, -, h⟩ := have_lebesgue_decomposition_spec h,
    conv_rhs { rw h },
    exact measure.le_add_right (le_refl _) },
  { rw [singular_part, dif_neg h],
    exact measure.zero_le μ }
end

lemma with_density_radon_nikodym_deriv_le (μ ν : measure α) :
  ν.with_density (radon_nikodym_deriv μ ν) ≤ μ :=
begin
  by_cases h : have_lebesgue_decomposition μ ν,
  { obtain ⟨-, -, h⟩ := have_lebesgue_decomposition_spec h,
    conv_rhs { rw h },
    exact measure.le_add_left (le_refl _) },
  { rw [radon_nikodym_deriv, dif_neg h, with_density_zero],
    exact measure.zero_le μ }
end

instance {μ ν : measure α} [finite_measure μ] :
  finite_measure (singular_part μ ν) :=
finite_measure_of_le μ $ singular_part_le μ ν

instance {μ ν : measure α} [sigma_finite μ] :
  sigma_finite (singular_part μ ν) :=
sigma_finite_of_le μ $ singular_part_le μ ν

instance {μ ν : measure α} [finite_measure μ] :
  finite_measure (ν.with_density $ radon_nikodym_deriv μ ν) :=
finite_measure_of_le μ $ with_density_radon_nikodym_deriv_le μ ν

instance {μ ν : measure α} [sigma_finite μ] :
  sigma_finite (ν.with_density $ radon_nikodym_deriv μ ν) :=
sigma_finite_of_le μ $ with_density_radon_nikodym_deriv_le μ ν

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
  obtain ⟨hmeas, hsing, hadd'⟩ := have_lebesgue_decomposition_spec ⟨⟨s, f⟩, hf, hs, hadd⟩,
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
  obtain ⟨hmeas, hsing, hadd'⟩ := have_lebesgue_decomposition_spec ⟨⟨s, f⟩, hf, hs, hadd⟩,
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
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ¬ μ ⊥ₘ ν) :
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

/-- **The Lebesgue decomposition theorem**: Any pair of finite measures `μ` and `ν`
`have_lebesgue_decomposition`. That is to say, there exists a measure `ξ` and a measurable function
`f`, such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f` -/
theorem have_lebesgue_decomposition_of_finite_measure
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] :
  have_lebesgue_decomposition μ ν :=
begin
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
  haveI : finite_measure (ν.with_density ξ),
  { refine finite_measure_with_density _,
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
      have := measure_lt_top (ν.with_density ξ) set.univ,
      rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ] at this },
  -- since `ν.with_density ξ ≤ μ`, it is clear that `μ = μ₁ + ν.with_density ξ`
  { rw hμ₁, ext1 A hA,
    rw [measure.coe_add, pi.add_apply, measure.sub_apply hA hle,
        add_comm, ennreal.add_sub_cancel_of_le (hle A hA)] },
end

end measure

end measure_theory
