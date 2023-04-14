/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import measure_theory.measure.haar
import measure_theory.group.fundamental_domain
import algebra.group.opposite

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `measure_theory.is_fundamental_domain.smul_invariant_measure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `measure_theory.is_fundamental_domain.is_mul_left_invariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/

noncomputable theory

open set measure_theory topological_space measure_theory.measure quotient_group
open_locale pointwise measure_theory topology big_operators nnreal ennreal

variables {G : Type*} [group G] [measurable_space G] [topological_space G]
  [topological_group G] [borel_space G]
  {μ : measure G}
  {Γ : subgroup G}

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G/Γ`."]
instance quotient_group.has_measurable_smul [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)] :
  has_measurable_smul G (G ⧸ Γ) :=
{ measurable_const_smul := λ g, (continuous_const_smul g).measurable,
  measurable_smul_const := λ x, (quotient_group.continuous_smul₁ x).measurable }

variables {𝓕 : set G} (h𝓕 : is_fundamental_domain Γ.opposite 𝓕 μ)
include h𝓕

variables [countable Γ] [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)]

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
  `G`-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.smul_invariant_measure_map
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  smul_invariant_measure G (G ⧸ Γ) (measure.map quotient_group.mk (μ.restrict 𝓕)) :=
{ measure_preimage_smul :=
  begin
    let π : G → G ⧸ Γ := quotient_group.mk,
    have meas_π : measurable π :=
      continuous_quotient_mk.measurable,
    have 𝓕meas : null_measurable_set 𝓕 μ := h𝓕.null_measurable_set,
    intros g A hA,
    have meas_πA : measurable_set (π ⁻¹' A) := measurable_set_preimage meas_π hA,
    rw [measure.map_apply meas_π hA,
      measure.map_apply meas_π (measurable_set_preimage (measurable_const_smul g) hA),
      measure.restrict_apply₀' 𝓕meas, measure.restrict_apply₀' 𝓕meas],
    set π_preA := π ⁻¹' A,
    have : (quotient_group.mk ⁻¹' ((λ (x : G ⧸ Γ), g • x) ⁻¹' A)) = has_mul.mul g ⁻¹' π_preA,
    { ext1, simp },
    rw this,
    have : μ (has_mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ has_mul.mul (g⁻¹) ⁻¹' 𝓕),
    { transitivity μ (has_mul.mul g ⁻¹' (π_preA ∩ has_mul.mul g⁻¹ ⁻¹' 𝓕)),
      { rw preimage_inter,
        congr,
        rw [← preimage_comp, comp_mul_left, mul_left_inv],
        ext,
        simp, },
      rw measure_preimage_mul, },
    rw this,
    have h𝓕_translate_fundom : is_fundamental_domain Γ.opposite (g • 𝓕) μ := h𝓕.smul_of_comm g,
    rw [h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA, ← preimage_smul_inv], refl,
    rintros ⟨γ, γ_in_Γ⟩,
    ext,
    have : π (x * (mul_opposite.unop γ)) = π (x) := by simpa [quotient_group.eq'] using γ_in_Γ,
    simp [(•), this],
  end }

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.is_mul_left_invariant_map [subgroup.normal Γ]
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
{ map_mul_left_eq_self := begin
    intros x,
    apply measure.ext,
    intros A hA,
    obtain ⟨x₁, _⟩ := @quotient.exists_rep _ (quotient_group.left_rel Γ) x,
    haveI := h𝓕.smul_invariant_measure_map,
    convert measure_preimage_smul x₁ ((measure.map quotient_group.mk) (μ.restrict 𝓕)) A using 1,
    rw [← h, measure.map_apply],
    { refl, },
    { exact measurable_const_mul _, },
    { exact hA, },
  end }

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.map_restrict_quotient [t2_space (G ⧸ Γ)]
  [second_countable_topology (G ⧸ Γ)] (K : positive_compacts (G ⧸ Γ)) [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] [μ.is_mul_right_invariant]
  (h𝓕_finite : μ 𝓕 < ⊤) : measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)
  = (μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K)) • (measure_theory.measure.haar_measure K) :=
begin
  let π : G →* G ⧸ Γ := quotient_group.mk' Γ,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  have 𝓕meas : null_measurable_set 𝓕 μ := h𝓕.null_measurable_set,
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by { rw [measure.restrict_apply₀' 𝓕meas, univ_inter], exact h𝓕_finite }⟩,
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
    h𝓕.is_mul_left_invariant_map,
  rw [measure.haar_measure_unique (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)) K,
    measure.map_apply meas_π, measure.restrict_apply₀' 𝓕meas, inter_comm],
  exact K.is_compact.measurable_set,
end

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
@[to_additive measure_preserving_quotient_add_group.mk' "Given a normal subgroup `Γ` of an additive
  topological group `G` with Haar measure `μ`, which is also right-invariant, and a finite volume
  fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is measure-preserving between appropriate
  multiples of Haar measure on `G` and `G ⧸ Γ`."]
lemma measure_preserving_quotient_group.mk' [t2_space (G ⧸ Γ)] [second_countable_topology (G ⧸ Γ)]
  (K : positive_compacts (G ⧸ Γ)) [subgroup.normal Γ] [measure_theory.measure.is_haar_measure μ]
  [μ.is_mul_right_invariant] (h𝓕_finite : μ 𝓕 < ⊤) (c : ℝ≥0)
  (h : μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K) = c) :
  measure_preserving
    (quotient_group.mk' Γ)
    (μ.restrict 𝓕)
    (c • (measure_theory.measure.haar_measure K)) :=
{ measurable := continuous_quotient_mk.measurable,
  map_eq := by rw [h𝓕.map_restrict_quotient K h𝓕_finite, h]; refl }

section

local notation `μ_𝓕` := measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)

/-- The `ess_sup` of a function `g` on the quotient space `G ⧸ Γ` with respect to the pushforward
  of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental domain `𝓕`, is the
  same as the `ess_sup` of `g`'s lift to the universal cover `G` with respect to `μ`. -/
@[to_additive "The `ess_sup` of a function `g` on the additive quotient space `G ⧸ Γ` with respect
  to the pushforward of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental
  domain `𝓕`, is the same as the `ess_sup` of `g`'s lift to the universal cover `G` with respect
  to `μ`."]
lemma ess_sup_comp_quotient_group_mk [μ.is_mul_right_invariant] {g : G ⧸ Γ → ℝ≥0∞}
  (g_ae_measurable : ae_measurable g μ_𝓕) :
  ess_sup g μ_𝓕 = ess_sup (λ (x : G), g x) μ :=
begin
  have hπ : measurable (quotient_group.mk : G → G ⧸ Γ) := continuous_quotient_mk.measurable,
  rw ess_sup_map_measure g_ae_measurable hπ.ae_measurable,
  refine h𝓕.ess_sup_measure_restrict _,
  rintros ⟨γ, hγ⟩ x,
  dsimp,
  congr' 1,
  exact quotient_group.mk_mul_of_mem x hγ,
end

/-- Given a quotient space `G ⧸ Γ` where `Γ` is `countable`, and the restriction,
  `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient! -/
@[to_additive "Given an additive quotient space `G ⧸ Γ` where `Γ` is `countable`, and the
  restriction, `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient!"]
lemma _root_.measure_theory.is_fundamental_domain.absolutely_continuous_map
  [μ.is_mul_right_invariant] :
  map (quotient_group.mk : G → G ⧸ Γ) μ ≪ map (quotient_group.mk : G → G ⧸ Γ) (μ.restrict 𝓕) :=
begin
  set π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  apply absolutely_continuous.mk,
  intros s s_meas hs,
  rw map_apply meas_π s_meas at hs ⊢,
  rw measure.restrict_apply at hs,
  apply h𝓕.measure_zero_of_invariant _ _ hs,
  { intros γ,
    ext g,
    rw set.mem_smul_set_iff_inv_smul_mem,
    rw mem_preimage,
    rw mem_preimage,
    congrm _ ∈ s,
    convert quotient_group.mk_mul_of_mem g (γ⁻¹).2, },
  exact measurable_set_preimage meas_π s_meas,
end

local attribute [-instance] quotient.measurable_space

/- Move to commit message in PR: question: how to deduce
  `ae_strongly_measurable (quotient_group.automorphize f) μ_𝓕`? -/

/-- This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the
  integral of a function `f` on `G` with respect to a right-invariant measure `μ` is equal to the
  integral over the quotient `G ⧸ Γ` of the automorphization of `f`. -/
@[to_additive "This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of an
  additive  group `G`, the integral of a function `f` on `G` with respect to a right-invariant
  measure `μ` is equal to the integral over the quotient `G ⧸ Γ` of the automorphization of `f`."]
lemma quotient_group.integral_eq_integral_automorphize {E : Type*} [normed_add_comm_group E]
  [complete_space E] [normed_space ℝ E] [μ.is_mul_right_invariant] {f : G → E}
  (hf₁ : integrable f μ) (hf₂ : ae_strongly_measurable (automorphize f) μ_𝓕) :
  ∫ x : G, f x ∂μ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 :=
calc ∫ x : G, f x ∂μ  = ∑' γ : Γ.opposite, ∫ x in 𝓕, f (γ • x) ∂μ : h𝓕.integral_eq_tsum'' f hf₁
... = ∫ x in 𝓕, ∑' γ : Γ.opposite, f (γ • x) ∂μ :
  begin
    rw integral_tsum,
    { exact λ i, (hf₁.1.comp_quasi_measure_preserving
        (measure_preserving_smul i μ).quasi_measure_preserving).restrict, },
    { rw ← h𝓕.lintegral_eq_tsum'' (λ x, ‖f x‖₊),
      exact ne_of_lt hf₁.2, },
  end
... = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 :
  (integral_map continuous_quotient_mk.ae_measurable hf₂).symm

/-- This is the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the integral of a
  function `f` on `G` times the lift to `G` of a function `g` on the quotient `G ⧸ Γ` with respect
  to a right-invariant measure `μ` on `G`, is equal to the integral over the quotient of the
  automorphization of `f` times `g`. -/
lemma quotient_group.integral_mul_eq_integral_automorphize_mul {K : Type*} [normed_field K]
  [complete_space K] [normed_space ℝ K] [μ.is_mul_right_invariant] {f : G → K}
  (f_ℒ_1 : integrable f μ) {g : G ⧸ Γ → K} (hg : ae_strongly_measurable g μ_𝓕)
  (g_ℒ_infinity : ess_sup (λ x, ↑‖g x‖₊) μ_𝓕 ≠ ∞)
  (F_ae_measurable : ae_strongly_measurable (quotient_group.automorphize f) μ_𝓕) :
  ∫ x : G, g (x : G ⧸ Γ) * (f x) ∂μ = ∫ x : G ⧸ Γ, g x * (quotient_group.automorphize f x) ∂μ_𝓕 :=
begin
  let π : G → G ⧸ Γ := quotient_group.mk,
  have H₀ : quotient_group.automorphize ((g ∘ π) * f) = g * (quotient_group.automorphize f) :=
    quotient_group.automorphize_smul_left f g,
  calc ∫ (x : G), g (π x) * f x ∂μ =
       ∫ (x : G ⧸ Γ), quotient_group.automorphize ((g ∘ π) * f) x ∂μ_𝓕 : _
  ... = ∫ (x : G ⧸ Γ), g x * (quotient_group.automorphize f x) ∂μ_𝓕 : by simp [H₀],
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  have H₁ : integrable ((g ∘ π) * f) μ,
  { have : ae_strongly_measurable (λ x : G, g (x : G ⧸ Γ)) μ,
    { refine (ae_strongly_measurable_of_absolutely_continuous _ _ hg).comp_measurable meas_π,
      exact h𝓕.absolutely_continuous_map },
    refine integrable.ess_sup_smul f_ℒ_1 this _,
    { have hg' : ae_strongly_measurable (λ x, ↑‖g x‖₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_ae_strongly_measurable hg,
      rw [← ess_sup_comp_quotient_group_mk h𝓕 hg'.ae_measurable],
      exact g_ℒ_infinity } },
  have H₂ : ae_strongly_measurable (quotient_group.automorphize ((g ∘ π) * f)) μ_𝓕,
  { simp_rw [H₀],
    exact hg.mul F_ae_measurable },
  apply quotient_group.integral_eq_integral_automorphize h𝓕 H₁ H₂,
end

end

---- trying to additivize 4/14/23
 --- ALEX HOMEWORK

section

variables {G' : Type*} [add_group G'] [measurable_space G'] [topological_space G']
  [topological_add_group G'] [borel_space G']
  {μ' : measure G'}
  {Γ' : add_subgroup G'}
  {𝓕' : set G'} (h𝓕' : is_add_fundamental_domain Γ'.opposite 𝓕' μ')

local notation `μ_𝓕` := measure.map (@quotient_add_group.mk G' _ Γ') (μ'.restrict 𝓕')

/-- This is the **Unfolding Trick**: Given an additive subgroup `Γ'` of an additive group `G'`,

**** FIx

 the integral of a
  function `f` on `G'` times the lift to `G'` of a function `g` on the quotient `G' ⧸ Γ'` with respect
  to a right-invariant measure `μ` on `G'`, is equal to the integral over the quotient of the
  automorphization of `f` times `g`. -/
lemma quotient_add_group.integral_mul_eq_integral_automorphize_mul
{K : Type*} [normed_field K]
  [complete_space K] [normed_space ℝ K] [μ'.is_add_right_invariant] {f : G' → K}
  (f_ℒ_1 : integrable f μ') {g : G' ⧸ Γ' → K} (hg : ae_strongly_measurable g μ_𝓕)
  (g_ℒ_infinity : ess_sup (λ x, ↑‖g x‖₊) μ_𝓕 ≠ ∞)
  (F_ae_measurable : ae_strongly_measurable (quotient_add_group.automorphize f) μ_𝓕) :
  ∫ x : G', g (x : G' ⧸ Γ') * (f x) ∂μ' = ∫ x : G' ⧸ Γ', g x * (quotient_add_group.automorphize f x) ∂μ_𝓕 :=
begin
  let π : G' → G' ⧸ Γ' := quotient_add_group.mk,
  have H₀ : quotient_add_group.automorphize ((g ∘ π) * f) = g * (quotient_add_group.automorphize f) :=
    quotient_add_group.automorphize_smul_left f g,
  calc ∫ (x : G'), g (π x) * f x ∂μ' =
       ∫ (x : G' ⧸ Γ'), quotient_add_group.automorphize ((g ∘ π) * f) x ∂μ_𝓕 : _
  ... = ∫ (x : G' ⧸ Γ'), g x * (quotient_add_group.automorphize f x) ∂μ_𝓕 : by simp [H₀],
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  have H₁ : integrable ((g ∘ π) * f) μ',
  { have : ae_strongly_measurable (λ x : G', g (x : G' ⧸ Γ')) μ',
    { refine (ae_strongly_measurable_of_absolutely_continuous _ _ hg).comp_measurable meas_π,
      exact h𝓕'.absolutely_continuous_map },
    refine integrable.ess_sup_smul f_ℒ_1 this _,
    { have hg' : ae_strongly_measurable (λ x, ↑‖g x‖₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_ae_strongly_measurable hg,
      rw [← ess_sup_comp_quotient_add_group_mk h𝓕' hg'.ae_measurable],
      exact g_ℒ_infinity } },
  have H₂ : ae_strongly_measurable (quotient_add_group.automorphize ((g ∘ π) * f)) μ_𝓕,
  { simp_rw [H₀],
    exact hg.mul F_ae_measurable },
  apply quotient_add_group.integral_eq_integral_automorphize h𝓕' H₁ H₂,
end

end

-- add `attribute` pairing line (ALEX HOMEWORK)
