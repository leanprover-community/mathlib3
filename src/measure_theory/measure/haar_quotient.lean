/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import measure_theory.measure.haar
import measure_theory.group.fundamental_domain
import topology.compact_open
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

open set measure_theory topological_space

variables {G : Type*} [group G] [measurable_space G] [topological_space G] [t2_space G]
  [topological_group G] [borel_space G]
  {μ : measure G}
  {Γ : subgroup G}

variables [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)]

/-- Given a subgroup `Γ` of `G` and a right invariant measure `μ` on `G`, the measure is also
  invariant under the action of `Γ` on `G` by **right** multiplication -/
lemma subgroup.smul_invariant_measure (hμ : measure_theory.is_mul_right_invariant μ) :
  smul_invariant_measure Γ.opposite G μ :=
{ measure_preimage_smul :=
begin
  rintros ⟨c, hc⟩ s hs,
  dsimp [(•)],
  refine hμ.measure_preimage_mul (mul_opposite.unop c) s,
end}

variables {𝓕 : set G} (h𝓕 : is_fundamental_domain Γ.opposite 𝓕 μ)

section

-- FROM OTHER PR'ed BRANCH -- move to has_continuous_smul₂  file
class has_continuous_smul₂ (Γ : Type*) (T : Type*) [topological_space T] [has_scalar Γ T]
 : Prop :=
(continuous_smul₂ : ∀ γ : Γ, continuous (λ x : T, γ • x))

-- move to has_continuous_smul₂  file
export has_continuous_smul₂ (continuous_smul₂)

-- move to has_continuous_smul₂  file
instance quotient_group.has_continuous_smul₂ : has_continuous_smul₂ G (G ⧸ Γ) :=
{ continuous_smul₂ := λ g₀, begin
    apply continuous_coinduced_dom,
    change continuous (λ g : G, quotient_group.mk (g₀ * g)),
    exact continuous_coinduced_rng.comp (continuous_mul_left g₀),
  end }

-- move to has_continuous_smul₂  file
lemma quotient_group.continuous_smul₁ (x : G ⧸ Γ) : continuous (λ g : G, g • x) :=
begin
  obtain ⟨g₀, rfl⟩ : ∃ g₀, quotient_group.mk g₀ = x,
  { exact @quotient.exists_rep _ (quotient_group.left_rel Γ) x },
  change continuous (λ g, quotient_group.mk (g * g₀)),
  exact continuous_coinduced_rng.comp (continuous_mul_right g₀)
end

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
instance quotient_group.has_measurable_smul : has_measurable_smul G (G ⧸ Γ) :=
{ measurable_const_smul := λ g, (continuous_smul₂ g).measurable,
  measurable_smul_const := λ x, (quotient_group.continuous_smul₁ x).measurable }

end

include h𝓕
variables [encodable Γ]

/-- If `𝓕` is a fundamental domain for the action by right multiplication of a subgroup `Γ` of a
  topological group `G`, then its left-translate by an element of `g` is also a fundamental
  domain. -/
lemma measure_theory.is_fundamental_domain.smul (g : G)
  (hμL : measure_theory.is_mul_left_invariant μ):
  is_fundamental_domain ↥Γ.opposite (has_mul.mul g ⁻¹' 𝓕) μ :=
{ measurable_set := measurable_set_preimage (measurable_const_mul g) (h𝓕.measurable_set),
  ae_covers := begin
    let s := {x : G | ¬∃ (γ : ↥(Γ.opposite)), γ • x ∈ 𝓕},
    have μs_eq_zero : μ s = 0 := h𝓕.2,
    change μ {x : G | ¬∃ (γ : ↥(Γ.opposite)), g * γ • x ∈ 𝓕} = 0,
    have : {x : G | ¬∃ (γ : ↥(Γ.opposite)), g * γ • x ∈ 𝓕} = has_mul.mul g ⁻¹' s,
    { ext,
      simp [s, left_right_mul], },
    rw [this, hμL.measure_preimage_mul g s, μs_eq_zero],
  end,
  ae_disjoint := begin
    intros γ γ_ne_one,
    have μs_eq_zero : μ (((λ x, γ • x) '' 𝓕) ∩ 𝓕) = 0 := h𝓕.3 γ γ_ne_one,
    change μ (((λ x, γ • x) '' (has_mul.mul g ⁻¹' 𝓕)) ∩ (has_mul.mul g ⁻¹' 𝓕)) = 0,
    have : ((λ x, γ • x) '' (has_mul.mul g ⁻¹' 𝓕)) ∩ (has_mul.mul g ⁻¹' 𝓕) =
      has_mul.mul g ⁻¹' (((λ x, γ • x) '' 𝓕) ∩ 𝓕),
    { ext,
      simp only [mem_inter_eq, image_smul, and.congr_left_iff, mem_preimage],
      intros gx,
      convert left_right_mem_preimage x g γ 𝓕, },
    rw [this, hμL.measure_preimage_mul g _, μs_eq_zero],
  end }

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
lemma measure_theory.is_fundamental_domain.smul_invariant_measure_map
  (hμL : measure_theory.is_mul_left_invariant μ) (hμR : measure_theory.is_mul_right_invariant μ) :
  smul_invariant_measure G (G ⧸ Γ) (measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)) :=
{ measure_preimage_smul :=
  begin
    let π : G → G ⧸ Γ := @quotient_group.mk G _ Γ ,
    have meas_π : measurable π :=
      continuous.measurable continuous_quotient_mk,
    have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
    intros g A hA,
    have meas_πA : measurable_set (π ⁻¹' A) := measurable_set_preimage meas_π hA,
    rw [measure.map_apply meas_π hA,
      measure.map_apply meas_π (measurable_set_preimage (measurable_const_smul g) hA),
      measure.restrict_apply' 𝓕meas, measure.restrict_apply' 𝓕meas],
    set π_preA := π ⁻¹' A,
    have : (quotient_group.mk ⁻¹' ((λ (x : G ⧸ Γ), g • x) ⁻¹' A)) = has_mul.mul g ⁻¹' π_preA :=
      by ext1; simp,
    rw this,
    have : μ (has_mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ has_mul.mul (g⁻¹) ⁻¹' 𝓕),
    { transitivity μ (has_mul.mul g ⁻¹' (π_preA ∩ has_mul.mul g⁻¹ ⁻¹' 𝓕)),
      { rw preimage_inter,
        congr,
        rw [← preimage_comp, comp_mul_left, mul_left_inv],
        ext,
        simp, },
      rw hμL.measure_preimage_mul, },
    rw this,
    have h𝓕_translate_fundom : is_fundamental_domain Γ.opposite (has_mul.mul g⁻¹ ⁻¹' 𝓕) μ :=
      h𝓕.smul (g⁻¹) hμL,
    haveI : smul_invariant_measure ↥(Γ.opposite) G μ := subgroup.smul_invariant_measure hμR,
    rw h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA,
    rintros ⟨γ, γ_in_Γ⟩,
    ext,
    have : π (x * (mul_opposite.unop γ)) = π (x) := by simpa [quotient_group.eq'] using γ_in_Γ,
    simp [(•), this],
  end }

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
lemma measure_theory.is_fundamental_domain.is_mul_left_invariant_map [subgroup.normal Γ]
  (hμL : measure_theory.is_mul_left_invariant μ) (hμR : measure_theory.is_mul_right_invariant μ) :
  is_mul_left_invariant (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)) :=
begin
  intros x A hA,
  obtain ⟨x₁, _⟩ := @quotient.exists_rep _ (quotient_group.left_rel Γ) x,
  haveI := h𝓕.smul_invariant_measure_map hμL hμR,
  convert measure_preimage_smul x₁ ((measure.map quotient_group.mk) (μ.restrict 𝓕)) A,
  rw ← h,
  refl,
end


variables [t2_space (G ⧸ Γ)] [topological_space.second_countable_topology (G ⧸ Γ)]

variables (K : topological_space.positive_compacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G/Γ`. -/
lemma measure_theory.is_fundamental_domain.map_restrict_quotient [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] (hμR : measure_theory.is_mul_right_invariant μ)
  (h𝓕_finite : μ 𝓕 < ⊤) : measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)
  = (μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K.val)) • (measure_theory.measure.haar_measure K) :=
begin
  let π : G →* G ⧸ Γ := quotient_group.mk' Γ,
  have meas_π : measurable π :=
    continuous.measurable continuous_quotient_mk, -- projection notation doesn't work here?
  have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by { rw [measure.restrict_apply' 𝓕meas, univ_inter], exact h𝓕_finite }⟩,
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  rw [measure.haar_measure_unique (h𝓕.is_mul_left_invariant_map
    (measure_theory.measure.is_mul_left_invariant_haar μ) hμR) K,
    measure.map_apply meas_π, measure.restrict_apply' 𝓕meas, inter_comm],
  exact K.prop.1.measurable_set,
end
