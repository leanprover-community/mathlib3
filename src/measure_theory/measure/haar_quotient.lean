/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import measure_theory.measure.haar
import measure_theory.group.fundamental_domain
import topology.compact_open

/-!
# Haar Quotient measure

In this file does stuff.

## Main results

* `measure_theory.is_fundamental_domain.smul_invariant_measure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of `G`'s
  Haar measure to a fundamental domain of `Γ` is a `G`-invariant measure on `G ⧸ Γ`.

* `measure_theory.is_fundamental_domain.is_mul_left_invariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  `G`'s Haar measure to a fundamental domain of `Γ` is a left-invariant measure on `G ⧸ Γ`.
-/

open set measure_theory

variables {G : Type*} [group G] [measurable_space G] [topological_space G] [t2_space G]
  [topological_group G] [borel_space G]
  {μ : measure G} [measure_theory.measure.is_haar_measure μ]
  {Γ : subgroup G} --[subgroup.normal Γ]
  {𝓕 : set G} (h𝓕 : is_fundamental_domain Γ 𝓕 μ)

variables [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)]

instance subgroup.smul_invariant_measure : smul_invariant_measure Γ G μ :=
{ measure_preimage_smul := λ c s hs, μ.haar_preimage_mul c s }

section
/-! First method to get `has_measurable_smul G (G ⧸ Γ)`.

More elegant but apparently requires local compactness of `G`?? -/

-- move this to basic topology
-- not clear if the `locally_compact_space` hypothesis here is really necessary
lemma foo {X₀ X Y Z : Type*} [t₀ : topological_space X₀] [topological_space X]
  [topological_space Y] [topological_space Z] [locally_compact_space Y] {f : X₀ → X}
  (hf : quotient_map f) {g : X × Y → Z} (hg : continuous (λ p : X₀ × Y, g (f p.1, p.2))) :
  continuous g :=
begin
  let Gf : C(X₀, C(Y, Z)) := continuous_map.curry ⟨_, hg⟩,
  have h : ∀ x : X, continuous (λ y, g (x, y)),
  { intros x,
    obtain ⟨x₀, rfl⟩ := hf.surjective x,
    exact (Gf x₀).continuous },
  let G : X → C(Y, Z) := λ x, ⟨_, h x⟩,
  have : continuous G,
  { rw hf.continuous_iff,
    exact Gf.continuous },
  convert continuous_map.continuous_uncurry_of_continuous ⟨G, this⟩,
  ext x,
  cases x,
  refl,
end

-- move this
lemma foo' {X₀ X Y Z : Type*} [t₀ : topological_space X₀] [topological_space X]
  [topological_space Y] [topological_space Z] [locally_compact_space Y] {f : X₀ → X}
  (hf : quotient_map f) {g : Y × X → Z} (hg : continuous (λ p : Y × X₀, g (p.1, f p.2))) :
  continuous g :=
begin
  have : continuous (λ p : X₀ × Y, g ((prod.swap p).1, f (prod.swap p).2)),
  { exact hg.comp continuous_swap },
  have : continuous (λ p : X₀ × Y, (g ∘ prod.swap) (f p.1, p.2)) := this,
  convert (foo hf this).comp continuous_swap,
  ext x,
  simp,
end

-- move this
lemma quotient_group.quotient_map : quotient_map (quotient_group.mk : G → G ⧸ Γ) :=
⟨quotient.surjective_quotient_mk', by refl⟩

instance quotient_group.has_continuous_smul [locally_compact_space G] :
  has_continuous_smul G (G ⧸ Γ) :=
{ continuous_smul := begin
    let F : G × G ⧸ Γ → G ⧸ Γ := λ p, p.1 • p.2,
    change continuous F,
    have H : continuous (F ∘ (λ p : G × G, (p.1, quotient_group.mk p.2))),
    { change continuous (λ p : G × G, quotient_group.mk (p.1 * p.2)),
      refine continuous_coinduced_rng.comp continuous_mul },
    exact foo' quotient_group.quotient_map H
  end }

-- `has_measurable_smul` follows for locally compact `G`

end

section
/-! Second method to get `has_measurable_smul G (G ⧸ Γ)`. -/

-- FROM OTHER PR'ed BRANCH
class has_continuous_smul₂ (Γ : Type*) (T : Type*) [topological_space T] [has_scalar Γ T]
 : Prop :=
(continuous_smul₂ : ∀ γ : Γ, continuous (λ x : T, γ • x))

export has_continuous_smul₂ (continuous_smul₂)

instance quotient_group.has_continuous_smul₂ : has_continuous_smul₂ G (G ⧸ Γ) :=
{ continuous_smul₂ := λ g₀, begin
    apply continuous_coinduced_dom,
    change continuous (λ g : G, quotient_group.mk (g₀ * g)),
    exact continuous_coinduced_rng.comp (continuous_mul_left g₀),
  end }

-- stupid name, fix
lemma quotient_group.continuous_smul₁ (x : G ⧸ Γ) : continuous (λ g : G, g • x) :=
begin
  obtain ⟨g₀, rfl⟩ : ∃ g₀, quotient_group.mk g₀ = x,
  { exact @quotient.exists_rep _ (quotient_group.left_rel Γ) x },
  change continuous (λ g, quotient_group.mk (g * g₀)),
  exact continuous_coinduced_rng.comp (continuous_mul_right g₀)
end

instance quotient_group.has_measurable_smul : has_measurable_smul G (G ⧸ Γ) :=
{ measurable_const_smul := λ g, (continuous_smul₂ g).measurable,
  measurable_smul_const := λ x, (quotient_group.continuous_smul₁ x).measurable }

end

include h𝓕
variables [encodable Γ]

lemma measure_theory.is_fundamental_domain.smul (g : G) :
  is_fundamental_domain ↥Γ (has_mul.mul g ⁻¹' 𝓕) μ :=
{ measurable_set := _,
  ae_covers := _,
  ae_disjoint := _ }

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of Haar measure on `G` to a
fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
lemma measure_theory.is_fundamental_domain.smul_invariant_measure_map :
  smul_invariant_measure G (G ⧸ Γ) (measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)) :=
{ measure_preimage_smul :=
  begin
    let π : G → G ⧸ Γ := @quotient_group.mk G _ Γ ,
    have meas_π : measurable π :=
      continuous.measurable continuous_quotient_mk, -- projection notation doesn't work here?
    have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
    intros g A hA,
    have meas_πA : measurable_set (π ⁻¹' A) := measurable_set_preimage meas_π hA,
    rw [measure.map_apply meas_π hA],
    rw measure.map_apply meas_π (measurable_set_preimage (measurable_const_smul g) hA),
    rw measure.restrict_apply' 𝓕meas,
    rw measure.restrict_apply' 𝓕meas,
    -- step1: get x1 ∈ 𝓕 with π(x1)=x
    set π_preA := π ⁻¹' A,
    rw (by ext1 y; simp :
      (quotient_group.mk ⁻¹' ((λ (x : G ⧸ Γ), g • x) ⁻¹' A))
      = has_mul.mul g ⁻¹' π_preA),

    have : μ (has_mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ has_mul.mul (g⁻¹) ⁻¹' 𝓕),
    { transitivity μ (has_mul.mul g ⁻¹' (π_preA ∩ has_mul.mul g⁻¹ ⁻¹' 𝓕)),
      { rw preimage_inter,
        congr,
        rw [← preimage_comp, comp_mul_left, mul_left_inv],
        ext,
        simp, },
      rw is_mul_left_invariant.measure_preimage_mul,
      exact measure.is_mul_left_invariant_haar μ, },
    rw this,

    have h𝓕_translate_fundom : is_fundamental_domain Γ (has_mul.mul g⁻¹ ⁻¹' 𝓕) μ := h𝓕.smul (g⁻¹),

    rw h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA,

    intros γ, -- ALEX Homework
    ext,
    split,
    { intros x_in_preA,
      rw mem_preimage at x_in_preA,
      rw mem_preimage at x_in_preA,
      rw mem_preimage,
      convert x_in_preA using 1,
      rw quotient_group.eq',
      -- seems to require `Γ` normal?
      sorry,
    },
    { intros x_in_preA,
      rw mem_preimage at x_in_preA,
      rw mem_preimage,
      rw mem_preimage,
      convert x_in_preA using 1,
      rw quotient_group.eq',
      -- seems to require `Γ` normal?
      sorry,
    },
  end }

/-- The pushforward to the quotient group `G ⧸ Γ` of the restriction of Haar measure on `G` to a
fundamental domain `𝓕` is a left-invariant measure on the group `G ⧸ Γ`. -/
lemma measure_theory.is_fundamental_domain.is_mul_left_invariant_map [subgroup.normal Γ] :
  is_mul_left_invariant (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)) :=
begin
  intros x A hA,
  obtain ⟨x₁, _⟩ := @quotient.exists_rep _ (quotient_group.left_rel Γ) x,
  haveI := h𝓕.smul_invariant_measure_map,
  convert measure_theory.measure_preimage_smul x₁ ((measure.map quotient_group.mk) (μ.restrict 𝓕)) A,
  rw ← h,
  refl,
end

variables [t2_space (G ⧸ Γ)] [topological_space.second_countable_topology (G ⧸ Γ)]
 -- prove t2, prove second_countability, (from discreteness?)

variables (K : topological_space.positive_compacts (G ⧸ Γ))

local notation `μ_X` := measure_theory.measure.haar_measure K

lemma map_restrict_unit_interval [subgroup.normal Γ] (h𝓕_finite : μ 𝓕 < ⊤) :
  measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)
  = (μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K.val)) • μ_X :=
begin
  let π : G →* G ⧸ Γ := quotient_group.mk' Γ,
  have meas_π : measurable π :=
    continuous.measurable continuous_quotient_mk, -- projection notation doesn't work here?
  have 𝓕meas : measurable_set 𝓕 := h𝓕.measurable_set,
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by { rw [measure.restrict_apply' 𝓕meas, univ_inter], exact h𝓕_finite }⟩,
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  rw [measure.haar_measure_unique h𝓕.is_mul_left_invariant_map K,
        measure.map_apply meas_π, measure.restrict_apply' 𝓕meas, inter_comm],
  exact K.prop.1.measurable_set
end


/- JUNK BIN

noncomputable def int.fract (a : ℝ) : ℝ := a - floor a

theorem int.fract_nonneg (a : ℝ) :
0 ≤ int.fract a := sorry

theorem int.fract_lt_one (a : ℝ) :
int.fract a < 1 := sorry

lemma min_cases {α : Type*} [linear_order α] (a b : α) :
min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := sorry

lemma max_cases {α : Type*} [linear_order α] (a b : α) :
max a b = b ∧ a ≤ b ∨ max a b = a ∧ b < a := sorry

instance : separated_space (metric.sphere (0:ℝ) 1) := to_separated

theorem disjoint.inter {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
disjoint (u ∩ s) (u ∩ t) :=
begin
  apply disjoint.inter_right',
  apply disjoint.inter_left',
  exact h,
end

theorem disjoint.inter' {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
disjoint (s ∩ u) (t ∩ u) :=
begin
  apply disjoint.inter_left,
  apply disjoint.inter_right,
  exact h,
end


  -- take the subinterval of π_preA in [x1,1)
  let A1 := π_preA ∩ Ico x1 1,
  have A1meas : measurable_set A1 := measurable_set.inter (measurable_set_preimage meas_π hA)
    measurable_set_Ico,
  -- and the rest is in [0,x1)
  let A2 := π_preA ∩ Ico 0 x1,
  have A2meas : measurable_set A2 := measurable_set.inter (measurable_set_preimage meas_π hA)
    measurable_set_Ico,
  have A1A2dis : disjoint A1 A2,
  { apply disjoint.inter,
    rw Ico_disjoint_Ico,
    cases (min_cases 1 x1); cases (max_cases x1 0); linarith, },
  have A1A2 : π_preA ∩ 𝓕 = A1 ∪ A2,
  { convert inter_union_distrib_left using 2,
    rw union_comm,
    refine (Ico_union_Ico_eq_Ico _ _).symm; linarith, },
  -- under (-x1), A1 is moved into [0,1-x1)
  let B1 : set ℝ :=  has_add.add x1 ⁻¹' A1,
  have B1meas : measurable_set B1 := measurable_set_preimage (measurable_const_add _) A1meas,
  -- and A2 is moved into [1-x1,1), up to translation by 1
  let B2 : set ℝ := has_add.add (x1-1) ⁻¹' A2,
  have B2meas : measurable_set B2 := measurable_set_preimage (measurable_const_add _) A2meas,
  have B1B2dis : disjoint B1 B2,
  { have B1sub : B1 ⊆ has_add.add x1 ⁻¹' (Ico x1 1) :=
      preimage_mono (π_preA.inter_subset_right _),
    have B2sub : B2 ⊆ has_add.add (x1-1) ⁻¹' (Ico 0 x1) :=
      preimage_mono (π_preA.inter_subset_right _),
    refine disjoint_of_subset B1sub B2sub _,
    rw [preimage_const_add_Ico, preimage_const_add_Ico, Ico_disjoint_Ico],
    cases min_cases (1-x1) (x1 - (x1 - 1)); cases max_cases (x1 - x1) (0 - (x1 - 1)); linarith, },
  have B1B2 : π_prexA ∩ 𝓕 = B1 ∪ B2,
  { have B1is : has_add.add x1 ⁻¹' π_preA ∩ Ico 0 (1 - x1) = B1 :=
      by simp [B1],
    have B2is : has_add.add x1 ⁻¹' π_preA ∩ Ico (1 - x1) 1 = B2,
    { calc has_add.add x1 ⁻¹' π_preA ∩ Ico (1 - x1) 1
          = has_add.add (x1 - 1) ⁻¹' π_preA ∩ Ico (1 - x1) 1 : _
      ... = B2 : by simp [B2],
      congr' 1,
      ext1 y,
      have : π 1 = 0 := by simpa using π_of_Γ 1,
      simp [this], },
    have : 𝓕 = Ico 0 (1-x1) ∪ (Ico (1-x1) 1) := by rw Ico_union_Ico_eq_Ico; linarith,
    rw [two_quotients, this, inter_distrib_left, B1is, B2is], },
  rw [measure_theory.measure.restrict_apply' 𝓕meas,
    measure_theory.measure.restrict_apply' 𝓕meas,
    A1A2, B1B2, measure_theory.measure_union B1B2dis B1meas B2meas,
    measure_theory.measure_union A1A2dis A1meas A2meas,
    real.volume_preimage_add_left, real.volume_preimage_add_left],

-/
