/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import algebra.group.opposite
import analysis.normed_space.lp_space
import measure_theory.group.fundamental_domain
import measure_theory.integral.integral_eq_improper
import measure_theory.measure.haar
import topology.compact_open
import measure_theory.function.strongly_measurable_supr
--- should be `.supr`

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

open measure_theory
open_locale measure_theory

@[to_additive ae_strongly_measurable_of_absolutely_continuous_add]
lemma ae_strongly_measurable_of_absolutely_continuous {α β : Type*} [measurable_space α]
  [topological_space β] {μ ν : measure α} (h : ν ≪ μ) (g : α → β)
  (hμ : ae_strongly_measurable g μ) : ae_strongly_measurable g ν :=
begin
  obtain ⟨g₁, hg₁, hg₁'⟩ := hμ,
  refine ⟨g₁, hg₁, h.ae_eq hg₁'⟩,
end

open_locale big_operators nnreal

noncomputable theory

open_locale topological_space

-- note: flip `measure_theory.ae_lt_top` and `measure_theory.ae_lt_top'`

-- move to `measure_theory.constructions.borel_space` next to `measurable.coe_nnreal_ennreal`
theorem strongly_measurable.coe_nnreal_ennreal {α : Type*} [measurable_space α]
  {f : α → nnreal} (hf : strongly_measurable f) :
strongly_measurable (λ (x : α), (f x : ennreal)) := ennreal.continuous_coe.comp_strongly_measurable hf

theorem strongly_measurable.coe_nnreal_real {α : Type*} [measurable_space α]
  {f : α → nnreal} (hf : strongly_measurable f) :
strongly_measurable (λ (x : α), (f x : real)) := nnreal.continuous_coe.comp_strongly_measurable hf

-- move to `measure_theory.constructions.borel_space` next to `ae_measurable.coe_nnreal_ennreal`
theorem ae_strongly_measurable.coe_nnreal_ennreal {α : Type*} [measurable_space α]
  {f : α → nnreal} {μ : measure_theory.measure α} (hf : ae_strongly_measurable f μ) :
ae_strongly_measurable (λ (x : α), (f x : ennreal)) μ := ennreal.continuous_coe.comp_ae_strongly_measurable hf

theorem ae_strongly_measurable.coe_nnreal_real {α : Type*} [measurable_space α]
  {f : α → nnreal} {μ : measure_theory.measure α} (hf : ae_strongly_measurable f μ) :
ae_strongly_measurable (λ (x : α), (f x : real)) μ := nnreal.continuous_coe.comp_ae_strongly_measurable hf

--- remind me, why not `measure_theory.integral_integral` and tsum as integral? Not now...
/-- THIS IS WHERE WE STOPPED ON 11/2/22 -/
lemma measure_theory.integral_tsum {α : Type*} {β : Type*} {m : measurable_space α}
  {μ : measure_theory.measure α} [encodable β] {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E]
  {f : β → α → E}
  (hf : ∀ (i : β), ae_strongly_measurable (f i) μ)
  (hf' : ∑' (i : β), ∫⁻ (a : α), ∥f i a∥₊ ∂μ ≠ ⊤) :
  ∫ (a : α), (∑' (i : β), f i a) ∂μ = ∑' (i : β), ∫ (a : α), f i a ∂μ :=
begin
  have hf'' := (λ i, (hf i).ae_measurable.nnnorm.coe_nnreal_ennreal),
  have hhh : ∀ᵐ (a : α) ∂μ, summable (λ (n : β), (∥f n a∥₊ : ℝ)),
  { haveI : countable β := sorry,
    rw ← lintegral_tsum hf'' at hf',
    refine (ae_lt_top' (ae_measurable.ennreal_tsum hf'') hf').mono _,
    intros x hx,
    rw ← ennreal.tsum_coe_ne_top_iff_summable_coe,
    exact hx.ne, },
  convert (measure_theory.has_sum_integral_of_dominated_convergence (λ i a, ∥f i a∥₊) hf _
    hhh _ _).tsum_eq.symm,
  { intros n,
    filter_upwards with x,
    refl, },
  { split,
    { simp_rw [← coe_nnnorm, ← nnreal.coe_tsum],
      apply ae_strongly_measurable.coe_nnreal_real,
      apply ae_strongly_measurable.nnreal_tsum,
      exact (λ i, (hf i).nnnorm), },
    { dsimp [has_finite_integral],
      have : ∫⁻ (a : α), ∑' (n : β), ∥f n a∥₊ ∂μ < ⊤,
      { rw [lintegral_tsum, lt_top_iff_ne_top],
        { exact hf', },
        { exact_mod_cast λ i, (hf i).ae_measurable.nnnorm, }, },
      convert this using 1,
      apply lintegral_congr_ae,
      simp_rw [← coe_nnnorm, ← nnreal.coe_tsum, nnreal.nnnorm_eq],
      filter_upwards [hhh] with a ha,
      exact ennreal.coe_tsum (nnreal.summable_coe.mp ha), }, },
  { filter_upwards [hhh] with x hx,
    exact (summable_of_summable_norm hx).has_sum, },
end

open_locale ennreal

open measure_theory

-- move to facts about integrable functions
lemma integrable.mul_ℒ_infinity  {G : Type*} {E : Type*} [normed_ring E] [normed_algebra ℝ E]
  [measurable_space E] [borel_space E] [has_measurable_mul₂ E] [measurable_space G]
  {μ : measure G}
  (f : G → E)
  (f_ℒ_1 : integrable f μ)
  (g : G → E)
  (g_measurable : ae_strongly_measurable g μ)
  (g_ℒ_infinity : ess_sup (λ x, (∥g x∥₊ : ℝ≥0∞)) μ < ∞) :
  integrable (λ (x : G), f x * g x) μ :=
begin
  let s : set ℝ≥0∞ := {a : ℝ≥0∞ | μ {x : G | a < (λ (x : G), ↑∥g x∥₊) x} = 0},
  have : ess_sup (λ x, (∥g x∥₊ : ℝ≥0∞)) μ = Inf s := ess_sup_eq_Inf _ _,
  obtain ⟨a₀, has : μ _ = 0, ha₀⟩ : ∃ (a : ℝ≥0∞) (H : a ∈ s), a < ⊤,
  { rw ← Inf_lt_iff,
    rw ← ess_sup_eq_Inf,
    exact g_ℒ_infinity },
  rw ennreal.lt_iff_exists_coe at ha₀,
  obtain ⟨a, rfl, -⟩ := ha₀,
  rw integrable at f_ℒ_1 ⊢,
  rw measure_theory.has_finite_integral_iff_norm at f_ℒ_1 ⊢,
  refine ⟨f_ℒ_1.1.mul g_measurable, _⟩,
  calc ∫⁻ (x : G), ennreal.of_real (∥f x * g x∥) ∂μ ≤
    ∫⁻ (x : G), ennreal.of_real (∥f x∥ * ∥g x∥) ∂μ : _
    ... ≤  ∫⁻ (x : G), ennreal.of_real (∥f x∥ * a) ∂μ : _
    ... =  ∫⁻ (x : G), (ennreal.of_real (∥f x∥) * a) ∂μ : _
    ... = ∫⁻ (x : G), ennreal.of_real (∥f x∥) ∂μ * a : _
    ... < ⊤ : _ ,
  { mono,
    { exact rfl.le, },
    { intros x,
      apply ennreal.of_real_le_of_real,
      exact norm_mul_le _ _, }, },
  { apply measure_theory.lintegral_mono_ae,
    rw ← compl_mem_ae_iff at has,
    filter_upwards [has] with x hx,
    apply ennreal.of_real_le_of_real,
    refine mul_le_mul rfl.le _ (norm_nonneg _) (norm_nonneg _),
    exact_mod_cast le_of_not_lt hx },
  { congr,
    ext1 x,
    rw ennreal.of_real_mul,
    { simp },
    { exact norm_nonneg _ } },
  { refine measure_theory.lintegral_mul_const'' _ (ae_strongly_measurable.ae_measurable _),
    exact (ennreal.continuous_of_real.comp continuous_norm).comp_ae_strongly_measurable f_ℒ_1.1 },
  { apply ennreal.mul_lt_top f_ℒ_1.2.ne,
    simp, }
end

open set measure_theory topological_space measure_theory.measure
open_locale pointwise nnreal

variables {G : Type*} [group G] [measurable_space G] [topological_space G]
  [topological_group G] [borel_space G]
  (μ : measure G)
  (Γ : subgroup G)

/-- Given a subgroup `Γ` of `G` and a right invariant measure `μ` on `G`, the measure is also
  invariant under the action of `Γ` on `G` by **right** multiplication. -/
@[to_additive "Given a subgroup `Γ` of an additive group `G` and a right invariant measure `μ` on
  `G`, the measure is also invariant under the action of `Γ` on `G` by **right** addition."]
instance subgroup.smul_invariant_measure [μ.is_mul_right_invariant] :
  smul_invariant_measure Γ.opposite G μ :=
{ measure_preimage_smul :=
begin
  rintros ⟨c, hc⟩ s hs,
  dsimp [(•)],
  refine measure_preimage_mul_right μ (mul_opposite.unop c) s,
end}

variables {Γ} {μ}

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
    haveI : smul_invariant_measure G G μ := ⟨λ c s hs, measure_preimage_mul μ c s⟩,
    -- Lean can generate the next instance but it has no additive version of the autogenerated proof
    haveI : smul_comm_class G Γ.opposite G := ⟨λ a b c, (mul_assoc _ _ _).symm⟩,
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

variables [t2_space (G ⧸ Γ)] [second_countable_topology (G ⧸ Γ)] (K : positive_compacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.map_restrict_quotient [subgroup.normal Γ]
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
lemma measure_preserving_quotient_group.mk' [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] [μ.is_mul_right_invariant]
  (h𝓕_finite : μ 𝓕 < ⊤) (c : ℝ≥0) (h : μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K) = c) :
  measure_preserving
    (quotient_group.mk' Γ)
    (μ.restrict 𝓕)
    (c • (measure_theory.measure.haar_measure K)) :=
{ measurable := continuous_quotient_mk.measurable,
  map_eq := by rw [h𝓕.map_restrict_quotient K h𝓕_finite, h]; refl }


---------------------------- UNFOLDING TRICK ---------------

open_locale big_operators ennreal

local notation `μ_𝓕` := measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)

@[simp] lemma subgroup_mem_opposite_iff (γ : Gᵐᵒᵖ) : γ ∈ Γ.opposite ↔ mul_opposite.unop γ ∈ Γ :=
by simp [subgroup.opposite]

@[to_additive]
lemma mul_ess_sup_of_g [μ.is_mul_right_invariant] (g : G ⧸ Γ → ℝ≥0∞)
  (g_measurable : ae_measurable g μ_𝓕) :
  ess_sup g μ_𝓕 = ess_sup (λ (x : G), g x) μ :=
begin
  have hπ : measurable (quotient_group.mk : G → G ⧸ Γ) := continuous_quotient_mk.measurable,
  rw ess_sup_map_measure g_measurable hπ.ae_measurable,
  refine h𝓕.ess_sup_measure_restrict _,
  rintros ⟨γ, hγ⟩ x,
  dsimp,
  congr' 1,
  exact quotient_group.mk_mul_of_mem x (mul_opposite.unop γ) hγ,
end


@[to_additive]
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
    convert quotient_group.mk_mul_of_mem g (mul_opposite.unop (γ⁻¹)) (γ⁻¹).2, },
  exact measurable_set_preimage meas_π s_meas,
end


omit h𝓕
local attribute [-instance] quotient.measurable_space

--- move to ` asdf `???
/-- Given a group `α` acting on a type `β`, and a function `f : β → γ`, we "automorphize" `f` to a
  function `β ⧸ α → γ` by summing over `α` orbits, `b ↦ ∑' (a : α), f(a • b)`. -/
@[to_additive]
def mul_action.automorphize {α : Type*} {β : Type*} [group α] [mul_action α β] {γ : Type*}
  [topological_space γ] [add_comm_monoid γ] [t2_space γ] (f : β → γ) :
  quotient (mul_action.orbit_rel α β) → γ :=
@quotient.lift _ _ (mul_action.orbit_rel α β) (λ b, ∑' (a : α), f(a • b))
begin
  rintros b₁ b₂ ⟨a, (rfl : a • b₂ = b₁)⟩,
  simpa [mul_smul] using (equiv.mul_right a).tsum_eq (λ a', f (a' • b₂)),
end


lemma measurable_lift {α : Type*} {β : Type*} [group α] [mul_action α β] [measurable_space β]
  [topological_space β] [borel_space β] {γ : Type*} [measurable_space γ]
  [measurable_space (quotient (mul_action.orbit_rel α β))]
  [borel_space (quotient (mul_action.orbit_rel α β))]
  (f : β → γ)
  (f_invariant : (∀ (a b : β), (mul_action.orbit_rel α β).r a b → f a = f b)) (hf : measurable f) :
  measurable (@quotient.lift _ _ (mul_action.orbit_rel α β) f f_invariant) :=
begin
  intros s s_meas,
  dsimp [measurable_set],
  sorry,
end


--def automorphize' {α : Type*} (f : G → ℂ) : G ⧸ Γ → ℂ := mul_action.automorphize f

--omit h𝓕

lemma automorphize.ae_strongly_measurable [μ.is_mul_right_invariant] (f : G → ℂ)
  (f_ae_sm : ae_strongly_measurable f μ) :
  ae_strongly_measurable (mul_action.automorphize f) μ_𝓕 :=
begin

end

include h𝓕

/-- This is the "unfolding" trick
PROOF:
∫_G f = ∑_γ ∫_𝓕 f(γ⁻¹ • x ) : h𝓕.integral_eq_tsum'
... = ∫_𝓕  ∑_γ  f(γ⁻¹ • x ) : integral_tsum (to be PRed)
... = ∫_𝓕  F ∘ π  : def of F
... = ∫_(G/Γ) F
 -/
@[to_additive]
lemma mul_unfolding_trick' [μ.is_mul_right_invariant] (f : G → ℂ) (f_ℒ_1 : integrable f μ)
  (F : G ⧸ Γ → ℂ)
  (F_ae_measurable : ae_strongly_measurable F μ_𝓕) -- NEEDED?? or can be proved?
  (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x ∂μ = ∫ (x : G ⧸ Γ), F x ∂μ_𝓕 :=
begin
  haveI : encodable Γ := encodable.of_countable Γ,
  set π : G → G ⧸ Γ := quotient_group.mk,
  calc ∫ (x : G), f x ∂μ  = ∑' (γ : Γ.opposite), ∫ x in 𝓕, f(γ • x) ∂μ :
    h𝓕.integral_eq_tsum'' f f_ℒ_1
  ... = ∫ x in 𝓕, ∑' (γ : Γ.opposite), f(γ • x) ∂μ : _
  ... = ∫ x in 𝓕, F (π x) ∂μ : _
  ... = ∫ (x : G ⧸ Γ), F x ∂μ_𝓕 :
    (integral_map (continuous_quotient_mk.ae_measurable : ae_measurable π (μ.restrict 𝓕))
      F_ae_measurable).symm,
  { rw integral_tsum,
    { exact λ i, (f_ℒ_1.1.comp_quasi_measure_preserving
        (measure_preserving_smul i μ).quasi_measure_preserving).restrict, },
    { rw ← h𝓕.lintegral_eq_tsum'' (λ x, ∥f (x)∥₊),
      exact ne_of_lt f_ℒ_1.2, }, },
  { congr,
    ext1 x,
    exact (hFf x).symm, },
end

--- STOPPED 2/06/23.

/-- This is the "unfolding" trick -/
@[to_additive]
lemma mul_unfolding_trick [μ.is_mul_right_invariant]
  {f : G → ℂ}
  (f_ℒ_1 : integrable f μ)
  {g : G ⧸ Γ → ℂ}
  (hg : ae_strongly_measurable g μ_𝓕)
  (g_ℒ_infinity : ess_sup (λ x, ↑∥g x∥₊) μ_𝓕 < ∞)
  {F : G ⧸ Γ → ℂ}
  (F_ae_measurable : ae_strongly_measurable F μ_𝓕) -- NEEDED??
  (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x * g (x : G ⧸ Γ) ∂μ = ∫ (x : G ⧸ Γ), F x * g x ∂μ_𝓕 :=
begin
  let π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  refine mul_unfolding_trick' h𝓕 (f * (g ∘ (coe : G → G ⧸ Γ))) _ (F * g) (F_ae_measurable.mul hg) _,
  { refine integrable.mul_ℒ_infinity f f_ℒ_1 (λ x : G, g (x : G ⧸ Γ)) _ _,
    { exact (ae_strongly_measurable_of_absolutely_continuous h𝓕.absolutely_continuous_map _
        hg).comp_measurable meas_π, },
    { have hg' : ae_strongly_measurable (λ x, ↑∥g x∥₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_ae_strongly_measurable hg,
      rw [← mul_ess_sup_of_g h𝓕 (λ x, ↑∥g x∥₊) hg'.ae_measurable],
      exact g_ℒ_infinity, }, },
  { intros x,
    rw [hFf x, ← tsum_mul_right],
    congr,
    ext1 γ,
    congr' 2,
    obtain ⟨γ₀, hγ₀⟩ := γ,
    simpa [quotient_group.eq, (•)] using hγ₀, },
end
