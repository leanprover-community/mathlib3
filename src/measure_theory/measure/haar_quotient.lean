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

-----

theorem ae_strongly_measurable.is_lub {α : Type*} {δ : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [measurable_space δ] [linear_order α] [order_topology α]
  [topological_space.second_countable_topology α] {ι : Sort*} {μ : measure_theory.measure δ}
  [countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ)
  (hg : ∀ᵐ (b : δ) ∂μ, is_lub {a : α | ∃ (i : ι), f i b = a} (g b)) :
ae_strongly_measurable g μ := sorry

@[measurability]
theorem ae_strongly_measurable_supr {α : Type*} {δ : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [measurable_space δ] [complete_linear_order α]
  [order_topology α] [topological_space.second_countable_topology α] {ι : Sort*}
  {μ : measure_theory.measure δ} [countable ι] {f : ι → δ → α}
  (hf : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
ae_strongly_measurable (λ (b : δ), ⨆ (i : ι), f i b) μ :=
ae_strongly_measurable.is_lub hf $ (ae_of_all μ (λ b, is_lub_supr))

theorem ae_strongly_measurable.ennreal_tsum {α : Type*} [measurable_space α] {ι : Type*}
  [countable ι] {f : ι → α → ennreal} {μ : measure_theory.measure α}
  (h : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
ae_strongly_measurable (λ (x : α), ∑' (i : ι), f i x) μ :=
  by { simp_rw [ennreal.tsum_eq_supr_sum], apply ae_strongly_measurable_supr,
  exact λ s, finset.ae_strongly_measurable_sum s (λ i _, h i) }

theorem strongly_measurable.is_lub {α : Type*} {δ : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [measurable_space δ] [linear_order α]
  [order_topology α] [topological_space.second_countable_topology α]
  {ι : Sort*} [countable ι] {f : ι → δ → α} {g : δ → α}
  (hf : ∀ (i : ι), strongly_measurable (f i))
  (hg : ∀ (b : δ), is_lub {a : α | ∃ (i : ι), f i b = a} (g b)) :
strongly_measurable g :=
begin
  change ∀ b, is_lub (set.range $ λ i, f i b) (g b) at hg,
  dsimp [strongly_measurable] at hf ⊢,




  rw [‹borel_space α›.measurable_eq, borel_eq_generate_from_Ioi α],
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  simp_rw [set.preimage, mem_Ioi, lt_is_lub_iff (hg _), exists_range_iff, set_of_exists],
  exact measurable_set.Union (λ i, hf i (is_open_lt' _).measurable_set)
end


@[measurability]
theorem strongly_measurable_supr {α : Type*} {δ : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [measurable_space δ] [complete_linear_order α]
  [order_topology α] [topological_space.second_countable_topology α] {ι : Sort*}
  [countable ι] {f : ι → δ → α} (hf : ∀ (i : ι), strongly_measurable (f i)) :
strongly_measurable (λ (b : δ), ⨆ (i : ι), f i b) :=
strongly_measurable.is_lub hf $ λ b, is_lub_supr



@[measurability]
theorem strongly_measurable.ennreal_tsum {α : Type*} [measurable_space α] {ι : Type*}
  [countable ι] {f : ι → α → ennreal} (h : ∀ (i : ι), strongly_measurable (f i)) :
strongly_measurable (λ (x : α), ∑' (i : ι), f i x) :=
by { simp_rw [ennreal.tsum_eq_supr_sum], apply strongly_measurable_supr,
  exact λ s, s.strongly_measurable_sum (λ i _, h i) }



@[measurability]
theorem strongly_measurable.nnreal_tsum {α : Type*} [measurable_space α]
{ι : Type*} [countable ι] {f : ι → α → nnreal} (h : ∀ (i : ι), strongly_measurable (f i)) :
strongly_measurable (λ (x : α), ∑' (i : ι), f i x) :=
begin
  simp_rw [nnreal.tsum_eq_to_nnreal_tsum],
  exact (strongly_measurable.ennreal_tsum (λ i, (h i).coe_nnreal_ennreal)).ennreal_to_nnreal,
end

---- KEY LEMMA, asked on Zulip 1/10/23
theorem ae_strongly_measurable.nnreal_tsum {α : Type*} [measurable_space α] {ι : Type*}
  [countable ι] {f : ι → α → nnreal} {μ : measure_theory.measure α}
  (h : ∀ (i : ι), ae_strongly_measurable (f i) μ) :
ae_strongly_measurable (λ (x : α), ∑' (i : ι), f i x) μ :=
begin
  simp_rw [nnreal.tsum_eq_to_nnreal_tsum],
  dsimp [ae_strongly_measurable],
  sorry,


  -- apply ae_strongly_measurable_supr,
  -- exact λ s, finset.ae_strongly_measurable_sum s (λ i _, h i),
  -- exact (ae_strongly_measurable.ennreal_tsum (λ i, (h i).coe_nnreal_ennreal)).ennreal_to_nnreal,
end
/-
begin
  simp_rw [ennreal.tsum_eq_supr_sum],
  apply ae_strongly_measurable_supr,
  exact λ s, finset.ae_strongly_measurable_sum s (λ i _, h i),
end
-/

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
lemma mul_ess_sup_of_g [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  (g : G ⧸ Γ → ℝ≥0∞) (g_measurable : ae_measurable g μ_𝓕) :
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

--open_locale measure_theory

@[to_additive]
lemma _root_.measure_theory.is_fundamental_domain.absolutely_continuous_map
  [μ.is_mul_right_invariant] :
  map (quotient_group.mk : G → G ⧸ Γ) μ ≪ map (quotient_group.mk : G → G ⧸ Γ) (μ.restrict 𝓕) :=
begin
  set π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  apply measure_theory.measure.absolutely_continuous.mk,
  intros s s_meas hs,
  rw map_apply meas_π s_meas at hs ⊢,
  rw measure.restrict_apply at hs,
  apply h𝓕.measure_zero_of_invariant _ _ hs,
  {
    intros γ,
    ext g,
    rw set.mem_smul_set_iff_inv_smul_mem,
    rw mem_preimage,
    rw mem_preimage,
    congrm _ ∈ s,
    convert quotient_group.mk_mul_of_mem g (mul_opposite.unop (γ⁻¹)) (γ⁻¹).2,
  },
  sorry, -- HOMEWORK easy measurability
end

/-- This is the "unfolding" trick

 PROOF: (Remember we PRed `integral_eq_tsum`)

∫_G f = ∑_γ ∫_𝓕 f(γ⁻¹ • x ) : h𝓕.integral_eq_tsum'
... = ∫_𝓕  ∑_γ  f(γ⁻¹ • x ) : integral_tsum (to be PRed)
... = ∫_𝓕  F ∘ π  : def of F
... = ∫_(G/Γ) F
 -/
@[to_additive]
lemma mul_unfolding_trick' [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  (f : G → ℂ)
  (f_summable: ∀ x : G, summable (λ (γ : Γ.opposite), f (γ⁻¹ • x))) -- NEEDED??
  (f_ℒ_1 : integrable f μ)
  (F : G ⧸ Γ → ℂ)
  (F_ae_measurable : ae_strongly_measurable F μ_𝓕) -- NEEDED??
  (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x ∂μ = ∫ (x : G ⧸ Γ), F x ∂μ_𝓕 :=
begin
  convert h𝓕.integral_eq_tsum f _ using 2,
  sorry,
end

--- STOPPED 1/10/23. Next time: PR `fundamental_domain.set_integral_eq_tsum` and explore alternative
--- proofs of unfolding:

/-- This is the "unfolding" trick -/
@[to_additive]
lemma mul_unfolding_trick [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  {f : G → ℂ}
  (f_summable: ∀ x : G, summable (λ (γ : Γ.opposite), f (γ⁻¹ • x))) -- NEEDED??
  (f_ℒ_1 : integrable f μ)
  {g : G ⧸ Γ → ℂ}
  (hg : ae_strongly_measurable g μ_𝓕)
  (g_ℒ_infinity : ess_sup (λ x, ↑∥g x∥₊) μ_𝓕 < ∞)
  {F : G ⧸ Γ → ℂ}
  (F_ae_measurable : ae_strongly_measurable F μ_𝓕) -- NEEDED??
  (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x * g (x : G ⧸ Γ) ∂μ = ∫ (x : G ⧸ Γ), F x * g x ∂μ_𝓕 :=
begin
  refine mul_unfolding_trick' h𝓕 (f * (g ∘ (coe : G → G ⧸ Γ))) _ _ (F * g) _ _,
end

#exit

--  set F : G ⧸ Γ → ℂ :=  λ x , ∑' (γ : Γ.opposite), f(γ • x)) ,
  have hFf' : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ⁻¹ • x),
  { intros x,
    rw hFf x,
    exact ((equiv.inv (Γ.opposite)).tsum_eq  (λ γ, f(γ • x))).symm, },
  let π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  rw integral_map meas_π.ae_measurable,
  have : ∀ (x : G), F (x : G ⧸ Γ) * g (x) = ∑' (γ : Γ.opposite), f (γ⁻¹ • x) * g (x),
  { intros x,
    rw hFf' x,
    convert (@tsum_smul_const _ Γ.opposite _ _ _ _ _ _ _ (λ γ, f (γ⁻¹ • x)) _ (g x) _).symm using 1,
    exact f_summable x, },
  refine eq.trans _ (integral_congr_ae (filter.eventually_of_forall this)).symm,
  haveI : encodable Γ.opposite := sorry,
  rw measure_theory.integral_tsum, --- WILL NEED MORE ASSUMPTIONS TO BE SATISFIED HERE
  haveI := h𝓕.smul_invariant_measure_map,
--  have := h𝓕.set_integral_eq_tsum (λ x, f x * g x) univ _,
  convert h𝓕.set_integral_eq_tsum (λ x, f x * g x) univ _,
  { simp, },
  { ext1 γ,
    simp only [smul_set_univ, univ_inter],
    congr,
    ext1 x,
    have : g ↑(γ⁻¹ • x) = g x,
    { obtain ⟨γ₀, hγ₀⟩ := γ,
      congr' 1,
      simpa [quotient_group.eq, (•)] using hγ₀, },
    rw this, },
  { refine integrable.mul_ℒ_infinity f _ (λ x : G, g (x : G ⧸ Γ)) _ _,
    { rw measure.restrict_univ,
      exact f_ℒ_1 },
    { rw measure.restrict_univ,
      exact (ae_strongly_measurable_of_absolutely_continuous h𝓕.absolutely_continuous_map _
        hg).comp_measurable meas_π, },
    { have hg' : ae_strongly_measurable (λ x, ↑∥g x∥₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_ae_strongly_measurable hg,
      rw [measure.restrict_univ, ← mul_ess_sup_of_g h𝓕 (λ x, ↑∥g x∥₊) hg'.ae_measurable],
      exact g_ℒ_infinity } },
  { intros γ,
    have hf' : ae_strongly_measurable f (measure.map ((•) γ⁻¹) μ),
    { rw measure_theory.map_smul,
      exact f_ℒ_1.1 },
    refine ((hf'.comp_measurable (measurable_const_smul _)).mono_measure _).mul _,
    { exact measure.restrict_le_self },
    { exact hg.comp_measurable meas_π } },
  { have := F_ae_measurable,

  },
end
