/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.lebesgue
import measure_theory.measure.regular

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: left and right invariant measures.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `is_haar_measure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/

noncomputable theory

open_locale ennreal pointwise big_operators
open has_inv set function measure_theory.measure

namespace measure_theory

variables {G : Type*}

section

variables [measurable_space G] [has_mul G]

/-- A measure `μ` on a topological group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left multiplication,
  since preimages are nicer to work with than images. -/
@[to_additive "A measure on a topological group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left addition,
  since preimages are nicer to work with than images."]
def is_mul_left_invariant (μ : set G → ℝ≥0∞) : Prop :=
∀ (g : G) {A : set G} (h : measurable_set A), μ ((λ h, g * h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself.
  To right translate sets we use preimage under right multiplication,
  since preimages are nicer to work with than images. -/
@[to_additive "A measure on a topological group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself.
  To right translate sets we use preimage under right addition,
  since preimages are nicer to work with than images."]
def is_mul_right_invariant (μ : set G → ℝ≥0∞) : Prop :=
∀ (g : G) {A : set G} (h : measurable_set A), μ ((λ h, h * g) ⁻¹' A) = μ A

@[to_additive measure_theory.is_add_left_invariant.smul]
lemma is_mul_left_invariant.smul {μ : measure G} (h : is_mul_left_invariant μ) (c : ℝ≥0∞) :
  is_mul_left_invariant ((c • μ : measure G) : set G → ℝ≥0∞) :=
λ g A hA, by rw [smul_apply, smul_apply, h g hA]

@[to_additive measure_theory.is_add_right_invariant.smul]
lemma is_mul_right_invariant.smul {μ : measure G} (h : is_mul_right_invariant μ) (c : ℝ≥0∞) :
  is_mul_right_invariant ((c • μ : measure G) : set G → ℝ≥0∞) :=
λ g A hA, by rw [smul_apply, smul_apply, h g hA]

end

namespace measure

variables [measurable_space G]

@[to_additive]
lemma map_mul_left_eq_self [topological_space G] [has_mul G] [has_continuous_mul G] [borel_space G]
  {μ : measure G} : (∀ g, measure.map ((*) g) μ = μ) ↔ is_mul_left_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_const_mul g) hA]
end

@[to_additive]
lemma _root_.measure_theory.is_mul_left_invariant.measure_preimage_mul
  [topological_space G] [group G] [topological_group G] [borel_space G]
  {μ : measure G} (h : is_mul_left_invariant μ) (g : G) (A : set G) :
  μ ((λ h, g * h) ⁻¹' A) = μ A :=
calc μ ((λ h, g * h) ⁻¹' A) = measure.map (λ h, g * h) μ A :
  ((homeomorph.mul_left g).to_measurable_equiv.map_apply A).symm
... = μ A : by rw map_mul_left_eq_self.2 h g

@[to_additive]
lemma map_mul_right_eq_self [topological_space G] [has_mul G] [has_continuous_mul G] [borel_space G]
  {μ : measure G} :
  (∀ g, measure.map (λ h, h * g) μ = μ) ↔ is_mul_right_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_mul_const g) hA]
end

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected def inv [has_inv G] (μ : measure G) : measure G :=
measure.map inv μ

variables [group G] [topological_space G] [topological_group G] [borel_space G]

@[to_additive]
lemma inv_apply (μ : measure G) {s : set G} (hs : measurable_set s) :
  μ.inv s = μ s⁻¹ :=
measure.map_apply measurable_inv hs

@[simp, to_additive] protected lemma inv_inv (μ : measure G) : μ.inv.inv = μ :=
begin
  ext1 s hs, rw [μ.inv.inv_apply hs, μ.inv_apply, set.inv_inv],
  exact measurable_inv hs
end

variables {μ : measure G}

@[to_additive]
instance regular.inv [t2_space G] [regular μ] : regular μ.inv :=
regular.map (homeomorph.inv G)

end measure

section inv
variables [measurable_space G] [group G] [topological_space G] [topological_group G] [borel_space G]
  {μ : measure G}

@[simp, to_additive] lemma regular_inv_iff [t2_space G] : μ.inv.regular ↔ μ.regular :=
begin
  split,
  { introI h,
    rw ←μ.inv_inv,
    exact measure.regular.inv },
  { introI h,
    exact measure.regular.inv }
end

@[to_additive]
lemma is_mul_left_invariant.inv (h : is_mul_left_invariant μ) :
  is_mul_right_invariant μ.inv :=
begin
  intros g A hA,
  rw [μ.inv_apply (measurable_mul_const g hA), μ.inv_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr,
  intro h,
  simp only [mul_inv_rev, comp_app, inv_inv]
end

@[to_additive]
lemma is_mul_right_invariant.inv (h : is_mul_right_invariant μ) : is_mul_left_invariant μ.inv :=
begin
  intros g A hA,
  rw [μ.inv_apply (measurable_const_mul g hA), μ.inv_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr,
  intro h,
  simp only [mul_inv_rev, comp_app, inv_inv]
end

@[simp, to_additive]
lemma is_mul_right_invariant_inv : is_mul_right_invariant μ.inv ↔ is_mul_left_invariant μ :=
⟨λ h, by { rw ← μ.inv_inv, exact h.inv }, λ h, h.inv⟩

@[simp, to_additive]
lemma is_mul_left_invariant_inv : is_mul_left_invariant μ.inv ↔ is_mul_right_invariant μ :=
⟨λ h, by { rw ← μ.inv_inv, exact h.inv }, λ h, h.inv⟩

end inv

section group

variables [measurable_space G] [topological_space G] [borel_space G] {μ : measure G}
variables [group G] [topological_group G]

/-- If a left-invariant measure gives positive mass to a compact set, then
it gives positive mass to any open set. -/
@[to_additive]
lemma is_mul_left_invariant.measure_pos_of_is_open (hμ : is_mul_left_invariant μ)
  (K : set G) (hK : is_compact K) (h : μ K ≠ 0) {U : set G} (hU : is_open U) (h'U : U.nonempty) :
  0 < μ U :=
begin
  contrapose! h,
  rw ← nonpos_iff_eq_zero,
  rw nonpos_iff_eq_zero at h,
  rw ← hU.interior_eq at h'U,
  obtain ⟨t, hKt⟩ : ∃ (t : finset G), K ⊆ ⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U,
  calc μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U) : measure_mono hKt
  ... ≤ ∑ g in t, μ ((λ (h : G), g * h) ⁻¹' U) : measure_bUnion_finset_le _ _
  ... = 0 : by simp [hμ _ hU.measurable_set, h]
end

/-! A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive]
lemma is_mul_left_invariant.null_iff_empty [regular μ] (hμ : is_mul_left_invariant μ)
  (h3μ : μ ≠ 0) {s : set G} (hs : is_open s) :
  μ s = 0 ↔ s = ∅ :=
begin
  obtain ⟨K, hK, h2K⟩ := regular.exists_compact_not_null.mpr h3μ,
  refine ⟨λ h, _, λ h, by simp only [h, measure_empty]⟩,
  contrapose h,
  exact (hμ.measure_pos_of_is_open K hK h2K hs (ne_empty_iff_nonempty.mp h)).ne'
end

@[to_additive]
lemma is_mul_left_invariant.null_iff [regular μ] (h2μ : is_mul_left_invariant μ)
  {s : set G} (hs : is_open s) :
  μ s = 0 ↔ s = ∅ ∨ μ = 0 :=
begin
  by_cases h3μ : μ = 0, { simp [h3μ] },
  simp only [h3μ, or_false],
  exact h2μ.null_iff_empty h3μ hs,
end

@[to_additive]
lemma is_mul_left_invariant.measure_ne_zero_iff_nonempty [regular μ]
  (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0) {s : set G} (hs : is_open s) :
  μ s ≠ 0 ↔ s.nonempty :=
by simp_rw [← ne_empty_iff_nonempty, ne.def, h2μ.null_iff_empty h3μ hs]

@[to_additive]
lemma is_mul_left_invariant.measure_pos_iff_nonempty [regular μ]
  (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0) {s : set G} (hs : is_open s) :
  0 < μ s ↔ s.nonempty :=
pos_iff_ne_zero.trans $ h2μ.measure_ne_zero_iff_nonempty h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then
it gives finite mass to any compact set. -/
@[to_additive]
lemma is_mul_left_invariant.measure_lt_top_of_is_compact (hμ : is_mul_left_invariant μ)
  (U : set G) (hU : is_open U) (h'U : U.nonempty) (h : μ U ≠ ∞) {K : set G} (hK : is_compact K) :
  μ K < ∞ :=
begin
  rw ← hU.interior_eq at h'U,
  obtain ⟨t, hKt⟩ : ∃ (t : finset G), K ⊆ ⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U,
  calc μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U) : measure_mono hKt
  ... ≤ ∑ g in t, μ ((λ (h : G), g * h) ⁻¹' U) : measure_bUnion_finset_le _ _
  ... = finset.card t * μ U : by simp only [hμ _ hU.measurable_set, finset.sum_const, nsmul_eq_mul]
  ... < ∞ : ennreal.mul_lt_top ennreal.coe_nat_ne_top h
end

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive]
lemma is_mul_left_invariant.measure_lt_top_of_is_compact' (hμ : is_mul_left_invariant μ)
  (U : set G) (hU : (interior U).nonempty) (h : μ U ≠ ∞) {K : set G} (hK : is_compact K) :
  μ K < ∞ :=
hμ.measure_lt_top_of_is_compact (interior U) is_open_interior hU
  ((measure_mono (interior_subset)).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive]
lemma lintegral_eq_zero_of_is_mul_left_invariant [regular μ]
  (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0) {f : G → ℝ≥0∞} (hf : continuous f) :
  ∫⁻ x, f x ∂μ = 0 ↔ f = 0 :=
begin
  split, swap, { rintro rfl, simp_rw [pi.zero_apply, lintegral_zero] },
  intro h, contrapose h,
  simp_rw [funext_iff, not_forall, pi.zero_apply] at h, cases h with x hx,
  obtain ⟨r, h1r, h2r⟩ : ∃ r : ℝ≥0∞, 0 < r ∧ r < f x :=
  exists_between (pos_iff_ne_zero.mpr hx),
  have h3r := hf.is_open_preimage (Ioi r) is_open_Ioi,
  let s := Ioi r,
  rw [← ne.def, ← pos_iff_ne_zero],
  have : 0 < r * μ (f ⁻¹' Ioi r),
  { have : (f ⁻¹' Ioi r).nonempty, from ⟨x, h2r⟩,
    simpa [h1r.ne', h2μ.measure_pos_iff_nonempty h3μ h3r, h1r] },
  refine this.trans_le _,
  rw [← set_lintegral_const, ← lintegral_indicator _ h3r.measurable_set],
  apply lintegral_mono,
  refine indicator_le (λ y, le_of_lt),
end

end group

section integration

variables [measurable_space G] [topological_space G] [borel_space G] {μ : measure G}
variables [group G] [has_continuous_mul G]
open measure

/-- Translating a function by left-multiplication does not change its `lintegral` with respect to
a left-invariant measure. -/
@[to_additive]
lemma lintegral_mul_left_eq_self (hμ : is_mul_left_invariant μ) (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (g * x) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  have : measure.map (has_mul.mul g) μ = μ,
  { rw ← map_mul_left_eq_self at hμ,
    exact hμ g },
  convert (lintegral_map_equiv f (homeomorph.mul_left g).to_measurable_equiv).symm,
  simp [this]
end

/-- Translating a function by right-multiplication does not change its `lintegral` with respect to
a right-invariant measure. -/
@[to_additive]
lemma lintegral_mul_right_eq_self (hμ : is_mul_right_invariant μ) (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (x * g) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  have : measure.map (homeomorph.mul_right g) μ = μ,
  { rw ← map_mul_right_eq_self at hμ,
    exact hμ g },
  convert (lintegral_map_equiv f (homeomorph.mul_right g).to_measurable_equiv).symm,
  simp [this]
end

end integration

section haar
namespace measure

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to compact
sets and positive mass to open sets. -/
class is_haar_measure {G : Type*} [group G] [topological_space G] [measurable_space G]
  (μ : measure G) : Prop :=
(left_invariant : is_mul_left_invariant μ)
(compact_lt_top : ∀ (K : set G), is_compact K → μ K < ∞)
(open_pos : ∀ (U : set G), is_open U → U.nonempty → 0 < μ U)

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and gives
finite mass to compact sets and positive mass to open sets. -/
class is_add_haar_measure {G : Type*} [add_group G] [topological_space G] [measurable_space G]
  (μ : measure G) : Prop :=
(add_left_invariant : is_add_left_invariant μ)
(compact_lt_top : ∀ (K : set G), is_compact K → μ K < ∞)
(open_pos : ∀ (U : set G), is_open U → U.nonempty → 0 < μ U)

attribute [to_additive] is_haar_measure

section

variables [group G] [measurable_space G] [topological_space G] (μ : measure G) [is_haar_measure μ]

@[to_additive]
lemma _root_.is_compact.haar_lt_top {K : set G} (hK : is_compact K) :
  μ K < ∞ :=
is_haar_measure.compact_lt_top K hK

@[to_additive]
lemma _root_.is_open.haar_pos {U : set G} (hU : is_open U) (h'U : U.nonempty) :
  0 < μ U :=
is_haar_measure.open_pos U hU h'U

@[to_additive]
lemma haar_pos_of_nonempty_interior {U : set G} (hU : (interior U).nonempty) : 0 < μ U :=
lt_of_lt_of_le (is_open_interior.haar_pos μ hU) (measure_mono (interior_subset))

@[to_additive]
lemma is_mul_left_invariant_haar : is_mul_left_invariant μ :=
is_haar_measure.left_invariant

@[simp, to_additive]
lemma haar_preimage_mul [topological_group G] [borel_space G] (g : G) (A : set G) :
  μ ((λ h, g * h) ⁻¹' A) = μ A :=
(is_mul_left_invariant_haar μ).measure_preimage_mul _ _

@[simp, to_additive]
lemma haar_singleton [topological_group G] [borel_space G] (g : G) :
  μ {g} = μ {(1 : G)} :=
begin
  convert haar_preimage_mul μ (g⁻¹) _,
  simp only [mul_one, preimage_mul_left_singleton, inv_inv],
end

@[simp, to_additive]
lemma haar_preimage_mul_right {G : Type*}
  [comm_group G] [measurable_space G] [topological_space G] (μ : measure G) [is_haar_measure μ]
  [topological_group G] [borel_space G] (g : G) (A : set G) :
  μ ((λ h, h * g) ⁻¹' A) = μ A :=
by simp_rw [mul_comm, haar_preimage_mul μ g A]

@[to_additive measure_theory.measure.is_add_haar_measure.smul]
lemma is_haar_measure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) :
  is_haar_measure (c • μ) :=
{ left_invariant := (is_mul_left_invariant_haar μ).smul _,
  compact_lt_top := λ K hK, begin
    change c * μ K < ∞,
    simp [lt_top_iff_ne_top, (hK.haar_lt_top μ).ne, cpos, ctop],
  end,
  open_pos := λ U U_open U_ne, bot_lt_iff_ne_bot.2 $ begin
    change c * μ U ≠ 0,
    simp [cpos, (_root_.is_open.haar_pos μ U_open U_ne).ne'],
  end }

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure -/
@[to_additive]
lemma is_haar_measure_of_is_compact_nonempty_interior [topological_group G] [borel_space G]
  (μ : measure G) (hμ : is_mul_left_invariant μ)
  (K : set G) (hK : is_compact K) (h'K : (interior K).nonempty) (h : μ K ≠ 0) (h' : μ K ≠ ∞) :
  is_haar_measure μ :=
{ left_invariant := hμ,
  compact_lt_top := λ L hL, hμ.measure_lt_top_of_is_compact' _ h'K h' hL,
  open_pos := λ U hU, hμ.measure_pos_of_is_open K hK h hU }

/-- The image of a Haar measure under a group homomorphism which is also a homeomorphism is again
a Haar measure. -/
@[to_additive]
lemma is_haar_measure_map [borel_space G] [topological_group G] {H : Type*} [group H]
  [topological_space H] [measurable_space H] [borel_space H] [t2_space H] [topological_group H]
  (f : G ≃* H) (hf : continuous f) (hfsymm : continuous f.symm) :
  is_haar_measure (measure.map f μ) :=
{ left_invariant := begin
    rw ← map_mul_left_eq_self,
    assume h,
    rw map_map (continuous_mul_left h).measurable hf.measurable,
    conv_rhs { rw ← map_mul_left_eq_self.2 (is_mul_left_invariant_haar μ) (f.symm h) },
    rw map_map hf.measurable (continuous_mul_left _).measurable,
    congr' 2,
    ext y,
    simp only [mul_equiv.apply_symm_apply, comp_app, mul_equiv.map_mul],
  end,
  compact_lt_top := begin
    assume K hK,
    rw map_apply hf.measurable hK.measurable_set,
    have : f.symm '' K = f ⁻¹' K := equiv.image_eq_preimage _ _,
    rw ← this,
    exact is_compact.haar_lt_top _ (hK.image hfsymm)
  end,
  open_pos := begin
    assume U hU h'U,
    rw map_apply hf.measurable hU.measurable_set,
    refine (hU.preimage hf).haar_pos _ _,
    have : f.symm '' U = f ⁻¹' U := equiv.image_eq_preimage _ _,
    rw ← this,
    simp [h'U],
  end }

/-- A Haar measure on a sigma-compact space is sigma-finite. -/
@[priority 100, to_additive] -- see Note [lower instance priority]
instance is_haar_measure.sigma_finite
  {G : Type*} [group G] [measurable_space G] [topological_space G] [sigma_compact_space G]
  (μ : measure G) [μ.is_haar_measure] :
  sigma_finite μ :=
⟨⟨{ set := compact_covering G,
  set_mem := λ n, mem_univ _,
  finite := λ n, is_compact.haar_lt_top μ $ is_compact_compact_covering G n,
  spanning := Union_compact_covering G }⟩⟩

open_locale topological_space
open filter

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has
no atom.

This applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/
@[priority 100, to_additive]
instance is_haar_measure.has_no_atoms
  {G : Type*} [group G] [measurable_space G] [topological_space G] [t1_space G]
  [topological_group G] [locally_compact_space G] [borel_space G] [(𝓝[{(1 : G)}ᶜ] (1 : G)).ne_bot]
  (μ : measure G) [μ.is_haar_measure] :
  has_no_atoms μ :=
begin
  suffices H : μ {(1 : G)} ≤ 0, by { constructor, simp [le_bot_iff.1 H] },
  obtain ⟨K, K_compact, K_int⟩ : ∃ (K : set G), is_compact K ∧ (1 : G) ∈ interior K,
  { rcases exists_compact_subset is_open_univ (mem_univ (1 : G)) with ⟨K, hK⟩,
    exact ⟨K, hK.1, hK.2.1⟩ },
  have K_inf : set.infinite K := infinite_of_mem_nhds (1 : G) (mem_interior_iff_mem_nhds.1 K_int),
  have μKlt : μ K ≠ ∞ := (K_compact.haar_lt_top μ).ne,
  have I : ∀ (n : ℕ), μ {(1 : G)} ≤ μ K / n,
  { assume n,
    obtain ⟨t, tK, tn⟩ : ∃ (t : finset G), ↑t ⊆ K ∧ t.card = n := K_inf.exists_subset_card_eq n,
    have A : μ t ≤ μ K := measure_mono tK,
    have B : μ t = n * μ {(1 : G)},
    { rw ← bUnion_of_singleton ↑t,
      change μ (⋃ (x ∈ t), {x}) = n * μ {1},
      rw @measure_bUnion_finset G G _ μ t (λ i, {i}),
      { simp only [tn, finset.sum_const, nsmul_eq_mul, haar_singleton] },
      { assume x hx y hy xy,
        simp only [on_fun, xy.symm, mem_singleton_iff, not_false_iff, disjoint_singleton_right] },
      { assume b hb, exact measurable_set_singleton b } },
    rw B at A,
    rwa [ennreal.le_div_iff_mul_le _ (or.inr μKlt), mul_comm],
    right,
    apply ne_of_gt (haar_pos_of_nonempty_interior μ ⟨_, K_int⟩) },
  have J : tendsto (λ (n : ℕ),  μ K / n) at_top (𝓝 (μ K / ∞)) :=
    ennreal.tendsto.const_div ennreal.tendsto_nat_nhds_top (or.inr μKlt),
  simp only [ennreal.div_top] at J,
  exact ge_of_tendsto' J I,
end

/- The above instance applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/
example {E : Type*} [normed_group E] [normed_space ℝ E] [nontrivial E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E] (μ : measure E) [is_add_haar_measure μ] :
  has_no_atoms μ := by apply_instance

end

end measure
end haar

end measure_theory
