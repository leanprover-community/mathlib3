/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import dynamics.ergodic.measure_preserving
import measure_theory.measure.regular
import measure_theory.group.measurable_equiv
import measure_theory.measure.open_pos

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `is_haar_measure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/

noncomputable theory

open_locale ennreal pointwise big_operators
open has_inv set function measure_theory.measure

variables {G : Type*} [measurable_space G]

namespace measure_theory
namespace measure

/-- A measure `μ` on a measurable additive group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
class is_add_left_invariant [has_add G] (μ : measure G) : Prop :=
(map_add_left_eq_self : ∀ g : G, map ((+) g) μ = μ)

/-- A measure `μ` on a measurable group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
@[to_additive] class is_mul_left_invariant [has_mul G] (μ : measure G) : Prop :=
(map_mul_left_eq_self : ∀ g : G, map ((*) g) μ = μ)

/-- A measure `μ` on a measurable additive group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
class is_add_right_invariant [has_add G] (μ : measure G) : Prop :=
(map_add_right_eq_self : ∀ g : G, map (+ g) μ = μ)

/-- A measure `μ` on a measurable group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
@[to_additive] class is_mul_right_invariant [has_mul G] (μ : measure G) : Prop :=
(map_mul_right_eq_self : ∀ g : G, map (* g) μ = μ)

end measure
open measure

section mul

variables [has_mul G] {μ : measure G}

@[to_additive]
lemma map_mul_left_eq_self (μ : measure G) [is_mul_left_invariant μ] (g : G) : map ((*) g) μ = μ :=
is_mul_left_invariant.map_mul_left_eq_self g

@[to_additive]
lemma map_mul_right_eq_self (μ : measure G) [is_mul_right_invariant μ] (g : G) : map (* g) μ = μ :=
is_mul_right_invariant.map_mul_right_eq_self g

@[to_additive]
instance [is_mul_left_invariant μ] (c : ℝ≥0∞) : is_mul_left_invariant (c • μ) :=
⟨λ g, by rw [measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive]
instance [is_mul_right_invariant μ] (c : ℝ≥0∞) : is_mul_right_invariant (c • μ) :=
⟨λ g, by rw [measure.map_smul, map_mul_right_eq_self]⟩

section has_measurable_mul

variables [has_measurable_mul G]

@[to_additive]
lemma measure_preserving_mul_left (μ : measure G) [is_mul_left_invariant μ] (g : G) :
  measure_preserving ((*) g) μ μ :=
⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]
lemma measure_preserving_mul_right (μ : measure G) [is_mul_right_invariant μ] (g : G) :
  measure_preserving (* g) μ μ :=
⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive /-" An alternative way to prove that `μ` is left invariant under addition. "-/]
lemma forall_measure_preimage_mul_iff (μ : measure G) :
  (∀ (g : G) (A : set G), measurable_set A → μ ((λ h, g * h) ⁻¹' A) = μ A) ↔
  is_mul_left_invariant μ :=
begin
  transitivity ∀ g, map ((*) g) μ = μ,
  { simp_rw [measure.ext_iff],
    refine forall_congr (λ g, forall_congr $ λ A, forall_congr $ λ hA, _),
    rw [map_apply (measurable_const_mul g) hA] },
  exact ⟨λ h, ⟨h⟩, λ h, h.1⟩
end

/-- An alternative way to prove that `μ` is right invariant under multiplication. -/
@[to_additive /-" An alternative way to prove that `μ` is right invariant under addition. "-/]
lemma forall_measure_preimage_mul_right_iff (μ : measure G) :
  (∀ (g : G) (A : set G), measurable_set A → μ ((λ h, h * g) ⁻¹' A) = μ A) ↔
  is_mul_right_invariant μ :=
begin
  transitivity ∀ g, map (* g) μ = μ,
  { simp_rw [measure.ext_iff],
    refine forall_congr (λ g, forall_congr $ λ A, forall_congr $ λ hA, _),
    rw [map_apply (measurable_mul_const g) hA] },
  exact ⟨λ h, ⟨h⟩, λ h, h.1⟩
end

end has_measurable_mul

end mul

section group

variables [group G]

@[to_additive]
lemma map_div_right_eq_self (μ : measure G) [is_mul_right_invariant μ] (g : G) :
  map (/ g) μ = μ :=
by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]


variables [has_measurable_mul G]

/-- We shorten this from `measure_preimage_mul_left`, since left invariant is the preferred option
  for measures in this formalization. -/
@[simp, to_additive "We shorten this from `measure_preimage_add_left`, since left invariant is the
preferred option for measures in this formalization."]
lemma measure_preimage_mul (μ : measure G) [is_mul_left_invariant μ] (g : G) (A : set G) :
  μ ((λ h, g * h) ⁻¹' A) = μ A :=
calc μ ((λ h, g * h) ⁻¹' A) = map (λ h, g * h) μ A :
  ((measurable_equiv.mul_left g).map_apply A).symm
... = μ A : by rw map_mul_left_eq_self μ g

@[simp, to_additive]
lemma measure_preimage_mul_right (μ : measure G) [is_mul_right_invariant μ] (g : G) (A : set G) :
  μ ((λ h, h * g) ⁻¹' A) = μ A :=
calc μ ((λ h, h * g) ⁻¹' A) = map (λ h, h * g) μ A :
  ((measurable_equiv.mul_right g).map_apply A).symm
... = μ A : by rw map_mul_right_eq_self μ g

@[to_additive]
lemma map_mul_left_ae (μ : measure G) [is_mul_left_invariant μ] (x : G) :
  filter.map (λ h, x * h) μ.ae = μ.ae :=
((measurable_equiv.mul_left x).map_ae μ).trans $ congr_arg ae $ map_mul_left_eq_self μ x

@[to_additive]
lemma map_mul_right_ae (μ : measure G) [is_mul_right_invariant μ] (x : G) :
  filter.map (λ h, h * x) μ.ae = μ.ae :=
((measurable_equiv.mul_right x).map_ae μ).trans $ congr_arg ae $ map_mul_right_eq_self μ x

@[to_additive]
lemma map_div_right_ae (μ : measure G) [is_mul_right_invariant μ] (x : G) :
  filter.map (λ t, t / x) μ.ae = μ.ae :=
((measurable_equiv.div_right x).map_ae μ).trans $ congr_arg ae $ map_div_right_eq_self μ x

end group

namespace measure

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected def inv [has_inv G] (μ : measure G) : measure G :=
measure.map inv μ

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
class is_neg_invariant [has_neg G] (μ : measure G) : Prop :=
(neg_eq_self : μ.neg = μ)

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive] class is_inv_invariant [has_inv G] (μ : measure G) : Prop :=
(inv_eq_self : μ.inv = μ)

section inv

variables [has_inv G]

@[simp, to_additive]
lemma inv_eq_self (μ : measure G) [is_inv_invariant μ] : μ.inv = μ :=
is_inv_invariant.inv_eq_self

@[simp, to_additive]
lemma map_inv_eq_self (μ : measure G) [is_inv_invariant μ] : map has_inv.inv μ = μ :=
is_inv_invariant.inv_eq_self

end inv

section has_involutive_inv

variables [has_involutive_inv G] [has_measurable_inv G]

@[simp, to_additive]
lemma inv_apply (μ : measure G) (s : set G) : μ.inv s = μ s⁻¹ :=
(measurable_equiv.inv G).map_apply s

@[simp, to_additive]
protected lemma inv_inv (μ : measure G) : μ.inv.inv = μ :=
(measurable_equiv.inv G).map_symm_map

@[simp, to_additive]
lemma measure_inv (μ : measure G) [is_inv_invariant μ] (A : set G) : μ A⁻¹ = μ A :=
by rw [← inv_apply, inv_eq_self]

@[to_additive]
lemma measure_preimage_inv (μ : measure G) [is_inv_invariant μ] (A : set G) :
  μ (has_inv.inv ⁻¹' A) = μ A :=
μ.measure_inv A

@[to_additive]
instance (μ : measure G) [sigma_finite μ] : sigma_finite μ.inv :=
(measurable_equiv.inv G).sigma_finite_map ‹_›

end has_involutive_inv

section mul_inv
variables [group G] [has_measurable_mul G] [has_measurable_inv G] {μ : measure G}

@[to_additive]
instance [is_mul_left_invariant μ] : is_mul_right_invariant μ.inv :=
begin
  constructor,
  intro g,
  conv_rhs { rw [← map_mul_left_eq_self μ g⁻¹] },
  simp_rw [measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), function.comp, mul_inv_rev, inv_inv]
end

@[to_additive]
instance [is_mul_right_invariant μ] : is_mul_left_invariant μ.inv :=
begin
  constructor,
  intro g,
  conv_rhs { rw [← map_mul_right_eq_self μ g⁻¹] },
  simp_rw [measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), function.comp, mul_inv_rev, inv_inv]
end

@[to_additive]
lemma map_div_left_eq_self (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  map (λ t, g / t) μ = μ :=
begin
  simp_rw [div_eq_mul_inv],
  conv_rhs { rw [← map_mul_left_eq_self μ g, ← map_inv_eq_self μ] },
  exact (map_map (measurable_const_mul g) measurable_inv).symm
end

@[to_additive]
lemma map_mul_right_inv_eq_self (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ]
  (g : G) : map (λ t, (g * t)⁻¹) μ = μ :=
begin
  conv_rhs { rw [← map_inv_eq_self μ, ← map_mul_left_eq_self μ g] },
  exact (map_map measurable_inv (measurable_const_mul g)).symm
end

@[to_additive]
lemma map_div_left_ae (μ : measure G) [is_mul_left_invariant μ] [is_inv_invariant μ] (x : G) :
  filter.map (λ t, x / t) μ.ae = μ.ae :=
((measurable_equiv.div_left x).map_ae μ).trans $ congr_arg ae $ map_div_left_eq_self μ x

end mul_inv

end measure

section topological_group

variables [topological_space G] [borel_space G] {μ : measure G}
variables [group G] [topological_group G]

@[to_additive]
instance measure.regular.inv [t2_space G] [regular μ] : regular μ.inv :=
regular.map (homeomorph.inv G)

@[to_additive]
lemma regular_inv_iff [t2_space G] : μ.inv.regular ↔ μ.regular :=
begin
  split,
  { introI h, rw ← μ.inv_inv, exact measure.regular.inv },
  { introI h, exact measure.regular.inv }
end

variables [is_mul_left_invariant μ]

/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/
@[to_additive "If a left-invariant measure gives positive mass to a compact set, then it gives
positive mass to any open set."]
lemma is_open_pos_measure_of_mul_left_invariant_of_compact
  (K : set G) (hK : is_compact K) (h : μ K ≠ 0) :
  is_open_pos_measure μ :=
begin
  refine ⟨λ U hU hne, _⟩,
  contrapose! h,
  rw ← nonpos_iff_eq_zero,
  rw ← hU.interior_eq at hne,
  obtain ⟨t, hKt⟩ : ∃ (t : finset G), K ⊆ ⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne,
  calc μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U) : measure_mono hKt
  ... ≤ ∑ g in t, μ ((λ (h : G), g * h) ⁻¹' U) : measure_bUnion_finset_le _ _
  ... = 0 : by simp [measure_preimage_mul, h]
end

/-- A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive "A nonzero left-invariant regular measure gives positive mass to any open set."]
lemma is_open_pos_measure_of_mul_left_invariant_of_regular [regular μ] (h₀ : μ ≠ 0) :
  is_open_pos_measure μ :=
let ⟨K, hK, h2K⟩ := regular.exists_compact_not_null.mpr h₀
in is_open_pos_measure_of_mul_left_invariant_of_compact K hK h2K

@[to_additive]
lemma null_iff_of_is_mul_left_invariant [regular μ]
  {s : set G} (hs : is_open s) :
  μ s = 0 ↔ s = ∅ ∨ μ = 0 :=
begin
  by_cases h3μ : μ = 0, { simp [h3μ] },
  { haveI := is_open_pos_measure_of_mul_left_invariant_of_regular h3μ,
    simp only [h3μ, or_false, hs.measure_eq_zero_iff μ] },
end

@[to_additive]
lemma measure_ne_zero_iff_nonempty_of_is_mul_left_invariant [regular μ]
  (hμ : μ ≠ 0) {s : set G} (hs : is_open s) :
  μ s ≠ 0 ↔ s.nonempty :=
by simpa [null_iff_of_is_mul_left_invariant hs, hμ] using ne_empty_iff_nonempty

@[to_additive]
lemma measure_pos_iff_nonempty_of_is_mul_left_invariant [regular μ]
  (h3μ : μ ≠ 0) {s : set G} (hs : is_open s) :
  0 < μ s ↔ s.nonempty :=
pos_iff_ne_zero.trans $ measure_ne_zero_iff_nonempty_of_is_mul_left_invariant h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/
@[to_additive "If a left-invariant measure gives finite mass to a nonempty open set, then it gives
finite mass to any compact set."]
lemma measure_lt_top_of_is_compact_of_is_mul_left_invariant
  (U : set G) (hU : is_open U) (h'U : U.nonempty) (h : μ U ≠ ∞) {K : set G} (hK : is_compact K) :
  μ K < ∞ :=
begin
  rw ← hU.interior_eq at h'U,
  obtain ⟨t, hKt⟩ : ∃ (t : finset G), K ⊆ ⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U,
  calc μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (λ (h : G), g * h) ⁻¹' U) : measure_mono hKt
  ... ≤ ∑ g in t, μ ((λ (h : G), g * h) ⁻¹' U) : measure_bUnion_finset_le _ _
  ... = finset.card t * μ U : by simp only [measure_preimage_mul, finset.sum_const, nsmul_eq_mul]
  ... < ∞ : ennreal.mul_lt_top ennreal.coe_nat_ne_top h
end

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive "If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set."]
lemma measure_lt_top_of_is_compact_of_is_mul_left_invariant'
  {U : set G} (hU : (interior U).nonempty) (h : μ U ≠ ∞) {K : set G} (hK : is_compact K) :
  μ K < ∞ :=
measure_lt_top_of_is_compact_of_is_mul_left_invariant (interior U) is_open_interior hU
  ((measure_mono (interior_subset)).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

end topological_group

section comm_group

variables [comm_group G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `is_mul_left_invariant` as default hypotheses in abelian groups. -/
@[priority 100, to_additive "In an abelian additive group every left invariant measure is also
right-invariant. We don't declare the converse as an instance, since that would loop type-class
inference, and we use `is_add_left_invariant` as default hypotheses in abelian groups."]
instance is_mul_left_invariant.is_mul_right_invariant {μ : measure G} [is_mul_left_invariant μ] :
  is_mul_right_invariant μ :=
⟨λ g, by simp_rw [mul_comm, map_mul_left_eq_self]⟩


end comm_group

section haar

namespace measure

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and gives
finite mass to compact sets and positive mass to open sets. -/
class is_add_haar_measure {G : Type*} [add_group G] [topological_space G] [measurable_space G]
  (μ : measure G)
  extends is_finite_measure_on_compacts μ, is_add_left_invariant μ, is_open_pos_measure μ : Prop

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to compact
sets and positive mass to open sets. -/
@[to_additive]
class is_haar_measure {G : Type*} [group G] [topological_space G] [measurable_space G]
  (μ : measure G)
  extends is_finite_measure_on_compacts μ, is_mul_left_invariant μ, is_open_pos_measure μ : Prop

/-- Record that a Haar measure on a locally compact space is locally finite. This is needed as the
fact that a measure which is finite on compacts is locally finite is not registered as an instance,
to avoid an instance loop.

See Note [lower instance priority]. -/

@[priority 100, to_additive "Record that an additive Haar measure on a locally compact space is
locally finite. This is needed as the fact that a measure which is finite on compacts is locally
finite is not registered as an instance, to avoid an instance loop.

See Note [lower instance priority]"]
instance is_locally_finite_measure_of_is_haar_measure {G : Type*}
  [group G] [measurable_space G] [topological_space G] [locally_compact_space G]
  (μ : measure G) [is_haar_measure μ] :
  is_locally_finite_measure μ :=
is_locally_finite_measure_of_is_finite_measure_on_compacts

section

variables [group G] [topological_space G] (μ : measure G) [is_haar_measure μ]

@[simp, to_additive]
lemma haar_singleton [topological_group G] [borel_space G] (g : G) :
  μ {g} = μ {(1 : G)} :=
begin
  convert measure_preimage_mul μ (g⁻¹) _,
  simp only [mul_one, preimage_mul_left_singleton, inv_inv],
end

@[to_additive measure_theory.measure.is_add_haar_measure.smul]
lemma is_haar_measure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) :
  is_haar_measure (c • μ) :=
{ lt_top_of_is_compact := λ K hK, ennreal.mul_lt_top ctop hK.measure_lt_top.ne,
  to_is_open_pos_measure := is_open_pos_measure_smul μ cpos }

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure. -/
@[to_additive "If a left-invariant measure gives positive mass to some compact set with nonempty
interior, then it is an additive Haar measure."]
lemma is_haar_measure_of_is_compact_nonempty_interior [topological_group G] [borel_space G]
  (μ : measure G) [is_mul_left_invariant μ]
  (K : set G) (hK : is_compact K) (h'K : (interior K).nonempty) (h : μ K ≠ 0) (h' : μ K ≠ ∞) :
  is_haar_measure μ :=
{ lt_top_of_is_compact :=
    λ L hL, measure_lt_top_of_is_compact_of_is_mul_left_invariant' h'K h' hL,
  to_is_open_pos_measure := is_open_pos_measure_of_mul_left_invariant_of_compact K hK h }

/-- The image of a Haar measure under a group homomorphism which is also a homeomorphism is again
a Haar measure. -/
@[to_additive "The image of an additive Haar measure under an additive group homomorphism which is
also a homeomorphism is again an additive Haar measure."]
lemma is_haar_measure_map [borel_space G] [topological_group G] {H : Type*} [group H]
  [topological_space H] [measurable_space H] [borel_space H] [t2_space H] [topological_group H]
  (f : G ≃* H) (hf : continuous f) (hfsymm : continuous f.symm) :
  is_haar_measure (measure.map f μ) :=
{ to_is_mul_left_invariant := begin
    constructor,
    assume h,
    rw map_map (continuous_mul_left h).measurable hf.measurable,
    conv_rhs { rw ← map_mul_left_eq_self μ (f.symm h) },
    rw map_map hf.measurable (continuous_mul_left _).measurable,
    congr' 2,
    ext y,
    simp only [mul_equiv.apply_symm_apply, comp_app, mul_equiv.map_mul],
  end,
  lt_top_of_is_compact := begin
    assume K hK,
    rw map_apply hf.measurable hK.measurable_set,
    have : f.symm '' K = f ⁻¹' K := equiv.image_eq_preimage _ _,
    rw ← this,
    exact is_compact.measure_lt_top (hK.image hfsymm)
  end,
  to_is_open_pos_measure := hf.is_open_pos_measure_map f.surjective }

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[priority 100, to_additive "A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority]"]
instance is_haar_measure.sigma_finite [sigma_compact_space G] : sigma_finite μ :=
⟨⟨{ set := compact_covering G,
  set_mem := λ n, mem_univ _,
  finite := λ n, is_compact.measure_lt_top $ is_compact_compact_covering G n,
  spanning := Union_compact_covering G }⟩⟩

open_locale topological_space
open filter

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has
no atoms.

The additive version of this instance applies in particular to show that an additive Haar measure on
a nontrivial finite-dimensional real vector space has no atom. -/
@[priority 100, to_additive "If the zero element of an additive group is not isolated, then an
additive Haar measure on this group has no atoms.

This applies in particular to show that an additive Haar measure on a nontrivial finite-dimensional
real vector space has no atom."]
instance is_haar_measure.has_no_atoms [topological_group G] [borel_space G]
  [t1_space G] [locally_compact_space G] [(𝓝[≠] (1 : G)).ne_bot]
  (μ : measure G) [μ.is_haar_measure] :
  has_no_atoms μ :=
begin
  suffices H : μ {(1 : G)} ≤ 0, by { constructor, simp [le_bot_iff.1 H] },
  obtain ⟨K, K_compact, K_int⟩ : ∃ (K : set G), is_compact K ∧ (1 : G) ∈ interior K,
  { rcases exists_compact_subset is_open_univ (mem_univ (1 : G)) with ⟨K, hK⟩,
    exact ⟨K, hK.1, hK.2.1⟩ },
  have K_inf : set.infinite K := infinite_of_mem_nhds (1 : G) (mem_interior_iff_mem_nhds.1 K_int),
  have μKlt : μ K ≠ ∞ := K_compact.measure_lt_top.ne,
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
    apply (measure_pos_of_nonempty_interior μ ⟨_, K_int⟩).ne' },
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
