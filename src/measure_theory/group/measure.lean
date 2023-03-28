/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import dynamics.ergodic.measure_preserving
import measure_theory.measure.regular
import measure_theory.group.measurable_equiv
import measure_theory.measure.open_pos
import measure_theory.group.action
import measure_theory.constructions.prod
import topology.continuous_function.cocompact_map

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

open_locale nnreal ennreal pointwise big_operators topology
open has_inv set function measure_theory.measure filter

variables {𝕜 G H : Type*} [measurable_space G] [measurable_space H]

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

@[to_additive measure_theory.is_add_left_invariant_smul]
instance is_mul_left_invariant_smul [is_mul_left_invariant μ] (c : ℝ≥0∞) :
  is_mul_left_invariant (c • μ) :=
⟨λ g, by rw [measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive measure_theory.is_add_right_invariant_smul]
instance is_mul_right_invariant_smul [is_mul_right_invariant μ] (c : ℝ≥0∞) :
  is_mul_right_invariant (c • μ) :=
⟨λ g, by rw [measure.map_smul, map_mul_right_eq_self]⟩

@[to_additive measure_theory.is_add_left_invariant_smul_nnreal]
instance is_mul_left_invariant_smul_nnreal [is_mul_left_invariant μ] (c : ℝ≥0) :
  is_mul_left_invariant (c • μ) :=
measure_theory.is_mul_left_invariant_smul (c : ℝ≥0∞)

@[to_additive measure_theory.is_add_right_invariant_smul_nnreal]
instance is_mul_right_invariant_smul_nnreal [is_mul_right_invariant μ] (c : ℝ≥0) :
  is_mul_right_invariant (c • μ) :=
measure_theory.is_mul_right_invariant_smul (c : ℝ≥0∞)

section has_measurable_mul

variables [has_measurable_mul G]

@[to_additive]
lemma measure_preserving_mul_left (μ : measure G) [is_mul_left_invariant μ] (g : G) :
  measure_preserving ((*) g) μ μ :=
⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]
lemma measure_preserving.mul_left (μ : measure G) [is_mul_left_invariant μ] (g : G)
  {X : Type*} [measurable_space X] {μ' : measure X} {f : X → G} (hf : measure_preserving f μ' μ) :
  measure_preserving (λ x, g * f x) μ' μ :=
(measure_preserving_mul_left μ g).comp hf

@[to_additive]
lemma measure_preserving_mul_right (μ : measure G) [is_mul_right_invariant μ] (g : G) :
  measure_preserving (* g) μ μ :=
⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

@[to_additive]
lemma measure_preserving.mul_right (μ : measure G) [is_mul_right_invariant μ] (g : G)
  {X : Type*} [measurable_space X] {μ' : measure X} {f : X → G} (hf : measure_preserving f μ' μ) :
  measure_preserving (λ x, f x * g) μ' μ :=
(measure_preserving_mul_right μ g).comp hf

@[to_additive]
instance is_mul_left_invariant.smul_invariant_measure [is_mul_left_invariant μ] :
  smul_invariant_measure G G μ :=
⟨λ x s hs, (measure_preserving_mul_left μ x).measure_preimage hs⟩

@[to_additive]
instance is_mul_right_invariant.to_smul_invariant_measure_op [μ.is_mul_right_invariant] :
  smul_invariant_measure Gᵐᵒᵖ G μ :=
⟨λ x s hs, (measure_preserving_mul_right μ (mul_opposite.unop x)).measure_preimage hs⟩

@[to_additive]
instance subgroup.smul_invariant_measure
  {G α : Type*} [group G] [mul_action G α] [measurable_space α]
  {μ : measure α} [smul_invariant_measure G α μ] (H : subgroup G) :
  smul_invariant_measure H α μ :=
⟨λ y s hs, by convert smul_invariant_measure.measure_preimage_smul μ (y : G) hs⟩

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

@[to_additive]
instance [is_mul_left_invariant μ] [sigma_finite μ] {H : Type*} [has_mul H]
  {mH : measurable_space H} {ν : measure H} [has_measurable_mul H]
  [is_mul_left_invariant ν] [sigma_finite ν] :
  is_mul_left_invariant (μ.prod ν) :=
begin
  constructor,
  rintros ⟨g, h⟩,
  change map (prod.map ((*) g) ((*) h)) (μ.prod ν) = μ.prod ν,
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h),
    map_mul_left_eq_self μ g, map_mul_left_eq_self ν h],
  { rw map_mul_left_eq_self μ g, apply_instance },
  { rw map_mul_left_eq_self ν h, apply_instance },
end

@[to_additive]
instance [is_mul_right_invariant μ] [sigma_finite μ] {H : Type*} [has_mul H]
  {mH : measurable_space H} {ν : measure H} [has_measurable_mul H]
  [is_mul_right_invariant ν] [sigma_finite ν] :
  is_mul_right_invariant (μ.prod ν) :=
begin
  constructor,
  rintros ⟨g, h⟩,
  change map (prod.map (* g) (* h)) (μ.prod ν) = μ.prod ν,
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h),
    map_mul_right_eq_self μ g, map_mul_right_eq_self ν h],
  { rw map_mul_right_eq_self μ g, apply_instance },
  { rw map_mul_right_eq_self ν h, apply_instance },
end

@[to_additive]
lemma is_mul_left_invariant_map {H : Type*}
  [measurable_space H] [has_mul H] [has_measurable_mul H]
  [is_mul_left_invariant μ]
  (f : G →ₙ* H) (hf : measurable f) (h_surj : surjective f) :
  is_mul_left_invariant (measure.map f μ) :=
begin
  refine ⟨λ h, _⟩,
  rw map_map (measurable_const_mul _) hf,
  obtain ⟨g, rfl⟩ := h_surj h,
  conv_rhs { rw ← map_mul_left_eq_self μ g },
  rw map_map hf (measurable_const_mul _),
  congr' 2,
  ext y,
  simp only [comp_app, map_mul],
end

end has_measurable_mul

end mul

section div_inv_monoid
variables [div_inv_monoid G]

@[to_additive]
lemma map_div_right_eq_self (μ : measure G) [is_mul_right_invariant μ] (g : G) :
  map (/ g) μ = μ :=
by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

end div_inv_monoid

section group
variables [group G] [has_measurable_mul G]

@[to_additive]
lemma measure_preserving_div_right (μ : measure G) [is_mul_right_invariant μ]
  (g : G) : measure_preserving (/ g) μ μ :=
by simp_rw [div_eq_mul_inv, measure_preserving_mul_right μ g⁻¹]

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

@[to_additive]
lemma eventually_mul_left_iff (μ : measure G) [is_mul_left_invariant μ] (t : G) {p : G → Prop} :
  (∀ᵐ x ∂μ, p (t * x)) ↔ ∀ᵐ x ∂μ, p x :=
by { conv_rhs { rw [filter.eventually, ← map_mul_left_ae μ t] }, refl }

@[to_additive]
lemma eventually_mul_right_iff (μ : measure G) [is_mul_right_invariant μ] (t : G) {p : G → Prop} :
  (∀ᵐ x ∂μ, p (x * t)) ↔ ∀ᵐ x ∂μ, p x :=
by { conv_rhs { rw [filter.eventually, ← map_mul_right_ae μ t] }, refl }

@[to_additive]
lemma eventually_div_right_iff (μ : measure G) [is_mul_right_invariant μ] (t : G) {p : G → Prop} :
  (∀ᵐ x ∂μ, p (x / t)) ↔ ∀ᵐ x ∂μ, p x :=
by { conv_rhs { rw [filter.eventually, ← map_div_right_ae μ t] }, refl }

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

variables [has_measurable_inv G]

@[to_additive]
lemma measure_preserving_inv (μ : measure G) [is_inv_invariant μ] :
  measure_preserving has_inv.inv μ μ :=
⟨measurable_inv, map_inv_eq_self μ⟩

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

section division_monoid
variables [division_monoid G] [has_measurable_mul G] [has_measurable_inv G] {μ : measure G}

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
lemma measure_preserving_div_left (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ]
  (g : G) : measure_preserving (λ t, g / t) μ μ :=
begin
  simp_rw [div_eq_mul_inv],
  exact (measure_preserving_mul_left μ g).comp (measure_preserving_inv μ)
end

@[to_additive]
lemma map_div_left_eq_self (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  map (λ t, g / t) μ = μ :=
(measure_preserving_div_left μ g).map_eq

@[to_additive]
lemma measure_preserving_mul_right_inv (μ : measure G)
  [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  measure_preserving (λ t, (g * t)⁻¹) μ μ :=
(measure_preserving_inv μ).comp $ measure_preserving_mul_left μ g

@[to_additive]
lemma map_mul_right_inv_eq_self (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ]
  (g : G) : map (λ t, (g * t)⁻¹) μ = μ :=
(measure_preserving_mul_right_inv μ g).map_eq

end division_monoid

section group
variables [group G] [has_measurable_mul G] [has_measurable_inv G] {μ : measure G}

@[to_additive]
lemma map_div_left_ae (μ : measure G) [is_mul_left_invariant μ] [is_inv_invariant μ] (x : G) :
  filter.map (λ t, x / t) μ.ae = μ.ae :=
((measurable_equiv.div_left x).map_ae μ).trans $ congr_arg ae $ map_div_left_eq_self μ x

end group

end measure

section topological_group

variables [topological_space G] [borel_space G] {μ : measure G} [group G]

@[to_additive]
instance measure.regular.inv [has_continuous_inv G] [t2_space G] [regular μ] : regular μ.inv :=
regular.map (homeomorph.inv G)

variables [topological_group G]

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
by simpa [null_iff_of_is_mul_left_invariant hs, hμ] using nonempty_iff_ne_empty.symm

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
  ... < ∞ : ennreal.mul_lt_top (ennreal.nat_ne_top _) h
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

/-- In a noncompact locally compact group, a left-invariant measure which is positive
on open sets has infinite mass. -/
@[simp, to_additive "In a noncompact locally compact additive group, a left-invariant measure which
is positive on open sets has infinite mass."]
lemma measure_univ_of_is_mul_left_invariant [locally_compact_space G] [noncompact_space G]
  (μ : measure G) [is_open_pos_measure μ] [μ.is_mul_left_invariant] :
  μ univ = ∞ :=
begin
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
  find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
  infinitely many translates of `K` which are disjoint from each other. As they all have the
  same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, hK, Kclosed, Kint⟩ : ∃ (K : set G), is_compact K ∧ is_closed K ∧ (1 : G) ∈ interior K,
  { rcases local_is_compact_is_closed_nhds_of_group (is_open_univ.mem_nhds (mem_univ (1 : G)))
      with ⟨K, hK⟩,
    exact ⟨K, hK.1, hK.2.1, hK.2.2.2⟩, },
  have K_pos : 0 < μ K, from measure_pos_of_nonempty_interior _ ⟨_, Kint⟩,
  have A : ∀ (L : set G), is_compact L → ∃ (g : G), disjoint L (g • K),
    from λ L hL, exists_disjoint_smul_of_is_compact hL hK,
  choose! g hg using A,
  set L : ℕ → set G := λ n, (λ T, T ∪ (g T • K))^[n] K with hL,
  have Lcompact : ∀ n, is_compact (L n),
  { assume n,
    induction n with n IH,
    { exact hK },
    { simp_rw [hL, iterate_succ'],
      apply is_compact.union IH (hK.smul (g (L n))) } },
  have Lclosed : ∀ n, is_closed (L n),
  { assume n,
    induction n with n IH,
    { exact Kclosed },
    { simp_rw [hL, iterate_succ'],
      apply is_closed.union IH (Kclosed.smul (g (L n))) } },
  have M : ∀ n, μ (L n) = (n + 1 : ℕ) * μ K,
  { assume n,
    induction n with n IH,
    { simp only [L, one_mul, algebra_map.coe_one, iterate_zero, id.def] },
    { calc μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) :
        begin
          simp_rw [hL, iterate_succ'],
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurable_set
        end
      ... = ((n + 1) + 1 : ℕ) * μ K :
        by simp only [IH, measure_smul, add_mul, nat.cast_add, algebra_map.coe_one, one_mul] } },
  have N : tendsto (λ n, μ (L n)) at_top (𝓝 (∞ * μ K)),
  { simp_rw [M],
    apply ennreal.tendsto.mul_const _ (or.inl ennreal.top_ne_zero),
    exact ennreal.tendsto_nat_nhds_top.comp (tendsto_add_at_top_nat _) },
  simp only [ennreal.top_mul, K_pos.ne', if_false] at N,
  apply top_le_iff.1,
  exact le_of_tendsto' N (λ n, measure_mono (subset_univ _)),
end

end topological_group

section comm_semigroup

variables [comm_semigroup G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `is_mul_left_invariant` as the default hypothesis in abelian groups. -/
@[priority 100, to_additive is_add_left_invariant.is_add_right_invariant "In an abelian additive
group every left invariant measure is also right-invariant. We don't declare the converse as an
instance, since that would loop type-class inference, and we use `is_add_left_invariant` as the
default hypothesis in abelian groups."]
instance is_mul_left_invariant.is_mul_right_invariant {μ : measure G} [is_mul_left_invariant μ] :
  is_mul_right_invariant μ :=
⟨λ g, by simp_rw [mul_comm, map_mul_left_eq_self]⟩


end comm_semigroup

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

/-- The image of a Haar measure under a continuous surjective proper group homomorphism is again
a Haar measure. See also `mul_equiv.is_haar_measure_map`. -/
@[to_additive "The image of an additive Haar measure under a continuous surjective proper additive
group homomorphism is again an additive Haar measure. See also
`add_equiv.is_add_haar_measure_map`."]
lemma is_haar_measure_map [borel_space G] [topological_group G] {H : Type*} [group H]
  [topological_space H] [measurable_space H] [borel_space H] [t2_space H] [topological_group H]
  (f : G →* H) (hf : continuous f) (h_surj : surjective f)
  (h_prop : tendsto f (cocompact G) (cocompact H)) :
  is_haar_measure (measure.map f μ) :=
{ to_is_mul_left_invariant := is_mul_left_invariant_map f.to_mul_hom hf.measurable h_surj,
  lt_top_of_is_compact := begin
    assume K hK,
    rw map_apply hf.measurable hK.measurable_set,
    exact is_compact.measure_lt_top
      ((⟨⟨f, hf⟩, h_prop⟩ : cocompact_map G H).is_compact_preimage hK),
  end,
  to_is_open_pos_measure := hf.is_open_pos_measure_map h_surj }

/-- A convenience wrapper for `measure_theory.measure.is_haar_measure_map`. -/
@[to_additive "A convenience wrapper for `measure_theory.measure.is_add_haar_measure_map`."]
lemma _root_.mul_equiv.is_haar_measure_map
  [borel_space G] [topological_group G] {H : Type*} [group H]
  [topological_space H] [measurable_space H] [borel_space H] [t2_space H] [topological_group H]
  (e : G ≃* H) (he : continuous e) (hesymm : continuous e.symm) :
  is_haar_measure (measure.map e μ) :=
is_haar_measure_map μ (e : G →* H) he e.surjective
  ({ .. e } : G ≃ₜ H).to_cocompact_map.cocompact_tendsto'

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[priority 100, to_additive "A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority]"]
instance is_haar_measure.sigma_finite [sigma_compact_space G] : sigma_finite μ :=
⟨⟨{ set := compact_covering G,
  set_mem := λ n, mem_univ _,
  finite := λ n, is_compact.measure_lt_top $ is_compact_compact_covering G n,
  spanning := Union_compact_covering G }⟩⟩

@[to_additive]
instance {G : Type*} [group G] [topological_space G] {mG : measurable_space G}
  {H : Type*} [group H] [topological_space H] {mH : measurable_space H}
  (μ : measure G) (ν : measure H) [is_haar_measure μ] [is_haar_measure ν]
  [sigma_finite μ] [sigma_finite ν]
  [has_measurable_mul G] [has_measurable_mul H] :
  is_haar_measure (μ.prod ν) := {}

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
example {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [nontrivial E]
  [finite_dimensional ℝ E] [measurable_space E] [borel_space E] (μ : measure E)
  [is_add_haar_measure μ] :
  has_no_atoms μ := by apply_instance

end

variables [nontrivially_normed_field 𝕜] [topological_space G] [topological_space H]
  [add_comm_group G] [add_comm_group H] [topological_add_group G] [topological_add_group H]
  [module 𝕜 G] [module 𝕜 H] (μ : measure G) [is_add_haar_measure μ] [borel_space G] [borel_space H]
  [t2_space H]

instance map_continuous_linear_equiv.is_add_haar_measure (e : G ≃L[𝕜] H) :
  is_add_haar_measure (μ.map e) :=
e.to_add_equiv.is_add_haar_measure_map _ e.continuous e.symm.continuous

variables [complete_space 𝕜] [t2_space G] [finite_dimensional 𝕜 G] [has_continuous_smul 𝕜 G]
  [has_continuous_smul 𝕜 H]

instance map_linear_equiv.is_add_haar_measure (e : G ≃ₗ[𝕜] H) : is_add_haar_measure (μ.map e) :=
map_continuous_linear_equiv.is_add_haar_measure _ e.to_continuous_linear_equiv

end measure
end haar

end measure_theory
