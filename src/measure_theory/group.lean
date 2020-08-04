/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.borel_space
/-!
# Measures on Groups

We develop some properties of measures on (topological) groups.

* We define properties on measures: left and right invariant measures.
* We define the conjugate `A ↦ μ (A⁻¹)` of a measure `μ`, and show that it is right invariant iff
  `μ` is left invariant.
-/
noncomputable theory

open has_inv set function measure_theory.measure measurable_space
variables {α β : Type*} {G H : Type*}

namespace opposite
instance [m : measurable_space G] : measurable_space Gᵒᵖ := m.map op

lemma opposite_eq_comap [m : measurable_space G] : opposite.measurable_space = m.comap unop :=
(comap_eq_map equiv_to_opposite).symm

lemma measurable_op [measurable_space G] : measurable (op : G → Gᵒᵖ) := λ _ h, h
lemma measurable_unop [measurable_space G] : measurable (unop : Gᵒᵖ → G) := λ _ h, h

/-- The map `G ≃ Gᵒᵖ` is a measurable equivalence -/
def measurable_equiv_to_opposite [measurable_space G] : measurable_equiv G Gᵒᵖ :=
{ measurable_to_fun := measurable_op,
  measurable_inv_fun := measurable_unop,
  ..equiv_to_opposite }

lemma borel_comap [m : topological_space H] (f : G → H) : @borel G (m.induced f) =
  (@borel H m).comap f :=
by { dsimp only [borel], rw [comap_generate_from], refl }

instance [measurable_space G] [topological_space G] [borel_space G] : borel_space Gᵒᵖ :=
{ measurable_eq :=
  by { rw [opposite_eq_induced, borel_comap, opposite_eq_comap, ‹borel_space G›.measurable_eq] } }

end opposite
open opposite

lemma measurable_equiv.is_measurable_iff [measurable_space α] [measurable_space β]
  (f : measurable_equiv α β) {s : set β} : is_measurable (f ⁻¹' s) ↔ is_measurable s :=
begin
  split,
  { intro h, convert f.symm.measurable h, rw [preimage_preimage], convert preimage_id'.symm, ext x,
    exact f.right_inv x },
  exact λ h, f.measurable h
end

namespace measure_theory

section mul

variables [measurable_space G] [has_mul G]

/-- A measure `μ` on a topological group is left invariant if
  for all measurable sets `s` and all `g`, we have `μ (gs) = μ s`,
  where `gs` denotes the translate of `s` by left multiplication with `g`. -/
def is_left_invariant (μ : set G → ennreal) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, g * h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant if
  for all measurable sets `s` and all `g`, we have `μ (sg) = μ s`,
  where `sg` denotes the translate of `s` by right multiplication with `g`. -/
def is_right_invariant (μ : set G → ennreal) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, h * g) ⁻¹' A) = μ A

end mul

namespace measure

section mul
variables [measurable_space G] [has_mul G] [topological_space G] [has_continuous_mul G]
  [borel_space G]

lemma map_mul_left_eq_self {μ : measure G} :
  (∀ g, measure.map ((*) g) μ = μ) ↔ is_left_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_mul_left g) hA]
end

lemma map_mul_right_eq_self {μ : measure G} :
  (∀ g, measure.map (λ h, h * g) μ = μ) ↔ is_right_invariant μ :=
begin
  apply forall_congr, intro g, rw [measure.ext_iff], apply forall_congr, intro A,
  apply forall_congr, intro hA, rw [map_apply (measurable_mul_right g) hA]
end

@[simp] lemma is_right_invariant_map_op {μ : measure G} :
  is_right_invariant (map op μ) ↔ is_left_invariant μ :=
begin
  symmetry, apply (equiv_to_opposite).forall_congr, intro g,
  apply (equiv.set.congr equiv_to_opposite).forall_congr, intro A,
  dsimp [equiv.set.congr], simp only [equiv.image_eq_preimage],
  symmetry, refine imp_congr_ctx measurable_equiv_to_opposite.is_measurable_iff _, intro hA,
  dsimp [equiv_to_opposite], rw [map_apply measurable_op (measurable_unop hA)],
  rw [map_apply measurable_op (measurable_mul_right (op g) (measurable_unop hA))],
  simp only [preimage_preimage, unop_op, preimage_id', unop_mul]
end

@[simp] lemma is_left_invariant_map_op {μ : measure G} :
  is_left_invariant (map op μ) ↔ is_right_invariant μ :=
begin
  symmetry, apply (equiv_to_opposite).forall_congr, intro g,
  apply (equiv.set.congr equiv_to_opposite).forall_congr, intro A,
  dsimp [equiv.set.congr], simp only [equiv.image_eq_preimage],
  symmetry, refine imp_congr_ctx measurable_equiv_to_opposite.is_measurable_iff _, intro hA,
  dsimp [equiv_to_opposite], rw [map_apply measurable_op (measurable_unop hA)],
  rw [map_apply measurable_op (measurable_mul_left (op g) (measurable_unop hA))],
  simp only [preimage_preimage, unop_op, preimage_id', unop_mul]
end

end mul

variables [measurable_space G] [group G]

/-- The conjugate of a measure on a topological group.
  Defined to be `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
protected def conj (μ : measure G) : measure G :=
measure.map inv μ

variables [topological_space G] [topological_group G] [borel_space G]

lemma conj_apply (μ : measure G) {s : set G} (hs : is_measurable s) :
  μ.conj s = μ s⁻¹ :=
by { unfold measure.conj, rw [measure.map_apply measurable_inv hs, inv_preimage] }

@[simp] lemma conj_conj (μ : measure G) : μ.conj.conj = μ :=
begin
  ext1 s hs, rw [μ.conj.conj_apply hs, μ.conj_apply, set.inv_inv], exact measurable_inv hs
end

variables {μ : measure G}

lemma regular.conj [t2_space G] (hμ : μ.regular) : μ.conj.regular :=
hμ.map (homeomorph.inv G)

end measure

section conj
variables [measurable_space G] [group G] [topological_space G] [topological_group G] [borel_space G]
  {μ : measure G}

@[simp] lemma regular_conj_iff [t2_space G] : μ.conj.regular ↔ μ.regular :=
by { refine ⟨λ h, _, measure.regular.conj⟩, rw ←μ.conj_conj, exact measure.regular.conj h }

lemma is_right_invariant_conj' (h : is_left_invariant μ) :
  is_right_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_right g hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv hA) using 2,
  simp only [←preimage_comp, ← inv_preimage],
  apply preimage_congr, intro h, simp only [mul_inv_rev, comp_app, inv_inv]
end

lemma is_left_invariant_conj' (h : is_right_invariant μ) : is_left_invariant μ.conj :=
begin
  rw [← measure.is_right_invariant_map_op, measure.conj, measure.map_map],
  show is_right_invariant (map (inv ∘ op) μ),
  rw [← measure.map_map], apply is_right_invariant_conj', rwa measure.is_left_invariant_map_op,
  all_goals { exact measurable_op <|> exact measurable_inv }
end

@[simp] lemma is_right_invariant_conj : is_right_invariant μ.conj ↔ is_left_invariant μ :=
by { refine ⟨λ h, _, is_right_invariant_conj'⟩, rw ←μ.conj_conj, exact is_left_invariant_conj' h }

@[simp] lemma is_left_invariant_conj : is_left_invariant μ.conj ↔ is_right_invariant μ :=
by { refine ⟨λ h, _, is_left_invariant_conj'⟩, rw ←μ.conj_conj, exact is_right_invariant_conj' h }

end conj

end measure_theory
