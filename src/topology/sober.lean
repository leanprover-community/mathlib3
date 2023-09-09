/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.separation

/-!
# Sober spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A quasi-sober space is a topological space where every
irreducible closed subset has a generic point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[quasi_sober α] [t0_space α]`.

## Main definition

* `is_generic_point` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `quasi_sober` : A space is quasi-sober if every irreducible closed subset has a generic point.

-/

open set

variables {α β : Type*} [topological_space α] [topological_space β]

section generic_point

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
def is_generic_point (x : α) (S : set α) : Prop := closure ({x} : set α) = S

lemma is_generic_point_def {x : α} {S : set α} : is_generic_point x S ↔ closure ({x} : set α) = S :=
iff.rfl

lemma is_generic_point.def {x : α} {S : set α} (h : is_generic_point x S) :
  closure ({x} : set α) = S := h

lemma is_generic_point_closure {x : α} : is_generic_point x (closure ({x} : set α)) := refl _

variables {x y : α} {S U Z : set α}

lemma is_generic_point_iff_specializes :
  is_generic_point x S ↔ ∀ y, x ⤳ y ↔ y ∈ S :=
by simp only [specializes_iff_mem_closure, is_generic_point, set.ext_iff]

namespace is_generic_point

lemma specializes_iff_mem (h : is_generic_point x S) : x ⤳ y ↔ y ∈ S :=
is_generic_point_iff_specializes.1 h y

lemma specializes (h : is_generic_point x S) (h' : y ∈ S) : x ⤳ y :=
h.specializes_iff_mem.2 h'

lemma mem (h : is_generic_point x S) : x ∈ S :=
h.specializes_iff_mem.1 specializes_rfl

protected lemma is_closed (h : is_generic_point x S) : is_closed S :=
h.def ▸ is_closed_closure

protected lemma is_irreducible (h : is_generic_point x S) : is_irreducible S :=
h.def ▸ is_irreducible_singleton.closure

/-- In a T₀ space, each set has at most one generic point. -/
protected lemma eq [t0_space α] (h : is_generic_point x S) (h' : is_generic_point y S) : x = y :=
((h.specializes h'.mem).antisymm (h'.specializes h.mem)).eq

lemma mem_open_set_iff (h : is_generic_point x S) (hU : is_open U) :
  x ∈ U ↔ (S ∩ U).nonempty :=
⟨λ h', ⟨x, h.mem, h'⟩, λ ⟨y, hyS, hyU⟩, (h.specializes hyS).mem_open hU hyU⟩

lemma disjoint_iff (h : is_generic_point x S) (hU : is_open U) : disjoint S U ↔ x ∉ U :=
by rw [h.mem_open_set_iff hU, ← not_disjoint_iff_nonempty_inter, not_not]

lemma mem_closed_set_iff (h : is_generic_point x S) (hZ : is_closed Z) :
  x ∈ Z ↔ S ⊆ Z :=
by rw [← h.def, hZ.closure_subset_iff, singleton_subset_iff]

protected lemma image (h : is_generic_point x S) {f : α → β} (hf : continuous f) :
  is_generic_point (f x) (closure (f '' S)) :=
begin
  rw [is_generic_point_def, ← h.def, ← image_singleton],
  exact subset.antisymm (closure_mono (image_subset _ subset_closure))
    (closure_minimal (image_closure_subset_closure_image hf) is_closed_closure)
end

end is_generic_point

lemma is_generic_point_iff_forall_closed (hS : is_closed S) (hxS : x ∈ S) :
  is_generic_point x S ↔ ∀ Z : set α, is_closed Z → x ∈ Z → S ⊆ Z :=
have closure {x} ⊆ S, from closure_minimal (singleton_subset_iff.2 hxS) hS,
by simp_rw [is_generic_point, subset_antisymm_iff, this, true_and, closure, subset_sInter_iff,
  mem_set_of_eq, and_imp, singleton_subset_iff]

end generic_point

section sober

/-- A space is sober if every irreducible closed subset has a generic point. -/
@[mk_iff]
class quasi_sober (α : Type*) [topological_space α] : Prop :=
(sober : ∀ {S : set α} (hS₁ : is_irreducible S) (hS₂ : is_closed S), ∃ x, is_generic_point x S)

/-- A generic point of the closure of an irreducible space. -/
noncomputable
def is_irreducible.generic_point [quasi_sober α] {S : set α} (hS : is_irreducible S) : α :=
(quasi_sober.sober hS.closure is_closed_closure).some

lemma is_irreducible.generic_point_spec [quasi_sober α] {S : set α} (hS : is_irreducible S) :
  is_generic_point hS.generic_point (closure S) :=
(quasi_sober.sober hS.closure is_closed_closure).some_spec

@[simp] lemma is_irreducible.generic_point_closure_eq [quasi_sober α] {S : set α}
  (hS : is_irreducible S) : closure ({hS.generic_point} : set α) = closure S :=
hS.generic_point_spec

variable (α)

/-- A generic point of a sober irreducible space. -/
noncomputable
def generic_point [quasi_sober α] [irreducible_space α] : α :=
(irreducible_space.is_irreducible_univ α).generic_point

lemma generic_point_spec [quasi_sober α] [irreducible_space α] :
  is_generic_point (generic_point α) ⊤ :=
by simpa using (irreducible_space.is_irreducible_univ α).generic_point_spec

@[simp]
lemma generic_point_closure [quasi_sober α] [irreducible_space α] :
  closure ({generic_point α} : set α) = ⊤ := generic_point_spec α

variable {α}

lemma generic_point_specializes [quasi_sober α] [irreducible_space α] (x : α) :
  generic_point α ⤳ x := (is_irreducible.generic_point_spec _).specializes (by simp)

local attribute [instance, priority 10] specialization_order

/-- The closed irreducible subsets of a sober space bijects with the points of the space. -/
noncomputable
def irreducible_set_equiv_points [quasi_sober α] [t0_space α] :
  { s : set α | is_irreducible s ∧ is_closed s } ≃o α :=
{ to_fun := λ s, s.prop.1.generic_point,
  inv_fun := λ x, ⟨closure ({x} : set α), is_irreducible_singleton.closure, is_closed_closure⟩,
  left_inv := λ s,
    subtype.eq $ eq.trans (s.prop.1.generic_point_spec) $ closure_eq_iff_is_closed.mpr s.2.2,
  right_inv := λ x, is_irreducible_singleton.closure.generic_point_spec.eq
      (by { convert is_generic_point_closure using 1, rw closure_closure }),
  map_rel_iff' := λ s t, by { change _ ⤳ _ ↔ _, rw specializes_iff_closure_subset,
    simp [s.prop.2.closure_eq, t.prop.2.closure_eq, ← subtype.coe_le_coe] } }

lemma closed_embedding.quasi_sober {f : α → β} (hf : closed_embedding f) [quasi_sober β] :
  quasi_sober α :=
begin
  constructor,
  intros S hS hS',
  have hS'' := hS.image f hf.continuous.continuous_on,
  obtain ⟨x, hx⟩ := quasi_sober.sober hS'' (hf.is_closed_map _ hS'),
  obtain ⟨y, hy, rfl⟩ := hx.mem,
  use y,
  change _ = _ at hx,
  apply set.image_injective.mpr hf.inj,
  rw [← hx, ← hf.closure_image_eq, set.image_singleton]
end

lemma open_embedding.quasi_sober {f : α → β} (hf : open_embedding f) [quasi_sober β] :
  quasi_sober α :=
begin
  constructor,
  intros S hS hS',
  have hS'' := hS.image f hf.continuous.continuous_on,
  obtain ⟨x, hx⟩ := quasi_sober.sober hS''.closure is_closed_closure,
  obtain ⟨T, hT, rfl⟩ := hf.to_inducing.is_closed_iff.mp hS',
  rw set.image_preimage_eq_inter_range at hx hS'',
  have hxT : x ∈ T,
  { rw ← hT.closure_eq, exact closure_mono (set.inter_subset_left _ _) hx.mem },
  have hxU : x ∈ set.range f,
  { rw hx.mem_open_set_iff hf.open_range,
    refine set.nonempty.mono _ hS''.1,
    simpa using subset_closure },
  rcases hxU with ⟨y, rfl⟩,
  use y,
  change _ = _,
  rw [hf.to_embedding.closure_eq_preimage_closure_image,
    set.image_singleton, (show _ = _, from hx)],
  apply set.image_injective.mpr hf.inj,
  ext z,
  simp only [set.image_preimage_eq_inter_range, set.mem_inter_iff, and.congr_left_iff],
  exact λ hy, ⟨λ h, hT.closure_eq ▸ closure_mono (set.inter_subset_left _ _) h,
    λ h, subset_closure ⟨h, hy⟩⟩
end

/-- A space is quasi sober if it can be covered by open quasi sober subsets. -/
lemma quasi_sober_of_open_cover (S : set (set α)) (hS : ∀ s : S, is_open (s : set α))
  [hS' : ∀ s : S, quasi_sober s] (hS'' : ⋃₀ S = ⊤) : quasi_sober α :=
begin
  rw quasi_sober_iff,
  intros t h h',
  obtain ⟨x, hx⟩ := h.1,
  obtain ⟨U, hU, hU'⟩ : x ∈ ⋃₀S := by { rw hS'', trivial },
  haveI : quasi_sober U := hS' ⟨U, hU⟩,
  have H : is_preirreducible (coe ⁻¹' t : set U) :=
    h.2.preimage (hS ⟨U, hU⟩).open_embedding_subtype_coe,
  replace H : is_irreducible (coe ⁻¹' t : set U) := ⟨⟨⟨x, hU'⟩, by simpa using hx⟩, H⟩,
  use H.generic_point,
  have := continuous_subtype_coe.closure_preimage_subset _ H.generic_point_spec.mem,
  rw h'.closure_eq at this,
  apply le_antisymm,
  { apply h'.closure_subset_iff.mpr, simpa using this },
  rw [← set.image_singleton, ← closure_closure],
  have := closure_mono (image_closure_subset_closure_image (@continuous_subtype_coe α _ U)),
  refine set.subset.trans _ this,
  rw H.generic_point_spec.def,
  refine (subset_closure_inter_of_is_preirreducible_of_is_open
    h.2 (hS ⟨U, hU⟩) ⟨x, hx, hU'⟩).trans (closure_mono _),
  rw ← subtype.image_preimage_coe,
  exact set.image_subset _ subset_closure,
end

@[priority 100]
instance t2_space.quasi_sober [t2_space α] : quasi_sober α :=
begin
  constructor,
  rintro S h -,
  obtain ⟨x, rfl⟩ := is_irreducible_iff_singleton.mp h,
  exact ⟨x, closure_singleton⟩
end

end sober
