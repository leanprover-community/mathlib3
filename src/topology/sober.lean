/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.separation
import topology.continuous_function.basic

/-!
# Sober spaces

A quasi-sober space is a topological space where every
irreducible closed subset has a generic point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[quasi_sober α] [t0_space α]`.

## Main definition

* `specializes` : `specializes x y` (`x ⤳ y`) means that `x` specializes to `y`, i.e.
  `y` is in the closure of `x`.
* `specialization_preorder` : specialization gives a preorder on a topological space.
* `specialization_order` : specialization gives a partial order on a T0 space.
* `is_generic_point` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `quasi_sober` : A space is quasi-sober if every irreducible closed subset has a generic point.

-/

variables {α β : Type*} [topological_space α] [topological_space β]

section specialize_order

/-- `x` specializes to `y` if `y` is in the closure of `x`. The notation used is `x ⤳ y`. -/
def specializes (x y : α) : Prop := y ∈ closure ({x} : set α)

infix ` ⤳ `:300 := specializes

lemma specializes_def (x y : α) : x ⤳ y ↔ y ∈ closure ({x} : set α) := iff.rfl

lemma specializes_iff_closure_subset {x y : α} :
  x ⤳ y ↔ closure ({y} : set α) ⊆ closure ({x} : set α) :=
is_closed_closure.mem_iff_closure_subset

lemma specializes_rfl {x : α} : x ⤳ x := subset_closure (set.mem_singleton x)

lemma specializes_refl (x : α) : x ⤳ x := specializes_rfl

lemma specializes.trans {x y z : α} : x ⤳ y → y ⤳ z → x ⤳ z :=
by { simp_rw specializes_iff_closure_subset, exact λ a b, b.trans a }

lemma specializes_iff_forall_closed {x y : α} :
  x ⤳ y ↔ ∀ (Z : set α) (h : is_closed Z), x ∈ Z → y ∈ Z :=
begin
  split,
  { intros h Z hZ,
    rw [hZ.mem_iff_closure_subset, hZ.mem_iff_closure_subset],
    exact (specializes_iff_closure_subset.mp h).trans },
  { intro h, exact h _ is_closed_closure (subset_closure $ set.mem_singleton x) }
end

lemma specializes_iff_forall_open {x y : α} :
  x ⤳ y ↔ ∀ (U : set α) (h : is_open U), y ∈ U → x ∈ U :=
begin
  rw specializes_iff_forall_closed,
  exact ⟨λ h U hU, not_imp_not.mp (h _ (is_closed_compl_iff.mpr hU)),
    λ h U hU, not_imp_not.mp (h _ (is_open_compl_iff.mpr hU))⟩,
end

lemma indistinguishable_iff_specializes_and (x y : α) :
  indistinguishable x y ↔ x ⤳ y ∧ y ⤳ x :=
(indistinguishable_iff_closure x y).trans (and_comm _ _)

lemma specializes_antisymm [t0_space α] (x y : α) : x ⤳ y → y ⤳ x → x = y :=
λ h₁ h₂, ((indistinguishable_iff_specializes_and _ _).mpr ⟨h₁, h₂⟩).eq

lemma specializes.map {x y : α} (h : x ⤳ y) {f : α → β} (hf : continuous f) : f x ⤳ f y :=
begin
  rw [specializes_def, ← set.image_singleton],
  exact image_closure_subset_closure_image hf ⟨_, h, rfl⟩,
end

lemma continuous_map.map_specialization {x y : α} (h : x ⤳ y) (f : C(α, β)) : f x ⤳ f y :=
h.map f.2

lemma specializes.eq [t1_space α] {x y : α} (h : x ⤳ y) : x = y :=
(set.mem_singleton_iff.mp
  ((specializes_iff_forall_closed.mp h) _ (t1_space.t1 _) (set.mem_singleton _))).symm

@[simp] lemma specializes_iff_eq [t1_space α] {x y : α} : x ⤳ y ↔ x = y :=
⟨specializes.eq, λ h, h ▸ specializes_refl _⟩

variable (α)

/-- Specialization forms a preorder on the topological space. -/
def specialization_preorder : preorder α :=
{ le := λ x y, y ⤳ x,
  le_refl := λ x, specializes_refl x,
  le_trans := λ _ _ _ h₁ h₂, specializes.trans h₂ h₁ }

local attribute [instance] specialization_preorder

/-- Specialization forms a partial order on a t0 topological space. -/
def specialization_order [t0_space α] : partial_order α :=
{ le_antisymm := λ _ _ h₁ h₂, specializes_antisymm _ _ h₂ h₁,
  .. specialization_preorder α }

variable {α}

lemma specialization_order.monotone_of_continuous (f : α → β) (hf : continuous f) : monotone f :=
λ x y h, specializes.map h hf

end specialize_order

section generic_point

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
def is_generic_point (x : α) (S : set α) : Prop := closure ({x} : set α) = S

lemma is_generic_point_def {x : α} {S : set α} : is_generic_point x S ↔ closure ({x} : set α) = S :=
iff.rfl

lemma is_generic_point.def {x : α} {S : set α} (h : is_generic_point x S) :
  closure ({x} : set α) = S := h

lemma is_generic_point_closure {x : α} : is_generic_point x (closure ({x} : set α)) := refl _

variables {x : α} {S : set α} (h : is_generic_point x S)

include h

lemma is_generic_point.specializes {y : α} (h' : y ∈ S) :
  x ⤳ y := by rwa ← h.def at h'

lemma is_generic_point.mem : x ∈ S :=
h.def ▸ subset_closure (set.mem_singleton x)

lemma is_generic_point.is_closed : is_closed S :=
h.def ▸ is_closed_closure

lemma is_generic_point.is_irreducible : is_irreducible S :=
h.def ▸ is_irreducible_singleton.closure

lemma is_generic_point.eq [t0_space α] {y : α} (h' : is_generic_point y S) : x = y :=
specializes_antisymm _ _ (h.specializes h'.mem) (h'.specializes h.mem)

lemma is_generic_point.mem_open_set_iff
  {U : set α} (hU : is_open U) : x ∈ U ↔ (S ∩ U).nonempty :=
⟨λ h', ⟨x, h.mem, h'⟩,
    λ h', specializes_iff_forall_open.mp (h.specializes h'.some_spec.1) U hU h'.some_spec.2⟩

lemma is_generic_point.disjoint_iff
  {U : set α} (hU : is_open U) : disjoint S U ↔ x ∉ U :=
by rw [h.mem_open_set_iff hU, ← set.ne_empty_iff_nonempty, not_not, set.disjoint_iff_inter_eq_empty]

lemma is_generic_point.mem_closed_set_iff
  {Z : set α} (hZ : is_closed Z) : x ∈ Z ↔ S ⊆ Z :=
by rw [← is_generic_point_def.mp h, hZ.closure_subset_iff, set.singleton_subset_iff]

lemma is_generic_point.image {f : α → β} (hf : continuous f) :
  is_generic_point (f x) (closure (f '' S)) :=
begin
  rw [is_generic_point_def, ← is_generic_point_def.mp h],
  apply le_antisymm,
  { exact closure_mono
      (set.singleton_subset_iff.mpr ⟨_, subset_closure $ set.mem_singleton x, rfl⟩) },
  { convert is_closed_closure.closure_subset_iff.mpr (image_closure_subset_closure_image hf),
    rw set.image_singleton }
end

omit h

lemma is_generic_point_iff_forall_closed {x : α} {S : set α} (hS : is_closed S) (hxS : x ∈ S) :
  is_generic_point x S ↔ ∀ (Z : set α) (hZ : is_closed Z) (hxZ : x ∈ Z), S ⊆ Z :=
begin
  split,
  { intros h Z hZ hxZ, exact (h.mem_closed_set_iff hZ).mp hxZ },
  { intro h,
    apply le_antisymm,
    { rwa [set.le_eq_subset, hS.closure_subset_iff, set.singleton_subset_iff] },
    { exact h _ is_closed_closure (subset_closure $ set.mem_singleton x) } }
end

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
  simp only [set.image_preimage_eq_inter_range, set.mem_inter_eq, and.congr_left_iff],
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
  obtain ⟨x, rfl⟩ := (is_irreducible_iff_singleton S).mp h,
  exact ⟨x, (t1_space.t1 x).closure_eq⟩
end

end sober
