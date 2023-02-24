/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.intervals.ord_connected
import tactic.wlog

/-!
# Order connected components of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `set.ord_connected_component s x` to be the set of `y` such that
`set.uIcc x y ⊆ s` and prove some basic facts about this definition. At the moment of writing,
this construction is used only to prove that any linear order with order topology is a T₅ space,
so we only add API needed for this lemma.
-/

open function order_dual
open_locale interval

namespace set

variables {α : Type*} [linear_order α] {s t : set α} {x y z : α}

/-- Order-connected component of a point `x` in a set `s`. It is defined as the set of `y` such that
`set.uIcc x y ⊆ s`. Note that it is empty if and only if `x ∉ s`. -/
def ord_connected_component (s : set α) (x : α) : set α := {y | [x, y] ⊆ s}

lemma mem_ord_connected_component : y ∈ ord_connected_component s x ↔ [x, y] ⊆ s := iff.rfl

lemma dual_ord_connected_component :
  ord_connected_component (of_dual ⁻¹' s) (to_dual x) = of_dual ⁻¹' (ord_connected_component s x) :=
ext $ to_dual.surjective.forall.2 $ λ x,
  by { rw [mem_ord_connected_component, dual_uIcc], refl }

lemma ord_connected_component_subset : ord_connected_component s x ⊆ s := λ y hy, hy right_mem_uIcc

lemma subset_ord_connected_component {t} [h : ord_connected s] (hs : x ∈ s) (ht : s ⊆ t) :
  s ⊆ ord_connected_component t x :=
λ y hy, (h.uIcc_subset hs hy).trans ht

@[simp] lemma self_mem_ord_connected_component : x ∈ ord_connected_component s x ↔ x ∈ s :=
by rw [mem_ord_connected_component, uIcc_self, singleton_subset_iff]

@[simp] lemma nonempty_ord_connected_component : (ord_connected_component s x).nonempty ↔ x ∈ s :=
⟨λ ⟨y, hy⟩, hy $ left_mem_uIcc, λ h, ⟨x, self_mem_ord_connected_component.2 h⟩⟩

@[simp] lemma ord_connected_component_eq_empty : ord_connected_component s x = ∅ ↔ x ∉ s :=
by rw [← not_nonempty_iff_eq_empty, nonempty_ord_connected_component]

@[simp] lemma ord_connected_component_empty : ord_connected_component ∅ x = ∅ :=
ord_connected_component_eq_empty.2 (not_mem_empty x)

@[simp] lemma ord_connected_component_univ : ord_connected_component univ x = univ :=
by simp [ord_connected_component]

lemma ord_connected_component_inter (s t : set α) (x : α) :
  ord_connected_component (s ∩ t) x = ord_connected_component s x ∩ ord_connected_component t x :=
by simp [ord_connected_component, set_of_and]

lemma mem_ord_connected_component_comm :
  y ∈ ord_connected_component s x ↔ x ∈ ord_connected_component s y :=
by rw [mem_ord_connected_component, mem_ord_connected_component, uIcc_comm]

lemma mem_ord_connected_component_trans (hxy : y ∈ ord_connected_component s x)
  (hyz : z ∈ ord_connected_component s y) : z ∈ ord_connected_component s x :=
calc [x, z] ⊆ [x, y] ∪ [y, z] : uIcc_subset_uIcc_union_uIcc
... ⊆ s : union_subset hxy hyz

lemma ord_connected_component_eq (h : [x, y] ⊆ s) :
  ord_connected_component s x = ord_connected_component s y :=
ext $ λ z, ⟨mem_ord_connected_component_trans (mem_ord_connected_component_comm.2 h),
  mem_ord_connected_component_trans h⟩

instance : ord_connected (ord_connected_component s x) :=
ord_connected_of_uIcc_subset_left $ λ y hy z hz, (uIcc_subset_uIcc_left hz).trans hy

/-- Projection from `s : set α` to `α` sending each order connected component of `s` to a single
point of this component. -/
noncomputable def ord_connected_proj (s : set α) : s → α :=
λ x : s, (nonempty_ord_connected_component.2 x.prop).some

lemma ord_connected_proj_mem_ord_connected_component (s : set α) (x : s) :
  ord_connected_proj s x ∈ ord_connected_component s x :=
nonempty.some_mem _

lemma mem_ord_connected_component_ord_connected_proj (s : set α) (x : s) :
  ↑x ∈ ord_connected_component s (ord_connected_proj s x) :=
mem_ord_connected_component_comm.2 $ ord_connected_proj_mem_ord_connected_component s x

@[simp] lemma ord_connected_component_ord_connected_proj (s : set α) (x : s) :
  ord_connected_component s (ord_connected_proj s x) = ord_connected_component s x :=
ord_connected_component_eq $ mem_ord_connected_component_ord_connected_proj _ _

@[simp] lemma ord_connected_proj_eq {x y : s} :
  ord_connected_proj s x = ord_connected_proj s y ↔ [(x : α), y] ⊆ s :=
begin
  split; intro h,
  { rw [← mem_ord_connected_component, ← ord_connected_component_ord_connected_proj, h,
      ord_connected_component_ord_connected_proj, self_mem_ord_connected_component],
    exact y.2 },
  { simp only [ord_connected_proj],
    congr' 1,
    exact ord_connected_component_eq h }
end

/-- A set that intersects each order connected component of a set by a single point. Defined as the
range of `set.ord_connected_proj s`. -/
def ord_connected_section (s : set α) : set α := range $ ord_connected_proj s

lemma dual_ord_connected_section (s : set α) :
  ord_connected_section (of_dual ⁻¹' s) = of_dual ⁻¹' (ord_connected_section s) :=
begin
  simp only [ord_connected_section, ord_connected_proj],
  congr' 1 with x, simp only, congr' 1,
  exact dual_ord_connected_component
end

lemma ord_connected_section_subset : ord_connected_section s ⊆ s :=
range_subset_iff.2 $ λ x, ord_connected_component_subset $ nonempty.some_mem _

lemma eq_of_mem_ord_connected_section_of_uIcc_subset (hx : x ∈ ord_connected_section s)
  (hy : y ∈ ord_connected_section s) (h : [x, y] ⊆ s) : x = y :=
begin
  rcases hx with ⟨x, rfl⟩, rcases hy with ⟨y, rfl⟩,
  exact ord_connected_proj_eq.2 (mem_ord_connected_component_trans
    (mem_ord_connected_component_trans (ord_connected_proj_mem_ord_connected_component _ _) h)
    (mem_ord_connected_component_ord_connected_proj _ _))
end

/-- Given two sets `s t : set α`, the set `set.order_separating_set s t` is the set of points that
belong both to some `set.ord_connected_component tᶜ x`, `x ∈ s`, and to some
`set.ord_connected_component sᶜ x`, `x ∈ t`. In the case of two disjoint closed sets, this is the
union of all open intervals $(a, b)$ such that their endpoints belong to different sets. -/
def ord_separating_set (s t : set α) : set α :=
(⋃ x ∈ s, ord_connected_component tᶜ x) ∩ (⋃ x ∈ t, ord_connected_component sᶜ x)

lemma ord_separating_set_comm (s t : set α) :
  ord_separating_set s t = ord_separating_set t s :=
inter_comm _ _

lemma disjoint_left_ord_separating_set : disjoint s (ord_separating_set s t) :=
disjoint.inter_right' _ $ disjoint_Union₂_right.2 $ λ x hx, disjoint_compl_right.mono_right $
  ord_connected_component_subset

lemma disjoint_right_ord_separating_set : disjoint t (ord_separating_set s t) :=
ord_separating_set_comm t s ▸ disjoint_left_ord_separating_set

lemma dual_ord_separating_set :
  ord_separating_set (of_dual ⁻¹' s) (of_dual ⁻¹' t) = of_dual ⁻¹' (ord_separating_set s t) :=
by simp only [ord_separating_set, mem_preimage, ← to_dual.surjective.Union_comp, of_dual_to_dual,
  dual_ord_connected_component, ← preimage_compl, preimage_inter, preimage_Union]

/-- An auxiliary neighborhood that will be used in the proof of `order_topology.t5_space`. -/
def ord_t5_nhd (s t : set α) : set α :=
⋃ x ∈ s, ord_connected_component (tᶜ ∩ (ord_connected_section $ ord_separating_set s t)ᶜ) x

lemma disjoint_ord_t5_nhd : disjoint (ord_t5_nhd s t) (ord_t5_nhd t s) :=
begin
  rw disjoint_iff_inf_le,
  rintro x ⟨hx₁, hx₂⟩,
  rcases mem_Union₂.1 hx₁ with ⟨a, has, ha⟩, clear hx₁,
  rcases mem_Union₂.1 hx₂ with ⟨b, hbt, hb⟩, clear hx₂,
  rw [mem_ord_connected_component, subset_inter_iff] at ha hb,
  wlog hab : a ≤ b,
  { exact this b hbt a has ha hb (le_of_not_le hab) },
  cases ha with ha ha', cases hb with hb hb',
  have hsub : [a, b] ⊆ (ord_separating_set s t).ord_connected_sectionᶜ,
  { rw [ord_separating_set_comm, uIcc_comm] at hb',
    calc [a, b] ⊆ [a, x] ∪ [x, b] : uIcc_subset_uIcc_union_uIcc
    ... ⊆ (ord_separating_set s t).ord_connected_sectionᶜ : union_subset ha' hb' },
  clear ha' hb',
  cases le_total x a with hxa hax,
  { exact hb (Icc_subset_uIcc' ⟨hxa, hab⟩) has },
  cases le_total b x with hbx hxb,
  { exact ha (Icc_subset_uIcc ⟨hab, hbx⟩) hbt },
  have : x ∈ ord_separating_set s t,
  { exact ⟨mem_Union₂.2 ⟨a, has, ha⟩, mem_Union₂.2 ⟨b, hbt, hb⟩⟩ },
  lift x to ord_separating_set s t using this,
  suffices : ord_connected_component (ord_separating_set s t) x ⊆ [a, b],
    from hsub (this $ ord_connected_proj_mem_ord_connected_component _ _) (mem_range_self _),
  rintros y (hy : [↑x, y] ⊆ ord_separating_set s t),
  rw [uIcc_of_le hab, mem_Icc, ← not_lt, ← not_lt],
  exact ⟨λ hya, disjoint_left.1 disjoint_left_ord_separating_set has
    (hy $ Icc_subset_uIcc' ⟨hya.le, hax⟩),
    λ hyb, disjoint_left.1 disjoint_right_ord_separating_set hbt
      (hy $ Icc_subset_uIcc ⟨hxb, hyb.le⟩)⟩
end

end set
