/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import topology.basic
import topology.order
import topology.separation
import data.set.intervals.basic
import order.upper_lower

/-!
# Lower topology

This file introduces the lower topology on a preorder. It is shown that the lower topology on a
partial order is T₀ and the non-empty complements of the upper closures of finite subsets form a
basis.

## Implementation notes

Approach inspired by `order_topology` from topology.algebra.order.basic

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

lower topology, preorder
-/

universe u
variable {α : Type u}

open set topological_space

/--
Type synonym for a preorder equipped with the lower topology
-/
@[derive preorder, nolint unused_arguments]
def lower (α : Type u) [preorder α] := α

instance (α : Type u) [preorder α] [p : nonempty α] : nonempty (lower α) := p

instance (α : Type u) [preorder α] [p : inhabited α] : inhabited (lower α) := p

/--
The lower topology is the topology generated by the complements of the closed intervals to infinity
-/
def lower_topology (α : Type u) [preorder α] : topological_space α :=
generate_from {s | ∃ a, (Ici a)ᶜ = s}

instance lower.topological_space (α : Type u) [preorder α] :
  topological_space (lower α) := lower_topology (lower α)


section pre_order


variable [preorder α]

lemma is_open_iff_generate_Ici_comp {s : set (lower α)} :
  is_open s ↔ generate_open {s | ∃ a, (Ici a)ᶜ = s} s := iff.rfl

/-
Left-closed right-infinite intervals [a,∞) are closed in the lower topology
-/
lemma is_closed_Ici (a : lower α) : is_closed (Ici a) :=
is_open_compl_iff.1 $ generate_open.basic _ ⟨a, rfl⟩

/-
The upper closure of a finite subset is closed in the lower topology
-/
lemma upper_closure_is_closed (F : set (lower α)) (h : F.finite) :
  is_closed (upper_closure F : set (lower α)) :=
begin
  simp only [← upper_set.infi_Ici, upper_set.coe_infi],
  exact is_closed_bUnion h (λ a h₁, is_closed_Ici a),
end

/-
Every subset open in the lower topology is a lower set
-/
lemma lower_open_is_lower {s : set (lower α)} (h : is_open s) : is_lower_set s :=
begin
  rw is_open_iff_generate_Ici_comp at h,
  induction h,
  case generate_open.basic : u h { obtain ⟨a, rfl⟩ := h, exact (is_upper_set_Ici a).compl },
  case univ : { exact is_lower_set_univ },
  case inter : u v hu1 hv1 hu2 hv2 { exact hu2.inter hv2 },
  case sUnion : _ _ ih { exact is_lower_set_sUnion ih },
end

lemma lower_closed_is_upper {s : set (lower α)} (h : is_closed s) : is_upper_set s :=
is_lower_set_compl.1 $ lower_open_is_lower h.is_open_compl
/-
The closure of a singleton {a} in the lower topology is the left-closed right-infinite interval
[a,∞)
-/
lemma lower_topology.closure_singleton (a : lower α) : closure {a} = Ici a :=
subset_antisymm (closure_minimal (λ b h, h.ge) $ is_closed_Ici a) $
  is_upper_set.Ici_subset (lower_closed_is_upper is_closed_closure) (subset_closure rfl)

end pre_order

section partial_order

variable [partial_order α]

/--
The non-empty complements of the upper closures of finite subsets are a collection of lower sets
which form a basis for the lower topology
-/
def lower_basis (α : Type u) [preorder α] :=
{s : set α | ∃ (F : set α), F.finite ∧
  ↑(upper_closure F).compl = s }

lemma lower_basis_is_basis : is_topological_basis (lower_basis (lower α)) :=
begin
  convert is_topological_basis_of_subbasis rfl,
  simp_rw [lower_basis, upper_set.coe_compl, coe_upper_closure, compl_set_of],
  push_neg, simp_rw set_of_forall,
  ext s, split,
  { rintro ⟨F, hF, rfl⟩,
    refine ⟨(λ a, (Ici a)ᶜ) '' F, ⟨hF.image _, image_subset_iff.2 $ λ _ _, ⟨_, rfl⟩⟩, _⟩,
    rw sInter_image, refl },
  { rintro ⟨F, ⟨hF, hs⟩, rfl⟩,
    haveI := hF.to_subtype,
    rw [subset_def, subtype.forall'] at hs,
    choose f he using hs,
    refine ⟨_, finite_range f, set.ext $ λ a, _⟩,
    simp_rw [bInter_range, Inter_subtype, ←compl_set_of, Ici_def, he, mem_Inter₂],
    refl },
end

instance (α : Type u) [p : partial_order α] : partial_order (lower α) := p

/-
The lower topology on a partial order is T₀.
-/
@[priority 90] -- see Note [lower instance priority]
instance lower_topology.to_t0_space : t0_space (lower α) :=
(t0_space_iff_inseparable _).2 $ λ x y h, by simpa only
  [inseparable_iff_closure_eq, lower_topology.closure_singleton, Ici_inj] using h

end partial_order
