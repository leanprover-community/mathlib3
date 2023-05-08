/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.zfc.basic

/-!
# Von Neumann ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`. We currently only have an initial development of transitive sets.

Further development can be found on the branch `von_neumann_v2`.

## Definitions

- `Set.is_transitive` means that every element of a set is a subset.

## Todo

- Define von Neumann ordinals.
- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `set_theory/ordinal/arithmetic.lean`.
-/

universe u

variables {x y z : Set.{u}}

namespace Set

/-- A transitive set is one where every element is a subset. -/
def is_transitive (x : Set) : Prop := ∀ y ∈ x, y ⊆ x

@[simp] theorem empty_is_transitive : is_transitive ∅ := λ y hy, (not_mem_empty y hy).elim

theorem is_transitive.subset_of_mem (h : x.is_transitive) : y ∈ x → y ⊆ x := h y

theorem is_transitive_iff_mem_trans : z.is_transitive ↔ ∀ {x y : Set}, x ∈ y → y ∈ z → x ∈ z :=
⟨λ h x y hx hy, h.subset_of_mem hy hx, λ H x hx y hy, H hy hx⟩

alias is_transitive_iff_mem_trans ↔ is_transitive.mem_trans _

protected theorem is_transitive.inter (hx : x.is_transitive) (hy : y.is_transitive) :
  (x ∩ y).is_transitive :=
λ z hz w hw, by { rw mem_inter at hz ⊢, exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩ }

protected theorem is_transitive.sUnion (h : x.is_transitive) : (⋃₀ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩,
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)
end

theorem is_transitive.sUnion' (H : ∀ y ∈ x, is_transitive y) : (⋃₀ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩,
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw
end

protected theorem is_transitive.union (hx : x.is_transitive) (hy : y.is_transitive) :
  (x ∪ y).is_transitive :=
begin
  rw ←sUnion_pair,
  apply is_transitive.sUnion' (λ z, _),
  rw mem_pair,
  rintro (rfl | rfl),
  assumption'
end

protected theorem is_transitive.powerset (h : x.is_transitive) : (powerset x).is_transitive :=
λ y hy z hz, by { rw mem_powerset at ⊢ hy, exact h.subset_of_mem (hy hz) }

theorem is_transitive_iff_sUnion_subset : x.is_transitive ↔ ⋃₀ x ⊆ x :=
⟨λ h y hy, by { rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩, exact h.mem_trans hz' hz },
  λ H y hy z hz, H $ mem_sUnion_of_mem hz hy⟩

alias is_transitive_iff_sUnion_subset ↔ is_transitive.sUnion_subset _

theorem is_transitive_iff_subset_powerset : x.is_transitive ↔ x ⊆ powerset x :=
⟨λ h y hy, mem_powerset.2 $ h.subset_of_mem hy, λ H y hy z hz, mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

end Set
