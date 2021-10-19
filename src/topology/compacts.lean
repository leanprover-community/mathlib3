/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import topology.homeomorph
/-!
# Compact sets

## Summary

We define the subtype of compact sets in a topological space.

## Main Definitions

- `closeds α` is the type of closed subsets of a topological space `α`.
- `compacts α` is the type of compact subsets of a topological space `α`.
- `nonempty_compacts α` is the type of non-empty compact subsets.
- `positive_compacts α` is the type of compact subsets with non-empty interior.
-/
open set


variables (α : Type*) {β : Type*} [topological_space α] [topological_space β]
namespace topological_space

/-- The type of closed subsets of a topological space. -/
def closeds := {s : set α // is_closed s}

/-- The type of closed subsets is inhabited, with default element the empty set. -/
instance : inhabited (closeds α) := ⟨⟨∅, is_closed_empty ⟩⟩

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts : Type* := { s : set α // is_compact s }

/-- The type of non-empty compact subsets of a topological space. The
non-emptiness will be useful in metric spaces, as we will be able to put
a distance (and not merely an edistance) on this space. -/
def nonempty_compacts := {s : set α // s.nonempty ∧ is_compact s}

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance nonempty_compacts_inhabited [inhabited α] : inhabited (nonempty_compacts α) :=
⟨⟨{default α}, singleton_nonempty (default α), is_compact_singleton ⟩⟩

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
  `nonempty_compacts`. -/
@[nolint has_inhabited_instance]
def positive_compacts: Type* := { s : set α // is_compact s ∧ (interior s).nonempty }

/-- In a nonempty compact space, `set.univ` is a member of `positive_compacts`, the compact sets
with nonempty interior. -/
def positive_compacts_univ {α : Type*} [topological_space α] [compact_space α] [nonempty α] :
  positive_compacts α :=
⟨set.univ, compact_univ, by simp⟩

variables {α}

namespace compacts

instance : semilattice_sup_bot (compacts α) :=
subtype.semilattice_sup_bot is_compact_empty (λ K₁ K₂, is_compact.union)

instance [t2_space α]: semilattice_inf_bot (compacts α) :=
subtype.semilattice_inf_bot is_compact_empty (λ K₁ K₂, is_compact.inter)

instance [t2_space α] : lattice (compacts α) :=
subtype.lattice (λ K₁ K₂, is_compact.union) (λ K₁ K₂, is_compact.inter)

@[simp] lemma bot_val : (⊥ : compacts α).1 = ∅ := rfl

@[simp] lemma sup_val {K₁ K₂ : compacts α} : (K₁ ⊔ K₂).1 = K₁.1 ∪ K₂.1 := rfl

@[ext] protected lemma ext {K₁ K₂ : compacts α} (h : K₁.1 = K₂.1) : K₁ = K₂ :=
subtype.eq h

@[simp] lemma finset_sup_val {β} {K : β → compacts α} {s : finset β} :
  (s.sup K).1 = s.sup (λ x, (K x).1) :=
finset.sup_coe _ _

instance : inhabited (compacts α) := ⟨⊥⟩

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : continuous f) (K : compacts α) : compacts β :=
⟨f '' K.1, K.2.image hf⟩

@[simp] lemma map_val {f : α → β} (hf : continuous f) (K : compacts α) :
  (K.map f hf).1 = f '' K.1 := rfl

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp] protected def equiv (f : α ≃ₜ β) : compacts α ≃ compacts β :=
{ to_fun := compacts.map f f.continuous,
  inv_fun := compacts.map _ f.symm.continuous,
  left_inv := by { intro K, ext1, simp only [map_val, ← image_comp, f.symm_comp_self, image_id] },
  right_inv := by { intro K, ext1,
    simp only [map_val, ← image_comp, f.self_comp_symm, image_id] } }

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
lemma equiv_to_fun_val (f : α ≃ₜ β) (K : compacts α) :
  (compacts.equiv f K).1 = f.symm ⁻¹' K.1 :=
congr_fun (image_eq_preimage_of_inverse f.left_inv f.right_inv) K.1

end compacts

section nonempty_compacts
open topological_space set
variable {α}

instance nonempty_compacts.to_compact_space {p : nonempty_compacts α} : compact_space p.val :=
⟨is_compact_iff_is_compact_univ.1 p.property.2⟩

instance nonempty_compacts.to_nonempty {p : nonempty_compacts α} : nonempty p.val :=
p.property.1.to_subtype

/-- Associate to a nonempty compact subset the corresponding closed subset -/
def nonempty_compacts.to_closeds [t2_space α] : nonempty_compacts α → closeds α :=
set.inclusion $ λ s hs, hs.2.is_closed

end nonempty_compacts

section positive_compacts

variable (α)
/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance nonempty_positive_compacts [locally_compact_space α] [nonempty α] :
  nonempty (positive_compacts α) :=
begin
  inhabit α,
  rcases exists_compact_subset is_open_univ (mem_univ (default α)) with ⟨K, hK⟩,
  exact ⟨⟨K, hK.1, ⟨_, hK.2.1⟩⟩⟩
end

end positive_compacts

end topological_space
