/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import topology.opens

/-!
# Compact sets

We define the subtype of compact sets in a topological space.

## Main Definitions

- `closeds α` is the type of closed subsets of a topological space `α`.
- `compacts α` is the type of compact subsets of a topological space `α`.
- `nonempty_compacts α` is the type of non-empty compact subsets.
- `positive_compacts α` is the type of compact subsets with non-empty interior.
- `open_compacts α`: The type of open compact sets of a topological space `α`.
-/

open set

variables (α : Type*) {β : Type*} [topological_space α] [topological_space β]

namespace topological_space

/-! ### Closed sets -/

/-- The type of closed subsets of a topological space. -/
def closeds : Type* := {s : set α // is_closed s}

/-- The type of closed subsets is inhabited, with default element the empty set. -/
instance : inhabited (closeds α) := ⟨⟨∅, is_closed_empty ⟩⟩

/-! ### Compact sets -/

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts : Type* := { s : set α // is_compact s }

namespace compacts
variables {α}

instance : semilattice_sup (compacts α) :=
subtype.semilattice_sup (λ K₁ K₂, is_compact.union)

instance : order_bot (compacts α) :=
subtype.order_bot is_compact_empty

instance [t2_space α] : semilattice_inf (compacts α) :=
subtype.semilattice_inf (λ K₁ K₂, is_compact.inter)

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

/-! ### Nonempty compact sets -/

/-- The type of non-empty compact subsets of a topological space. The
non-emptiness will be useful in metric spaces, as we will be able to put
a distance (and not merely an edistance) on this space. -/
def nonempty_compacts : Type* := {s : set α // s.nonempty ∧ is_compact s}

namespace nonempty_compacts
variables {α}

/-- Turns a nonempty compact set into the corresponding compact set. -/
def to_compacts : nonempty_compacts α → compacts α := inclusion $ λ s hs, hs.2

/-- Associate to a nonempty compact subset the corresponding closed subset -/
def to_closeds [t2_space α] : nonempty_compacts α → closeds α := inclusion $ λ s hs, hs.2.is_closed

@[ext] protected lemma ext {s t : nonempty_compacts α} (h : s.1 = t.1) : s = t := subtype.eq h

instance : semilattice_sup (nonempty_compacts α) :=
subtype.semilattice_sup $ λ s t hs ht, ⟨hs.1.mono $ subset_union_left _ _, hs.2.union ht.2⟩

instance [compact_space α] [nonempty α] : order_top (nonempty_compacts α) :=
subtype.order_top ⟨univ_nonempty, compact_univ⟩

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [inhabited α] : inhabited (nonempty_compacts α) :=
⟨⟨{default}, singleton_nonempty default, is_compact_singleton ⟩⟩

instance to_compact_space {p : nonempty_compacts α} : compact_space p.val :=
⟨is_compact_iff_is_compact_univ.1 p.property.2⟩

instance to_nonempty {p : nonempty_compacts α} : nonempty p.val := p.property.1.to_subtype

end nonempty_compacts

/-! ### Positive compact sets -/

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
`nonempty_compacts`. -/
def positive_compacts : Type* := {s : set α // is_compact s ∧ (interior s).nonempty}

namespace positive_compacts
variables {α}

/-- Turns an open compact set into the corresponding compact set. -/
def to_opens : positive_compacts α → compacts α := inclusion $ λ s hs, hs.1

@[ext] protected lemma ext {s t : positive_compacts α} (h : s.1 = t.1) : s = t := subtype.eq h

instance : semilattice_sup (positive_compacts α) :=
subtype.semilattice_sup $ λ s t hs ht,
  ⟨hs.1.union ht.1, hs.2.mono $ interior_mono $ subset_union_left _ _⟩

instance [compact_space α] [nonempty α] : order_top (positive_compacts α) :=
subtype.order_top ⟨compact_univ, by { convert univ_nonempty, exact interior_univ, apply_instance }⟩

instance [compact_space α] [nonempty α] : inhabited (positive_compacts α) := ⟨⊤⟩

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance [locally_compact_space α] [nonempty α] : nonempty (positive_compacts α) :=
let ⟨K, hK⟩ := exists_compact_subset is_open_univ $ mem_univ (classical.arbitrary α) in
  ⟨⟨K, hK.1, _, hK.2.1⟩⟩

@[simp] lemma val_sup (s t : positive_compacts α) : (s ⊔ t).1 = s.1 ∪ t.1 := rfl
@[simp] lemma val_top [compact_space α] [nonempty α] : (⊤ : positive_compacts α).1 = univ := rfl

end positive_compacts

/-! ### Open compact sets -/

/-- The open compact sets of a topological space. See also `compacts` and `opens`. -/
def open_compacts : Type* := {s : set α // is_open s ∧ is_compact s}

namespace open_compacts
variables {α}

/-- Turns an open compact set into the corresponding open set. -/
def to_opens : open_compacts α → opens α := inclusion $ λ s hs, hs.1

/-- Turns an open compact set into the corresponding compact set. -/
def to_compacts : open_compacts α → compacts α := inclusion $ λ s hs, hs.2

lemma «open» (s : open_compacts α) : is_open s.1 := s.2.1
lemma compact (s : open_compacts α) : is_compact s.1 := s.2.2

@[ext] protected lemma ext {s t : open_compacts α} (h : s.1 = t.1) : s = t := subtype.eq h

instance : semilattice_sup (open_compacts α) :=
subtype.semilattice_sup $ λ s t hs ht, ⟨hs.1.union ht.1, hs.2.union ht.2⟩

instance : order_bot (open_compacts α) := subtype.order_bot ⟨is_open_empty, is_compact_empty⟩
instance [compact_space α] : order_top (open_compacts α) :=
subtype.order_top ⟨is_open_univ, compact_univ⟩

instance : inhabited (open_compacts α) := ⟨⊥⟩

instance [t2_space α] : semilattice_inf (open_compacts α) :=
subtype.semilattice_inf $ λ s t hs ht, ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

instance [t2_space α] : lattice (open_compacts α) :=
{ ..open_compacts.semilattice_sup, ..open_compacts.semilattice_inf }

@[simp] lemma val_sup (s t : open_compacts α) : (s ⊔ t).1 = s.1 ∪ t.1 := rfl
@[simp] lemma val_inf [t2_space α] (s t : open_compacts α) : (s ⊓ t).1 = s.1 ∩ t.1 := rfl
@[simp] lemma val_bot : (⊥ : open_compacts α).1 = ∅ := rfl
@[simp] lemma val_top [compact_space α] : (⊤ : open_compacts α).1 = univ := rfl

/-- The image of an open compact under a continuous open map. -/
def map (f : α → β) (hf : continuous f) (hf' : is_open_map f) (s : open_compacts α) :
  open_compacts β :=
⟨f '' s.1, hf' _ s.open, s.compact.image hf⟩

@[simp] lemma val_map {f : α → β} (hf : continuous f) (hf' : is_open_map f) (s : open_compacts α) :
  (s.map f hf hf').1 = f '' s.1 := rfl

end open_compacts
end topological_space
