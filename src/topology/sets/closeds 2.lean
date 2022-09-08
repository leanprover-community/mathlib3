/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import topology.sets.opens

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `closeds α`: The type of closed sets.
* `clopens α`: The type of clopen sets.
-/

open set

variables {α β : Type*} [topological_space α] [topological_space β]

namespace topological_space

/-! ### Closed sets -/

/-- The type of closed subsets of a topological space. -/
structure closeds (α : Type*) [topological_space α] :=
(carrier : set α)
(closed' : is_closed carrier)

namespace closeds
variables {α}

instance : set_like (closeds α) α :=
{ coe := closeds.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

lemma closed (s : closeds α) : is_closed (s : set α) := s.closed'

@[ext] protected lemma ext {s t : closeds α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (closeds α) := ⟨λ s t, ⟨s ∪ t, s.closed.union t.closed⟩⟩
instance : has_inf (closeds α) := ⟨λ s t, ⟨s ∩ t, s.closed.inter t.closed⟩⟩
instance : has_top (closeds α) := ⟨⟨univ, is_closed_univ⟩⟩
instance : has_bot (closeds α) := ⟨⟨∅, is_closed_empty⟩⟩

instance : distrib_lattice (closeds α) :=
set_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)
instance : bounded_order (closeds α) := bounded_order.lift (coe : _ → set α) (λ _ _, id) rfl rfl

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : inhabited (closeds α) := ⟨⊥⟩

@[simp] lemma coe_sup (s t : closeds α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : closeds α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top : (↑(⊤ : closeds α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : closeds α) : set α) = ∅ := rfl

end closeds

/-! ### Clopen sets -/

/-- The type of clopen sets of a topological space. -/
structure clopens (α : Type*) [topological_space α] :=
(carrier : set α)
(clopen' : is_clopen carrier)

namespace clopens

instance : set_like (clopens α) α :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

lemma clopen (s : clopens α) : is_clopen (s : set α) := s.clopen'

/-- Reinterpret a compact open as an open. -/
@[simps] def to_opens (s : clopens α) : opens α := ⟨s, s.clopen.is_open⟩

@[ext] protected lemma ext {s t : clopens α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (clopens α) := ⟨λ s t, ⟨s ∪ t, s.clopen.union t.clopen⟩⟩
instance : has_inf (clopens α) := ⟨λ s t, ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩
instance : has_top (clopens α) := ⟨⟨⊤, is_clopen_univ⟩⟩
instance : has_bot (clopens α) := ⟨⟨⊥, is_clopen_empty⟩⟩
instance : has_sdiff (clopens α) := ⟨λ s t, ⟨s \ t, s.clopen.diff t.clopen⟩⟩
instance : has_compl (clopens α) := ⟨λ s, ⟨sᶜ, s.clopen.compl⟩⟩

instance : boolean_algebra (clopens α) :=
set_like.coe_injective.boolean_algebra _ (λ _ _, rfl) (λ _ _, rfl) rfl rfl (λ _, rfl) (λ _ _, rfl)

@[simp] lemma coe_sup (s t : clopens α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : clopens α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top : (↑(⊤ : clopens α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : clopens α) : set α) = ∅ := rfl
@[simp] lemma coe_sdiff (s t : clopens α) : (↑(s \ t) : set α) = s \ t := rfl
@[simp] lemma coe_compl (s : clopens α) : (↑sᶜ : set α) = sᶜ := rfl

instance : inhabited (clopens α) := ⟨⊥⟩

end clopens
end topological_space
