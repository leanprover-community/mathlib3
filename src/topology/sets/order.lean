/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.upper_lower
import topology.sets.closeds

/-!
# Clopen upper sets

In this file we define the type of clopen upper sets.
-/

open set

variables {α β : Type*} [topological_space α] [has_le α] [topological_space β] [has_le β]

namespace topological_space

/-! ### Compact open sets -/

/-- The type of clopen upper sets of a topological space. -/
structure clopen_upset (α : Type*) [topological_space α] [has_le α] extends clopens α :=
(upper' : is_upper_set carrier)

namespace clopen_upset

instance : set_like (clopen_upset α) α :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t h, by { obtain ⟨⟨_, _⟩, _⟩ := s, obtain ⟨⟨_, _⟩, _⟩ := t, congr' } }

lemma upper (s : clopen_upset α) : is_upper_set (s : set α) := s.upper'
lemma clopen (s : clopen_upset α) : is_clopen (s : set α) := s.clopen'

/-- Reinterpret a upper clopen as an upper set. -/
@[simps] def to_upper_set (s : clopen_upset α) : upper_set α := ⟨s, s.upper⟩

@[ext] protected lemma ext {s t : clopen_upset α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : clopens α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (clopen_upset α) :=
⟨λ s t, ⟨s.to_clopens ⊔ t.to_clopens, s.upper.union t.upper⟩⟩
instance : has_inf (clopen_upset α) :=
⟨λ s t, ⟨s.to_clopens ⊓ t.to_clopens, s.upper.inter t.upper⟩⟩
instance : has_top (clopen_upset α) := ⟨⟨⊤, is_upper_set_univ⟩⟩
instance : has_bot (clopen_upset α) := ⟨⟨⊥, is_upper_set_empty⟩⟩

instance : lattice (clopen_upset α) :=
set_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance : bounded_order (clopen_upset α) :=
bounded_order.lift (coe : _ → set α) (λ _ _, id) rfl rfl

@[simp] lemma coe_sup (s t : clopen_upset α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : clopen_upset α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top : (↑(⊤ : clopen_upset α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : clopen_upset α) : set α) = ∅ := rfl

instance : inhabited (clopen_upset α) := ⟨⊥⟩

end clopen_upset
end topological_space
