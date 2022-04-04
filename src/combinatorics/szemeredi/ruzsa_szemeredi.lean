/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.szemeredi.behrend

/-!
# The Ruzsa-Szemerédi problem

This file

-/

open_locale pointwise

variables {α : Type*}

/-- A multiplicative Ruzsa-Szemerédi set in a graph is a set such that each edge belongs to at most
one triangle in it. -/
def mul_ruzsa_szemeredi (G : simple_graph α) (s : set α) : Prop := sorry

/-- Whether a given finset is Ruzsa-Szemerédi is decidable. -/
instance (G : simple_graph α) (s : finset α) : decidable (mul_ruzsa_szemeredi G (s : set α)) :=
sorry

/-- The multiplicative Ruzsa-Szemerédi number of a finset is the cardinality of its biggest
multiplicative Ruzsa-Szemerédi subset. -/
def mul_ruzsa_szemeredi_number (G : simple_graph α) (s : finset α) : ℕ :=
s.card.find_greatest $ λ m, ∃ t ⊆ s, t.card = m ∧ mul_ruzsa_szemeredi G (t : set α)

namespace ruzsa_szemeredi
variables [decidable_eq α]

/-- The vertices of the Ruzsa-Szemerédi graph. -/
@[derive inhabited] inductive vertices (α : Type*)
| inl : α → vertices
| inm : α → vertices
| inr : α → vertices

-- inductive ruzsa_szemeredi_vertices (n : ℕ)
-- | inl : fin n → ruzsa_szemeredi_vertices
-- | inm : fin (2 * n) → ruzsa_szemeredi_vertices
-- | inr : fin (3 * n) → ruzsa_szemeredi_vertices

open vertices

/-- The set of vertices of the Ruzsa-Szemerédi graph corresponding to a set in the original monoid.
-/
inductive vertex_set (s : set α) : set (vertices α)
| inl {a : α} : a ∈ s → vertex_set (inl a)
| inm {b : α} : b ∈ s → vertex_set (inm b)
| inr {c : α} : c ∈ s → vertex_set (inr c)

section monoid
variables [monoid α]

section edges
variables {s : set α} {a b c : α}

/-- The edges of the Ruzsa-Szemerédi graph. -/
inductive edges (s : set α) : vertices α → vertices α → Prop
| lm {a b : α} : b ∈ a • s            → edges (inl a) (inm b)
| ml {a b : α} : b ∈ a • s            → edges (inm b) (inl a)
| mr {b c : α} : c ∈ b • s            → edges (inm b) (inr c)
| rm {b c : α} : c ∈ b • s            → edges (inr c) (inm b)
| rl {c a : α} : a ∈ c • s.image (^2) → edges (inr c) (inl a)
| lr {c a : α} : a ∈ c • s.image (^2) → edges (inl a) (inr c)

open edges

lemma edges_symm : symmetric (edges s)
| _ _ (lm h) := ml h
| _ _ (ml h) := lm h
| _ _ (mr h) := rm h
| _ _ (rm h) := mr h
| _ _ (rl h) := lr h
| _ _ (lr h) := rl h

lemma edges_irrefl : ∀ x : vertices α, ¬ edges s x x.

@[simp] lemma edges_inl_inm_iff : edges s (inl a) (inm b) ↔ b ∈ a • s :=
⟨by { rintro ⟨⟩, assumption }, lm⟩

@[simp] lemma edges_inm_inr_iff : edges s (inm b) (inr c) ↔ c ∈ b • s :=
⟨by { rintro ⟨⟩, assumption }, mr⟩

@[simp] lemma edges_inr_inl_iff : edges s (inr c) (inl a) ↔ a ∈ c • s.image (^2) :=
⟨by { rintro ⟨⟩, assumption }, rl⟩

/-- The Ruzsa-Szemerédi graph. -/
def graph (s : set α) : simple_graph (vertices α) :=
{ adj := edges s,
  symm := edges_symm,
  loopless := edges_irrefl }

protected lemma mul_salem_spencer.mul_ruzsa_szemeredi (h : mul_salem_spencer s) :
  mul_ruzsa_szemeredi (graph s) (vertex_set s) :=
begin
  sorry
end

end edges
end monoid
end ruzsa_szemeredi
