/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import .behrend
import .mathlib
import .triangle

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to a most one triangle.
The lower bound comes from turning the big Salem-Spencer set from Behrend's lower bound on Roth
numbers into a graph which has the property that every triangle gives a (possibly trivial)
arithmetic progression on the original set.
-/

open finset sum₃
open_locale pointwise

variables {α : Type*} [fintype α] [decidable_eq α]

/-- A Ruzsa-Szemerédi graph is a graph such that each edge belongs to at most one triangle. -/
def ruzsa_szemeredi (G : simple_graph α) [G.decidable] : Prop :=
(G.clique_finset 3 : set (finset α)).pairwise $ λ x y, (x ∩ y).card ≤ 1

/-- Whether a given graph is Ruzsa-Szemerédi is decidable. -/
instance (G : simple_graph α) [G.decidable] : decidable (ruzsa_szemeredi G) :=
sorry

namespace ruzsa_szemeredi

/-- The vertices of the Ruzsa-Szemerédi graph. -/
@[nolint inhabited_instance] abbreviation vertices {α : Type*} (s : set α) := sum₃ s s s

section monoid
variables [monoid α]

section edges
variables {s : set α} {a b c : s}

/-- The edges of the Ruzsa-Szemerédi graph. -/
inductive edges (s : set α) : vertices s → vertices s → Prop
| lm {a b : s} : ↑b ∈ (a : α) • s            → edges (in₀ a) (in₁ b)
| ml {a b : s} : ↑b ∈ (a : α) • s            → edges (in₁ b) (in₀ a)
| mr {b c : s} : ↑c ∈ (b : α) • s            → edges (in₁ b) (in₂ c)
| rm {b c : s} : ↑c ∈ (b : α) • s            → edges (in₂ c) (in₁ b)
| rl {c a : s} : ↑c ∈ (a : α) • s.image (^2) → edges (in₂ c) (in₀ a)
| lr {c a : s} : ↑c ∈ (a : α) • s.image (^2) → edges (in₀ a) (in₂ c)

open edges

lemma edges_symm : symmetric (edges s)
| _ _ (lm h) := ml h
| _ _ (ml h) := lm h
| _ _ (mr h) := rm h
| _ _ (rm h) := mr h
| _ _ (rl h) := lr h
| _ _ (lr h) := rl h

lemma edges_irrefl : ∀ x : vertices s, ¬ edges s x x.

@[simp] lemma edges_inl_inm_iff : edges s (in₀ a) (in₁ b) ↔ ↑b ∈ (a : α) • s :=
⟨by { rintro ⟨⟩, assumption }, lm⟩

@[simp] lemma edges_inm_inr_iff : edges s (in₁ b) (in₂ c) ↔ ↑c ∈ (b : α) • s :=
⟨by { rintro ⟨⟩, assumption }, mr⟩

@[simp] lemma edges_inr_inl_iff : edges s (in₂ c) (in₀ a) ↔ ↑c ∈ (a : α) • s.image (^2) :=
⟨by { rintro ⟨⟩, assumption }, rl⟩

/-- The Ruzsa-Szemerédi graph. -/
@[simps] def graph (s : set α) : simple_graph (vertices s) :=
{ adj := edges s,
  symm := edges_symm,
  loopless := edges_irrefl }

open_locale classical

/-- Throwaway tactic. -/
meta def sets_simp : tactic unit :=
`[ext] >> `[simp only [finset.mem_insert, finset.mem_singleton]] >> `[try {tauto}]

lemma graph_triple :
  ∀ x y z, (graph s).adj x y → (graph s).adj y z → (graph s).adj z x →
    ∃ a b c, ({in₀ a, in₁ b, in₂ c} : finset (vertices s)) = {x, y, z} ∧
      (graph s).adj (in₀ a) (in₁ b) ∧
      (graph s).adj (in₁ b) (in₂ c) ∧
      (graph s).adj (in₂ c) (in₀ a)
| _ _ _ (lm h₁) (mr h₂) (rl h₃) := ⟨_, _, _, by sets_simp, lm h₁, mr h₂, rl h₃⟩
| _ _ _ (ml h₁) (lr h₂) (rm h₃) := ⟨_, _, _, by sets_simp, lm h₁, mr h₃, rl h₂⟩
| _ _ _ (mr h₁) (rl h₂) (lm h₃) := ⟨_, _, _, by sets_simp, lm h₃, mr h₁, rl h₂⟩
| _ _ _ (rm h₁) (ml h₂) (lr h₃) := ⟨_, _, _, by sets_simp, lm h₂, mr h₁, rl h₃⟩
| _ _ _ (rl h₁) (lm h₂) (mr h₃) := ⟨_, _, _, by sets_simp, lm h₂, mr h₃, rl h₁⟩
| _ _ _ (lr h₁) (rm h₂) (ml h₃) := ⟨_, _, _, by sets_simp, lm h₃, mr h₂, rl h₁⟩

lemma triangle_iff {a b c : s} :
  (graph s).adj (in₀ a) (in₁ b) ∧ (graph s).adj (in₁ b) (in₂ c) ∧ (graph s).adj (in₂ c) (in₀ a) ↔
    (a : α) * c = b * b  :=
begin
  split,
  {
    rintro ⟨hab, hbc, hca⟩,
    simp at hab hbc hca,
    change _ ∈ _ at hab,
    sorry
  },
  sorry
end

protected lemma _root_.mul_salem_spencer.ruzsa_szemeredi {s : finset α}
  (h : mul_salem_spencer (s : set α)) :
  ruzsa_szemeredi (graph (s : set α)) :=
begin
  rintro t ht u hu htu,
  rw [←nat.lt_succ_iff, lt_iff_not_le],
  rintro h,
  obtain ⟨v, hvtu, hv⟩ := exists_smaller_set _ _ h,
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hv,
  simp only [insert_subset, mem_inter, singleton_subset_iff] at hvtu,
  sorry
end

end edges
end monoid
end ruzsa_szemeredi
