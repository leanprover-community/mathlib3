/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.clique
import combinatorics.additive.salem_spencer

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to a most one triangle.
The lower bound comes from turning the big Salem-Spencer set from Behrend's lower bound on Roth
numbers into a graph that has the property that every triangle gives a (possibly trivial)
arithmetic progression on the original set.

## Main declarations

* `simple_graph.edge_disjoint_triangles`: Predicate for a graph whose triangles are edge-disjoint.
* `ruzsa_szemeredi.add_graph`: The Ruzsa-Szemerédi graph associated to a set `s`.
* `add_salem_spencer.edge_disjoint_triangles`: If `s` is Salem-Spencer, then `add_graph s` has
  edge-disjoint triangles.

## TODO

Show the explicit bound.
-/

open simple_graph sum3
open_locale pointwise

variables {α : Type*}

namespace simple_graph
variables [decidable_eq α]

/-- A graph has edge-disjoint triangles if each edge belongs to at most one triangle. -/
def edge_disjoint_triangles (G : simple_graph α) : Prop :=
(G.clique_set 3).pairwise $ λ x y, (x ∩ y).card ≤ 1

/-- Whether a given finite graph has edge-disjoint triangles is decidable. -/
instance [fintype α] (G : simple_graph α) [decidable_rel G.adj] :
  decidable G.edge_disjoint_triangles :=
decidable_of_iff ((G.clique_finset 3 : set (finset α)).pairwise $ λ x y, (x ∩ y).card ≤ 1) $
  by { rw coe_clique_finset, refl }

end simple_graph

namespace ruzsa_szemeredi
section vertices
variables [has_mul α]

/-- The vertices of the Ruzsa-Szemerédi graph. -/
@[to_additive "The vertices of the Ruzsa-Szemerédi graph."]
abbreviation mul_vertices (s : set α) : Type* := s ⊕ ↥(s * s) ⊕ ↥(s * s * s)

instance (a : α) : inhabited (mul_vertices ({a} : set α)) := ⟨in₀ ⟨a, set.mem_singleton _⟩⟩

open finset fintype

@[to_additive] instance [decidable_eq α] (s : finset α) : fintype (mul_vertices (s : set α)) :=
of_equiv (s ⊕ ↥(s * s) ⊕ ↥(s * s * s)) $
  by refine (equiv.refl _).sum_congr (equiv.sum_congr _ _); { simp_rw ←coe_mul, refl }

@[simp, to_additive]
lemma card_mul_vertices [decidable_eq α] (s : finset α) :
  card (mul_vertices (s : set α)) = s.card + (s * s).card + (s * s * s).card :=
begin
  have e : mul_vertices (s : set α) ≃ (s ⊕ ↥(s * s) ⊕ ↥(s * s * s)),
  { refine (equiv.refl _).sum_congr (equiv.sum_congr _ _); { simp_rw ←coe_mul, refl } },
  simp_rw [fintype.card_congr e, card_sum, card_coe, add_assoc],
end

end vertices

section edges

/-- The edges of the Ruzsa-Szemerédi graph. -/
inductive add_edges [add_monoid α] (s : set α) : add_vertices s → add_vertices s → Prop
| in₀₁ {a : s}     {b} : ↑b ∈ (a : α) +ᵥ s               → add_edges (in₀ a) (in₁ b)
| in₁₀ {a : s}     {b} : ↑b ∈ (a : α) +ᵥ s               → add_edges (in₁ b) (in₀ a)
| in₁₂ {b : s + s} {c} : ↑c ∈ (b : α) +ᵥ s               → add_edges (in₁ b) (in₂ c)
| in₂₁ {b : s + s} {c} : ↑c ∈ (b : α) +ᵥ s               → add_edges (in₂ c) (in₁ b)
| in₂₀ {a : s}     {c} : ↑c ∈ (a : α) +ᵥ s.image ((•) 2) → add_edges (in₂ c) (in₀ a)
| in₀₂ {a : s}     {c} : ↑c ∈ (a : α) +ᵥ s.image ((•) 2) → add_edges (in₀ a) (in₂ c)

variables [monoid α] {s : set α} {a : s} {b : ↥(s * s)} {c : ↥(s * s * s)}

/-- The edges of the Ruzsa-Szemerédi graph. -/
@[to_additive] inductive mul_edges (s : set α) : mul_vertices s → mul_vertices s → Prop
| in₀₁ {a : s}     {b} : ↑b ∈ (a : α) • s            → mul_edges (in₀ a) (in₁ b)
| in₁₀ {a : s}     {b} : ↑b ∈ (a : α) • s            → mul_edges (in₁ b) (in₀ a)
| in₁₂ {b : s * s} {c} : ↑c ∈ (b : α) • s            → mul_edges (in₁ b) (in₂ c)
| in₂₁ {b : s * s} {c} : ↑c ∈ (b : α) • s            → mul_edges (in₂ c) (in₁ b)
| in₂₀ {a : s}     {c} : ↑c ∈ (a : α) • s.image (^2) → mul_edges (in₂ c) (in₀ a)
| in₀₂ {a : s}     {c} : ↑c ∈ (a : α) • s.image (^2) → mul_edges (in₀ a) (in₂ c)

open mul_edges

@[to_additive] lemma mul_edges_symm : symmetric (mul_edges s) :=
λ x y h, by cases h; constructor; assumption

@[to_additive] lemma mul_edges_irrefl : ∀ x, ¬ mul_edges s x x.

@[simp, to_additive] lemma mul_edges_inl_inm_iff : mul_edges s (in₀ a) (in₁ b) ↔ ↑b ∈ (a : α) • s :=
⟨by { rintro ⟨⟩, assumption }, in₀₁⟩

@[simp, to_additive] lemma mul_edges_inm_inr_iff : mul_edges s (in₁ b) (in₂ c) ↔ ↑c ∈ (b : α) • s :=
⟨by { rintro ⟨⟩, assumption }, in₁₂⟩

@[simp, to_additive] lemma mul_edges_inr_inl_iff :
  mul_edges s (in₂ c) (in₀ a) ↔ ↑c ∈ (a : α) • s.image (^2) :=
⟨by { rintro ⟨⟩, assumption }, in₂₀⟩

/-- The Ruzsa-Szemerédi graph associated to the set `s`. -/
@[to_additive "The Ruzsa-Szemerédi graph associated to the set `s`.", simps]
def mul_graph (s : set α) : simple_graph (mul_vertices s) :=
⟨mul_edges s, mul_edges_symm, mul_edges_irrefl⟩

/-- Throwaway tactic. -/
meta def sets_simp : tactic unit :=
`[ext] >> `[simp only [finset.mem_insert, finset.mem_singleton]] >> `[try {tauto}]

@[to_additive] lemma mul_graph_triple [decidable_eq α] :
  ∀ x y z, (mul_graph s).adj x y → (mul_graph s).adj y z → (mul_graph s).adj z x →
    ∃ a b c, ({in₀ a, in₁ b, in₂ c} : finset (mul_vertices s)) = {x, y, z} ∧
      (mul_graph s).adj (in₀ a) (in₁ b) ∧
      (mul_graph s).adj (in₁ b) (in₂ c) ∧
      (mul_graph s).adj (in₂ c) (in₀ a)
| _ _ _ (in₀₁ h₁) (in₁₂ h₂) (in₂₀ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₁, in₁₂ h₂, in₂₀ h₃⟩
| _ _ _ (in₁₀ h₁) (in₀₂ h₂) (in₂₁ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₁, in₁₂ h₃, in₂₀ h₂⟩
| _ _ _ (in₁₂ h₁) (in₂₀ h₂) (in₀₁ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₃, in₁₂ h₁, in₂₀ h₂⟩
| _ _ _ (in₂₁ h₁) (in₁₀ h₂) (in₀₂ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₂, in₁₂ h₁, in₂₀ h₃⟩
| _ _ _ (in₂₀ h₁) (in₀₁ h₂) (in₁₂ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₂, in₁₂ h₃, in₂₀ h₁⟩
| _ _ _ (in₀₂ h₁) (in₂₁ h₂) (in₁₀ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₃, in₁₂ h₂, in₂₀ h₁⟩

end edges

section cancel_monoid
open mul_edges
open_locale classical

@[to_additive] lemma mul_triangle_iff [cancel_monoid α] {s : set α} {a b c} :
  (mul_graph s).adj (in₀ a) (in₁ b) ∧ (mul_graph s).adj (in₁ b) (in₂ c) ∧
    (mul_graph s).adj (in₂ c) (in₀ a) ↔
      ∃ d e f ∈ s, (a : α) * d = b ∧ (a : α) * e ^ 2 = c ∧ (b : α) * f = c ∧ (d : α) * f = e * e :=
begin
  simp only [mul_graph_adj, mul_edges_inr_inl_iff, mul_edges_inm_inr_iff, mul_edges_inl_inm_iff],
  split,
  { rintro ⟨⟨d, hd, hab⟩, ⟨f, hf, hbc⟩, _, ⟨e, he, rfl⟩, hca⟩,
    refine ⟨_, hd, _, he, _, hf, hab, hca, hbc, _⟩,
    simp_rw [←hca, ←hab, smul_eq_mul, mul_assoc, pow_two] at hbc,
    exact mul_left_cancel hbc },
  { rintro ⟨d, hd, e, he, f, hf, hab, hca, hbc, -⟩,
    exact ⟨⟨d, hd, hab⟩, ⟨f, hf, hbc⟩, _, ⟨e, he, rfl⟩, hca⟩ }
end

end cancel_monoid

open add_edges set

variables {s : set ℕ}

lemma triangle_iff (h : add_salem_spencer s) {t : finset (add_vertices s)} :
  (add_graph s).is_n_clique 3 t ↔
    ∃ a d (hd : d ∈ s), t = {in₀ a, in₁ ⟨a + d, add_mem_add a.2 hd⟩, in₂ ⟨a + 2 * d,
      by { rw [two_mul, add_assoc], exact add_mem_add a.2 (add_mem_add hd hd) }⟩} :=
begin
  refine is_3_clique_iff.trans ⟨_, _⟩,
  { rintro ⟨a', b', c', hab, hac, hbc, rfl⟩,
    obtain ⟨a, b, c, habc, hab, hbc, hca⟩ := add_graph_triple _ _ _ hab hbc hac.symm,
    obtain ⟨d, hd, e, he, f, hf, hab, hca, hbc, hdef⟩ := add_triangle_iff.1 ⟨hab, hbc, hca⟩,
    rw ←h hd hf he hdef at hbc,
    rw [←add_salem_spencer_iff_eq_right.1 h hd hf he hdef, smul_eq_mul] at hca,
    exact ⟨a, d, hd, habc.symm.trans $ by simp_rw [hab, hca, subtype.coe_eta]⟩ },
  rintro ⟨a, d, hd, rfl⟩,
  exact ⟨in₀ a,
         in₁ ⟨a + d, add_mem_add a.2 hd⟩,
         in₂ ⟨a + 2 * d, by { rw [two_mul, add_assoc], exact add_mem_add a.2 (add_mem_add hd hd) }⟩,
    in₀₁ $ vadd_mem_vadd_set hd,
    in₀₂ $ vadd_mem_vadd_set $ mem_image_of_mem _ hd,
    in₁₂ $ by { simp_rw [two_mul, ←add_assoc], exact vadd_mem_vadd_set hd }, rfl⟩,
end

protected lemma _root_.add_salem_spencer.edge_disjoint_triangles (hs : add_salem_spencer s) :
  (add_graph s).edge_disjoint_triangles :=
begin
  refine λ t ht u hu htu, not_lt.1 (λ h, htu _),
  rw [mem_clique_set_iff, triangle_iff hs] at ht hu,
  obtain ⟨a, ha, b, hb, hab⟩ := finset.one_lt_card.1 h,
  obtain ⟨c, e, he, rfl⟩ := ht,
  obtain ⟨d, f, hf, rfl⟩ := hu,
  simp only [finset.mem_inter, finset.mem_insert, finset.mem_singleton, in₀, in₁, in₂] at ha hb,
  obtain a | a | a := a; obtain b | b | b := b; simp only [or_false, false_or] at ha hb;
    obtain ⟨⟨rfl, ha⟩, rfl, hb⟩ := ⟨ha, hb⟩,
  { cases hab rfl },
  { rw [subtype.mk_eq_mk, ha, add_right_inj] at hb,
    simp_rw [ha, hb] },
  { rw [subtype.mk_eq_mk, ha, add_right_inj, mul_right_inj' (@two_ne_zero ℕ _ _)] at hb,
    simp_rw [ha, hb] },
  { rw [subtype.mk_eq_mk, hb, add_right_inj] at ha,
    simp_rw [ha, hb] },
  { rw ha.trans hb.symm at hab,
    cases hab rfl },
  { simp only [subtype.mk_eq_mk, two_mul, ←add_assoc] at ha hb,
    rw [ha, add_right_inj] at hb,
    rw [hb, add_left_inj, subtype.coe_inj] at ha,
    simp_rw [ha, hb] },
  { rw [subtype.mk_eq_mk, hb, add_right_inj, mul_right_inj' (@two_ne_zero ℕ _ _)] at ha,
    simp_rw [ha, hb] },
  { simp only [subtype.mk_eq_mk, two_mul, ←add_assoc] at ha hb,
    rw [hb, add_right_inj] at ha,
    rw [ha, add_left_inj, subtype.coe_inj] at hb,
    simp_rw [ha, hb] },
  { rw ha.trans hb.symm at hab,
    cases hab rfl }
end

end ruzsa_szemeredi
