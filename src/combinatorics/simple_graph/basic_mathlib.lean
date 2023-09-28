/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import combinatorics.simple_graph.basic
import data.sym.card

/-!
# Stuff for combinatorics.simple_graph.basic
-/

namespace simple_graph
variables {V V' : Type*} {G : simple_graph V} {K K' : Type*}

open fintype (card)
open finset

instance [subsingleton V] : is_empty (edge_set G) :=
begin
  split,
  rintro ⟨i, hi⟩,
  induction i using sym2.induction_on with i j,
  simp only [mem_edge_set] at hi,
  cases hi.ne (subsingleton.elim _ _)
end

def top_edge_set_equiv : (⊤ : simple_graph V).edge_set ≃ {a : sym2 V // ¬a.is_diag} :=
equiv.subtype_equiv_right $ λ i, sym2.induction_on i $ λ x y, iff.rfl

lemma card_top_edge_set [decidable_eq V] [fintype V] :
  card (⊤ : simple_graph V).edge_set = (card V).choose 2 :=
by rw [fintype.card_congr top_edge_set_equiv, sym2.card_subtype_not_diag]

lemma edge_set_eq_empty_iff {G : simple_graph V} : G.edge_set = ∅ ↔ G = ⊥ :=
by rw [←edge_set_bot, edge_set_inj]

lemma disjoint_edge_set {G H : simple_graph V} : disjoint G.edge_set H.edge_set ↔ disjoint G H :=
by rw [set.disjoint_iff_inter_eq_empty, disjoint_iff, ←edge_set_inf, edge_set_eq_empty_iff]

lemma disjoint_left {G H : simple_graph V} : disjoint G H ↔ (∀ x y, G.adj x y → ¬ H.adj x y) :=
by simp only [←disjoint_edge_set, set.disjoint_left, sym2.forall, mem_edge_set]

@[simp] lemma adj_sup_iff {ι V : Type*} {s : finset ι} {f : ι → simple_graph V} {x y : V} :
  (s.sup f).adj x y ↔ ∃ i ∈ s, (f i).adj x y :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { simp },
  { simp [or_and_distrib_right, exists_or_distrib, ih] },
end

lemma top_hom_injective (f : (⊤ : simple_graph V') →g G) :
  function.injective f :=
λ x y h, by_contra (λ z, (f.map_rel z).ne h)

def top_hom_graph_equiv :
  ((⊤ : simple_graph V') ↪g G) ≃ ((⊤ : simple_graph V') →g G) :=
{ to_fun := λ f, f,
  inv_fun := λ f, ⟨⟨f, top_hom_injective _⟩, λ x y, ⟨λ h, ne_of_apply_ne _ h.ne, f.map_rel⟩⟩,
  left_inv := λ f, rel_embedding.ext (λ _, rfl),
  right_inv := λ f, rel_hom.ext (λ _, rfl) }

lemma neighbor_set_bot {x : V} : (⊥ : simple_graph V).neighbor_set x = ∅ :=
by { ext y, simp }

lemma neighbor_set_top {x : V} : (⊤ : simple_graph V).neighbor_set x = {x}ᶜ :=
by { ext y, rw [mem_neighbor_set, top_adj, set.mem_compl_singleton_iff, ne_comm] }

lemma neighbor_set_sup {G H : simple_graph V} {x : V} :
  (G ⊔ H).neighbor_set x = G.neighbor_set x ∪ H.neighbor_set x :=
by { ext y, simp }

lemma neighbor_set_inf {G H : simple_graph V} {x : V} :
  (G ⊓ H).neighbor_set x = G.neighbor_set x ∩ H.neighbor_set x :=
by { ext y, simp only [mem_neighbor_set, inf_adj, set.mem_inter_iff] }

lemma neighbor_set_supr {ι : Type*} {s : ι → simple_graph V} {x : V} :
  (⨆ i, s i).neighbor_set x = ⋃ i, (s i).neighbor_set x :=
by { ext y, simp }

lemma neighbor_set_infi {ι : Type*} [nonempty ι] {s : ι → simple_graph V} {x : V} :
  (⨅ i, s i).neighbor_set x = ⋂ i, (s i).neighbor_set x :=
begin
  ext y,
  simp only [mem_neighbor_set, infi_adj, ne.def, set.infi_eq_Inter, set.mem_Inter,
    and_iff_left_iff_imp],
  intro h,
  inhabit ι,
  exact (h default).ne,
end

lemma neighbor_set_disjoint {G H : simple_graph V} {x : V} (h : disjoint G H) :
  disjoint (G.neighbor_set x) (H.neighbor_set x) :=
by rw [set.disjoint_iff_inter_eq_empty, ←neighbor_set_inf, h.eq_bot, neighbor_set_bot]

section

instance {V : Type*} {x : V} : is_empty ((⊥ : simple_graph V).neighbor_set x) :=
  subtype.is_empty_false

lemma neighbor_finset_bot {x : V} : (⊥ : simple_graph V).neighbor_finset x = ∅ :=
by { ext y, simp }

lemma neighbor_finset_top [fintype V] [decidable_eq V] {x : V} :
  (⊤ : simple_graph V).neighbor_finset x = {x}ᶜ :=
by { ext y, rw [mem_neighbor_finset, top_adj, finset.mem_compl, mem_singleton, ne_comm] }

lemma neighbor_finset_sup [decidable_eq V] {G H : simple_graph V} {x : V}
  [fintype ((G ⊔ H).neighbor_set x)] [fintype (G.neighbor_set x)] [fintype (H.neighbor_set x)] :
  (G ⊔ H).neighbor_finset x = G.neighbor_finset x ∪ H.neighbor_finset x :=
by { ext y, simp }

lemma neighbor_finset_inf [decidable_eq V] {G H : simple_graph V} {x : V}
  [fintype ((G ⊓ H).neighbor_set x)] [fintype (G.neighbor_set x)] [fintype (H.neighbor_set x)] :
  (G ⊓ H).neighbor_finset x = G.neighbor_finset x ∩ H.neighbor_finset x :=
by { ext y, simp }

instance _root_.finset.decidable_rel_sup
  {ι V : Type*} {s : finset ι} {f : ι → simple_graph V} [Π i, decidable_rel (f i).adj] :
  decidable_rel (s.sup f).adj :=
λ x y, decidable_of_iff' _ adj_sup_iff

lemma neighbor_finset_supr [decidable_eq V] {ι : Type*} {s : finset ι} {f : ι → simple_graph V}
  {x : V} [Π i, fintype ((f i).neighbor_set x)] [fintype ((s.sup f).neighbor_set x)] :
  (s.sup f).neighbor_finset x = s.bUnion (λ i, (f i).neighbor_finset x) :=
by { ext y, simp }

@[simp] lemma coe_neighbor_finset {G : simple_graph V} {x : V} [fintype (G.neighbor_set x)] :
  (G.neighbor_finset x : set V) = G.neighbor_set x :=
by rw [neighbor_finset_def, set.coe_to_finset]

lemma neighbor_finset_disjoint {G H : simple_graph V} {x : V}
  [fintype (G.neighbor_set x)] [fintype (H.neighbor_set x)] (h : disjoint G H) :
  disjoint (G.neighbor_finset x) (H.neighbor_finset x) :=
by { rw [←disjoint_coe, coe_neighbor_finset, coe_neighbor_finset], exact neighbor_set_disjoint h }

end

end simple_graph
