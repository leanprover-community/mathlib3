/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import data.set_like.basic
import category_theory.category.basic
import category_theory.filtered
import topology.category.Top.limits

/-!
# Ends

This file contains a definition of the ends of a simple graph, as sections of the inverse system
assigning, to each finite set of vertices, the connected components of its complement.
-/

universes u
variables {V : Type u} (G : simple_graph V) (K L L' M : set V)

open classical

noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph

section out

/-- The graph induced by removing `K` -/
@[reducible] def out := G.induce $ Kᶜ

/-- Subsetship induces an obvious map on the induced graphs. -/
@[reducible] def out_hom {K L} (h : K ⊆ L) : G.out L →g G.out K :=
{ to_fun := λ ⟨v, hvK⟩, ⟨v, set.compl_subset_compl.mpr h hvK⟩,
  map_rel' := by { rintros ⟨_, _⟩ ⟨_, _⟩, exact id } }

lemma out_hom_refl (K) : G.out_hom (subset_refl K) = hom.id :=
by { ext ⟨_, _⟩, refl, }

lemma out_hom_trans {K L M} (h : K ⊆ L) (h' : L ⊆ M) :
  G.out_hom (h.trans h') = (G.out_hom h).comp (G.out_hom h') :=
by { ext ⟨_, _⟩, refl, }

lemma out_hom_injective {K} {L} (h : K ⊆ L) : function.injective (G.out_hom h) :=
by { rintros ⟨v, _⟩ ⟨w, _⟩ e,
    simpa only [out_hom, subtype.mk_eq_mk, rel_hom.coe_fn_mk] using e, }

end out

/-- The components outside a given set of vertices `K` -/
@[reducible] def comp_out := (G.out K).connected_component

variables {G} {K L M}

/-- The set of vertices of `G` making up the connected component `C` -/
@[reducible, simp] def comp_out.supp (C : G.comp_out K) : set V :=
{v : V | ∃ h : v ∈ Kᶜ, connected_component_mk (G.out K) ⟨v, h⟩ = C}

@[ext] lemma comp_out.eq_iff_supp_eq (C D : G.comp_out K) : C = D ↔ C.supp = D.supp :=
begin
  split,
  { rintro ⟨⟩, refl, },
  { refine connected_component.ind₂ _ C D,
    rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
    simp only [set.ext_iff, connected_component.eq, set.mem_compl_iff, set.mem_set_of_eq] at h ⊢,
    exact ((h v).mp ⟨hv, reachable.refl _⟩).some_spec, }
end

instance : set_like (G.comp_out K) V :=
{ coe := comp_out.supp,
  coe_injective' := λ C D, (comp_out.eq_iff_supp_eq _ _).mpr, }


@[simp] lemma comp_out.mem_supp_iff {v : V} {C : comp_out G K} :
  v ∈ C ↔ ∃ (vK : v ∈ Kᶜ), connected_component_mk (G.out K) ⟨v, vK⟩ = C := iff.rfl

/-- The connected component of `v`. -/
@[reducible] def comp_out_mk (G : simple_graph V) {v : V} (vK : v ∈ Kᶜ) : G.comp_out K :=
  connected_component_mk (G.out K) ⟨v, vK⟩

lemma comp_out_mk_mem (G : simple_graph V) {v : V} (vK : v ∈ Kᶜ) :
  v ∈ G.comp_out_mk vK := ⟨vK, rfl⟩

lemma comp_out_mk_eq_of_adj (G : simple_graph V) {v w : V} (vK : v ∈ Kᶜ) (wK : w ∈ Kᶜ) :
  G.adj v w → G.comp_out_mk vK = G.comp_out_mk wK :=
by { rw [connected_component.eq], rintro a, apply adj.reachable, exact a }

namespace comp_out

/-- The induced subgraph of `V` given by the vertices of `C`. -/
@[reducible, protected]
def subgraph (C : comp_out G K) : G.subgraph := (⊤ : G.subgraph).induce (C : set V)

lemma coe_inj {C D : G.comp_out K} : (C : set V) = (D : set V) ↔ C = D := set_like.coe_set_eq

@[simp] protected lemma nonempty (C : G.comp_out K) : (C : set V).nonempty :=
begin
  refine C.ind (λ v, _),
  use v,
  simp only [set.mem_compl_iff, set_like.mem_coe, mem_supp_iff, connected_component.eq,
             subtype.coe_eta, exists_prop],
  exact ⟨v.prop, reachable.refl _⟩,
end

protected lemma disjoint_right (C : G.comp_out K) : disjoint K C :=
begin
  rw set.disjoint_iff,
  rintro v ⟨vK, vC⟩,
  simp only [mem_supp_iff, set.mem_compl_iff, set_like.mem_coe] at vC,
  exact vC.some vK,
end

lemma not_mem_of_mem {C : G.comp_out K} {c : V} (cC : c ∈ C) : c ∉ K :=
λ cK, set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩

protected lemma pairwise_disjoint :
  pairwise $ λ  C D : G.comp_out K, disjoint (C : set V) (D : set V) :=
begin
  rintro C D ne,
  rw set.disjoint_iff,
  rintro u ⟨uC, uD⟩,
  simp only [set.mem_compl_iff, set_like.mem_coe, mem_supp_iff] at uC uD,
  exact ne (uC.some_spec.symm.trans uD.some_spec),
end

lemma eq_of_not_disjoint (C D : G.comp_out K) : ¬ disjoint (C : set V) (D : set V) → C = D :=
comp_out.pairwise_disjoint.eq

/--
Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
lemma mem_of_adj : ∀ {C : G.comp_out K} (c d : V), c ∈ C → d ∉ K → G.adj c d → d ∈ C :=
begin
  refine connected_component.ind _,
  rintros v c d cC dnK cd,
  have cd' : (G.out K).reachable (⟨c, not_mem_of_mem cC⟩) ⟨d, dnK⟩ := adj.reachable cd,
  simp only [mem_supp_iff, set.mem_compl_iff, connected_component.eq] at cC ⊢,
  exact ⟨dnK, cd'.symm.trans cC.some_spec⟩,
end

/--
Assuming `G` is preconnected and `K` not empty, given any connected component `C` outside of `K`,
there exists a vertex `k ∈ K` adjacent to a vertex `v ∈ C`.
-/
lemma exists_adj_boundary_pair [Gc : G.preconnected] (hK : K.nonempty) :
  ∀ (C : G.comp_out K), ∃ (ck : V × V), ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.adj ck.1 ck.2 :=
begin
  refine connected_component.ind (λ v, _),
  let C : G.comp_out K := G.comp_out_mk v.prop,
  let dis := set.disjoint_iff.mp C.disjoint_right,
  by_contra' h,
  suffices : set.univ = (C : set V),
  { exact dis ⟨hK.some_spec, this ▸ (set.mem_univ hK.some)⟩, },
  symmetry,
  rw set.eq_univ_iff_forall,
  rintro u,
  by_contradiction unC,
  obtain ⟨p⟩ := Gc v u,
  obtain ⟨⟨⟨x, y⟩, xy⟩, d, xC, ynC⟩ :=
    p.exists_boundary_dart (C : set V) (G.comp_out_mk_mem v.prop) unC,
  have : (G.out K).connected_component_mk v = G.comp_out_mk v.prop, by
    simp only [connected_component.eq, subtype.coe_eta],
  rw this at h,
  apply ynC,
  exact mem_of_adj x y xC (λ (yK : y ∈ K), h ⟨x, y⟩ xC yK xy) xy,
end

/--
If `K ⊆ L`, the components outside of `L` are all contained in a single component outside of `K`.
-/
@[reducible] def hom (h : K ⊆ L) (C : G.comp_out L) : G.comp_out K := C.map (G.out_hom h)

lemma subset_hom (C : G.comp_out L) (h : K ⊆ L) : (C : set V) ⊆ (C.hom h : set V) :=
begin
  rintro c cC,
  simp only [set.mem_compl_iff, set_like.mem_coe, mem_supp_iff] at cC ⊢,
  obtain ⟨cL, rfl⟩ := cC,
  exact ⟨λ h', cL (h h'), rfl⟩,
end

lemma hom_eq_iff_le (C : G.comp_out L) (h : K ⊆ L) (D : G.comp_out K) :
  C.hom h = D ↔ (C : set V) ⊆ (D : set V) :=
begin
  split,
  { rintro rfl, exact C.subset_hom h, },
  { revert C, refine connected_component.ind _,
    rintro ⟨v, vL⟩ vD,
    have h₁ : v ∈ ↑D, by
    { refine set.mem_of_mem_of_subset _ vD,
      simp only [set.mem_compl_iff, set_like.mem_coe, mem_supp_iff, connected_component.eq],
      refine ⟨vL, _⟩,
      refl, },
    simp only [set.mem_compl_iff, mem_supp_iff, set_like.mem_coe] at h₁,
    exact h₁.some_spec, },
end

lemma hom_refl (C : G.comp_out L) : C.hom (subset_refl L) = C :=
by { change C.map _ = C, rw [G.out_hom_refl L, C.map_id], }

lemma hom_trans (C : G.comp_out L) (h : K ⊆ L) (h' : M ⊆ K) :
  C.hom (h'.trans h) = (C.hom h).hom h' :=
by { change C.map _ = (C.map _).map _, rw [G.out_hom_trans, C.map_comp], }

lemma hom_inf (C : G.comp_out L) (h : K ⊆ L) (Cinf : (C : set V).infinite) :
  (C.hom h : set V).infinite := set.infinite.mono (C.subset_hom h) Cinf

end comp_out

section ends

variables (G)

open category_theory

/--
The functor assigning a finite set in `V` to the set of connected components in its complement.
-/
def comp_out_functor : (finset V)ᵒᵖ ⥤ Type u :=
{ obj := λ K, G.comp_out K.unop,
  map := λ _ _ f, comp_out.hom (le_of_op_hom f),
  map_id' := λ K, funext $ λ C, C.hom_refl,
  map_comp' := λ K L M h h', funext $ λ C, C.hom_trans (le_of_op_hom h) (le_of_op_hom h') }

/-- The end of a graph, defined as the sections of the functor `comp_out_functor` . -/
@[protected]
def «end» := (comp_out_functor G).sections

end ends

end simple_graph
