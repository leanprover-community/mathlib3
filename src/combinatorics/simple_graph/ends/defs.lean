/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import category_theory.cofiltered_system
import combinatorics.simple_graph.connectivity
import data.set_like.basic

/-!
# Ends

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a definition of the ends of a simple graph, as sections of the inverse system
assigning, to each finite set of vertices, the connected components of its complement.
-/

universes u
variables {V : Type u} (G : simple_graph V) (K L L' M : set V)

namespace simple_graph

/-- The components outside a given set of vertices `K` -/
@[reducible] def component_compl := (G.induce Kᶜ).connected_component

variables {G} {K L M}

/-- The connected component of `v` in `G.induce Kᶜ`. -/
@[reducible] def component_compl_mk (G : simple_graph V) {v : V} (vK : v ∉ K) :
  G.component_compl K :=
connected_component_mk (G.induce Kᶜ) ⟨v, vK⟩

/-- The set of vertices of `G` making up the connected component `C` -/
def component_compl.supp (C : G.component_compl K) : set V :=
{v : V | ∃ h : v ∉ K, G.component_compl_mk h = C}

@[ext] lemma component_compl.supp_injective :
  function.injective (component_compl.supp : G.component_compl K → set V) :=
begin
  refine connected_component.ind₂ _,
  rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
  simp only [set.ext_iff, connected_component.eq, set.mem_set_of_eq, component_compl.supp] at h ⊢,
  exact ((h v).mp ⟨hv, reachable.refl _⟩).some_spec,
end

lemma component_compl.supp_inj {C D : G.component_compl K} : C.supp = D.supp ↔ C = D :=
component_compl.supp_injective.eq_iff

instance component_compl.set_like : set_like (G.component_compl K) V :=
{ coe := component_compl.supp,
  coe_injective' := λ C D, (component_compl.supp_inj).mp, }

@[simp] lemma component_compl.mem_supp_iff {v : V} {C : component_compl G K} :
  v ∈ C ↔ ∃ (vK : v ∉ K), G.component_compl_mk vK = C := iff.rfl

lemma component_compl_mk_mem (G : simple_graph V) {v : V} (vK : v ∉ K) :
  v ∈ G.component_compl_mk vK := ⟨vK, rfl⟩

lemma component_compl_mk_eq_of_adj (G : simple_graph V) {v w : V} (vK : v ∉ K) (wK : w ∉ K)
  (a : G.adj v w) : G.component_compl_mk vK = G.component_compl_mk wK :=
by { rw [connected_component.eq], apply adj.reachable, exact a }

namespace component_compl

/--
A `component_compl` specialization of `quot.lift`, where soundness has to be proved only
for adjacent vertices.
-/
protected def lift {β : Sort*} (f : ∀ ⦃v⦄ (hv : v ∉ K), β)
  (h : ∀ ⦃v w⦄ (hv : v ∉ K) (hw : w ∉ K) (a : G.adj v w), f hv = f hw) : G.component_compl K → β :=
connected_component.lift (λ vv, f vv.prop) $ (λ v w p, by
  { induction p with _ u v w a q ih,
    { rintro _, refl, },
    { rintro h', exact (h u.prop v.prop a).trans (ih h'.of_cons), } })

protected lemma ind {β : G.component_compl K → Prop}
  (f : ∀ ⦃v⦄ (hv : v ∉ K), β (G.component_compl_mk hv)) : ∀ (C : G.component_compl K), β C := by
{ apply connected_component.ind, exact λ ⟨v, vnK⟩, f vnK, }

/-- The induced graph on the vertices `C`. -/
@[reducible]
protected def coe_graph (C : component_compl G K) : simple_graph C := G.induce (C : set V)

lemma coe_inj {C D : G.component_compl K} : (C : set V) = (D : set V) ↔ C = D := set_like.coe_set_eq

@[simp] protected lemma nonempty (C : G.component_compl K) : (C : set V).nonempty :=
C.ind (λ v vnK, ⟨v, vnK, rfl⟩)

protected lemma exists_eq_mk (C : G.component_compl K) :
  ∃ v (h : v ∉ K), G.component_compl_mk h = C :=
C.nonempty

protected lemma disjoint_right (C : G.component_compl K) : disjoint K C :=
begin
  rw set.disjoint_iff,
  exact λ v ⟨vK, vC⟩, vC.some vK,
end

lemma not_mem_of_mem {C : G.component_compl K} {c : V} (cC : c ∈ C) : c ∉ K :=
λ cK, set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩

protected lemma pairwise_disjoint :
  pairwise $ λ C D : G.component_compl K, disjoint (C : set V) (D : set V) :=
begin
  rintro C D ne,
  rw set.disjoint_iff,
  exact λ u ⟨uC, uD⟩, ne (uC.some_spec.symm.trans uD.some_spec),
end

/--
Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
lemma mem_of_adj : ∀ {C : G.component_compl K} (c d : V), c ∈ C → d ∉ K → G.adj c d → d ∈ C :=
λ C c d ⟨cnK, h⟩ dnK cd,
  ⟨ dnK, by { rw [←h, connected_component.eq], exact adj.reachable cd.symm, } ⟩

/--
Assuming `G` is preconnected and `K` not empty, given any connected component `C` outside of `K`,
there exists a vertex `k ∈ K` adjacent to a vertex `v ∈ C`.
-/
lemma exists_adj_boundary_pair (Gc : G.preconnected) (hK : K.nonempty) :
  ∀ (C : G.component_compl K), ∃ (ck : V × V), ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.adj ck.1 ck.2 :=
begin
  refine component_compl.ind (λ v vnK, _),
  let C : G.component_compl K := G.component_compl_mk vnK,
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
    p.exists_boundary_dart (C : set V) (G.component_compl_mk_mem vnK) unC,
  exact ynC (mem_of_adj x y xC (λ (yK : y ∈ K), h ⟨x, y⟩ xC yK xy) xy),
end

/--
If `K ⊆ L`, the components outside of `L` are all contained in a single component outside of `K`.
-/
@[reducible] def hom (h : K ⊆ L) (C : G.component_compl L) : G.component_compl K :=
C.map $ induce_hom hom.id $ set.compl_subset_compl.2 h

lemma subset_hom (C : G.component_compl L) (h : K ⊆ L) : (C : set V) ⊆ (C.hom h : set V) := by
{ rintro c ⟨cL, rfl⟩, exact ⟨λ h', cL (h h'), rfl⟩ }

lemma _root_.simple_graph.component_compl_mk_mem_hom (G : simple_graph V) {v : V} (vK : v ∉ K)
  (h : L ⊆ K) : v ∈ (G.component_compl_mk vK).hom h :=
subset_hom (G.component_compl_mk vK) h (G.component_compl_mk_mem vK)

lemma hom_eq_iff_le (C : G.component_compl L) (h : K ⊆ L) (D : G.component_compl K) :
  C.hom h = D ↔ (C : set V) ⊆ (D : set V) :=
⟨ λ h', h' ▸ (C.subset_hom h), C.ind (λ v vnL vD, (vD ⟨vnL, rfl⟩).some_spec) ⟩

lemma hom_eq_iff_not_disjoint (C : G.component_compl L) (h : K ⊆ L) (D : G.component_compl K) :
  C.hom h = D ↔ ¬ disjoint (C : set V) (D : set V) :=
begin
  rw set.not_disjoint_iff,
  split,
  { rintro rfl,
    apply C.ind (λ x xnL, _),
    exact ⟨x, ⟨xnL, rfl⟩, ⟨(λ xK, xnL (h xK)), rfl⟩⟩, },
  { apply C.ind (λ x xnL, _),
    rintro ⟨x, ⟨_, e₁⟩, _, rfl⟩,
    rw ←e₁, refl, },
end

lemma hom_refl (C : G.component_compl L) : C.hom (subset_refl L) = C :=
by { change C.map _ = C, erw [induce_hom_id G Lᶜ, connected_component.map_id], }

lemma hom_trans (C : G.component_compl L) (h : K ⊆ L) (h' : M ⊆ K) :
  C.hom (h'.trans h) = (C.hom h).hom h' :=
by { change C.map _ = (C.map _).map _, erw [connected_component.map_comp, induce_hom_comp], refl, }

lemma hom_mk {v : V} (vnL : v ∉ L) (h : K ⊆ L) :
  (G.component_compl_mk vnL).hom h = (G.component_compl_mk (set.not_mem_subset h vnL)) := rfl

lemma hom_infinite (C : G.component_compl L) (h : K ⊆ L) (Cinf : (C : set V).infinite) :
  (C.hom h : set V).infinite := set.infinite.mono (C.subset_hom h) Cinf

lemma infinite_iff_in_all_ranges {K : finset V} (C : G.component_compl K) :
  C.supp.infinite ↔ ∀ L (h : K ⊆ L), ∃ D : G.component_compl L, D.hom h = C :=
begin
  classical,
  split,
  { rintro Cinf L h,
    obtain ⟨v, ⟨vK, rfl⟩, vL⟩ := set.infinite.nonempty (set.infinite.diff Cinf L.finite_to_set),
    exact ⟨component_compl_mk _ vL, rfl⟩ },
  { rintro h Cfin,
    obtain ⟨D, e⟩ := h (K ∪ Cfin.to_finset) (finset.subset_union_left K Cfin.to_finset),
    obtain ⟨v, vD⟩ := D.nonempty,
    let Ddis := D.disjoint_right,
    simp_rw [finset.coe_union, set.finite.coe_to_finset, set.disjoint_union_left,
             set.disjoint_iff] at Ddis,
    exact Ddis.right ⟨(component_compl.hom_eq_iff_le _ _ _).mp e vD, vD⟩, },
end

end component_compl

section ends

variables (G)

open category_theory

/--
The functor assigning, to a finite set in `V`, the set of connected components in its complement.
-/
@[simps] def component_compl_functor : (finset V)ᵒᵖ ⥤ Type u :=
{ obj := λ K, G.component_compl K.unop,
  map := λ _ _ f, component_compl.hom (le_of_op_hom f),
  map_id' := λ K, funext $ λ C, C.hom_refl,
  map_comp' := λ K L M h h', funext $ λ C, C.hom_trans (le_of_op_hom h) (le_of_op_hom h') }

/-- The end of a graph, defined as the sections of the functor `component_compl_functor` . -/
@[protected]
def «end» := (component_compl_functor G).sections

lemma end_hom_mk_of_mk {s} (sec : s ∈ G.end) {K L : (finset V)ᵒᵖ} (h : L ⟶ K)
  {v : V} (vnL : v ∉ L.unop) (hs : s L = G.component_compl_mk vnL) :
  s K = G.component_compl_mk (set.not_mem_subset (le_of_op_hom h) vnL) :=
begin
  rw [←(sec h), hs],
  apply component_compl.hom_mk,
end

lemma infinite_iff_in_eventual_range {K : (finset V)ᵒᵖ} (C : G.component_compl_functor.obj K) :
  C.supp.infinite ↔ C ∈ G.component_compl_functor.eventual_range K :=
begin
  simp only [C.infinite_iff_in_all_ranges, category_theory.functor.eventual_range,
             set.mem_Inter, set.mem_range, component_compl_functor_map],
  exact ⟨λ h Lop KL, h Lop.unop (le_of_op_hom KL), λ h L KL, h (opposite.op L) (op_hom_of_le KL)⟩,
end

end ends

end simple_graph
