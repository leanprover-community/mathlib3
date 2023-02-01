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

namespace simple_graph

/-- The components outside a given set of vertices `K` -/
@[reducible] def comp_out := (G.induce Kᶜ).connected_component

variables {G} {K L M}

/-- The connected component of `v`. -/
@[reducible] def comp_out_mk (G : simple_graph V) {v : V} (vK : v ∈ Kᶜ) : G.comp_out K :=
connected_component_mk (G.induce Kᶜ) ⟨v, vK⟩

/-- The set of vertices of `G` making up the connected component `C` -/
@[reducible] def comp_out.supp (C : G.comp_out K) : set V :=
{v : V | ∃ h : v ∈ Kᶜ, G.comp_out_mk h = C}

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
  v ∈ C ↔ ∃ (vK : v ∈ Kᶜ), G.comp_out_mk vK = C := iff.rfl

lemma comp_out_mk_mem (G : simple_graph V) {v : V} (vK : v ∈ Kᶜ) :
  v ∈ G.comp_out_mk vK := ⟨vK, rfl⟩

lemma comp_out_mk_eq_of_adj (G : simple_graph V) {v w : V} (vK : v ∈ Kᶜ) (wK : w ∈ Kᶜ)
  (a : G.adj v w) : G.comp_out_mk vK = G.comp_out_mk wK :=
by { rw [connected_component.eq], apply adj.reachable, exact a }

namespace comp_out

/--
A `comp_out` specialization of `quot.lift`, where soundness has to be proved only for adjacent
vertices.
-/
def lift {β : Sort*} (f : ∀ ⦃v⦄ (hv : v ∈ Kᶜ), β)
  (h : ∀ ⦃v w⦄ (hv : v ∈ Kᶜ) (hw : w ∈ Kᶜ) (a : G.adj v w), f hv = f hw) : G.comp_out K → β :=
connected_component.lift (λ vv, f vv.prop) $ (λ v w p, by
  { induction p with _ u v w a q ih,
    { rintro _, refl, },
    { rintro h', exact (h u.prop v.prop a).trans (ih h'.of_cons), } })

lemma ind {β : G.comp_out K → Prop} (f : ∀ ⦃v⦄ (hv : v ∈ Kᶜ), β (G.comp_out_mk hv)) :
  ∀ (C : G.comp_out K), β C := by
{ apply connected_component.ind, exact λ ⟨v, vnK⟩, f vnK, }

/-- The induced graph on the vertices `C`. -/
@[reducible, protected]
def coe_graph (C : comp_out G K) : simple_graph C.supp := G.induce (C : set V)

lemma coe_inj {C D : G.comp_out K} : (C : set V) = (D : set V) ↔ C = D := set_like.coe_set_eq

@[simp] protected lemma nonempty (C : G.comp_out K) : (C : set V).nonempty :=
C.ind (λ v vnK, ⟨v, vnK, rfl⟩)

protected lemma exists_eq_mk (C : G.comp_out K) : ∃ (v) (h : v ∈ Kᶜ), G.comp_out_mk h = C :=
C.nonempty


protected lemma disjoint_right (C : G.comp_out K) : disjoint K C :=
begin
  rw set.disjoint_iff,
  exact λ v ⟨vK, vC⟩, vC.some vK,
end

lemma not_mem_of_mem {C : G.comp_out K} {c : V} (cC : c ∈ C) : c ∉ K :=
λ cK, set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩

protected lemma pairwise_disjoint :
  pairwise $ λ  C D : G.comp_out K, disjoint (C : set V) (D : set V) :=
begin
  rintro C D ne,
  rw set.disjoint_iff,
  exact λ u ⟨uC, uD⟩, ne (uC.some_spec.symm.trans uD.some_spec),
end

lemma eq_of_not_disjoint (C D : G.comp_out K) : ¬ disjoint (C : set V) (D : set V) → C = D :=
comp_out.pairwise_disjoint.eq

/--
Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
lemma mem_of_adj : ∀ {C : G.comp_out K} (c d : V), c ∈ C → d ∉ K → G.adj c d → d ∈ C :=
λ C c d ⟨cnK,h⟩ dnK cd,
  ⟨ dnK, by { rw [←h, connected_component.eq], exact adj.reachable cd.symm, } ⟩

/--
Assuming `G` is preconnected and `K` not empty, given any connected component `C` outside of `K`,
there exists a vertex `k ∈ K` adjacent to a vertex `v ∈ C`.
-/
lemma exists_adj_boundary_pair (Gc : G.preconnected) (hK : K.nonempty) :
  ∀ (C : G.comp_out K), ∃ (ck : V × V), ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.adj ck.1 ck.2 :=
begin
  refine comp_out.ind (λ v vnK, _),
  let C : G.comp_out K := G.comp_out_mk vnK,
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
    p.exists_boundary_dart (C : set V) (G.comp_out_mk_mem vnK) unC,
  exact ynC (mem_of_adj x y xC (λ (yK : y ∈ K), h ⟨x, y⟩ xC yK xy) xy),
end

/--
If `K ⊆ L`, the components outside of `L` are all contained in a single component outside of `K`.
-/
@[reducible] def hom (h : K ⊆ L) (C : G.comp_out L) : G.comp_out K :=
C.map (induce_hom G G hom.id (λ x, set.not_mem_subset h))

lemma subset_hom (C : G.comp_out L) (h : K ⊆ L) : (C : set V) ⊆ (C.hom h : set V) := by
{ rintro c ⟨cL,rfl⟩, exact ⟨λ h', cL (h h'), rfl⟩ }

lemma _root_.simple_graph.comp_out_mk_mem_hom (G : simple_graph V) {v : V} (vK : v ∈ Kᶜ)
  (h : L ⊆ K) : v ∈ (G.comp_out_mk vK).hom h :=
subset_hom (G.comp_out_mk vK) h (G.comp_out_mk_mem vK)

lemma hom_eq_iff_le (C : G.comp_out L) (h : K ⊆ L) (D : G.comp_out K) :
  C.hom h = D ↔ (C : set V) ⊆ (D : set V) :=
⟨ λ h', h' ▸ (C.subset_hom h), C.ind (λ v vnL vD, (vD ⟨vnL, rfl⟩).some_spec) ⟩

lemma hom_eq_iff_not_disjoint (C : G.comp_out L) (h : K ⊆ L) (D : G.comp_out K) :
  C.hom h = D ↔ ¬ disjoint (C : set V) (D : set V) :=
begin
  rw set.not_disjoint_iff,
  split,
  { rintro rfl,
    apply C.ind (λ x xnL, _),
    exact ⟨x, ⟨xnL,rfl⟩, ⟨(λ xK, xnL (h xK)), rfl⟩⟩, },
  { apply C.ind (λ x xnL, _),
    rintro ⟨x,⟨_,e₁⟩,⟨_,rfl⟩⟩,
    rw ←e₁, refl, },
end

lemma hom_refl (C : G.comp_out L) : C.hom (subset_refl L) = C :=
by { change C.map _ = C, erw [induce_hom_id G Lᶜ, connected_component.map_id], }

lemma hom_trans (C : G.comp_out L) (h : K ⊆ L) (h' : M ⊆ K) :
  C.hom (h'.trans h) = (C.hom h).hom h' :=
by { change C.map _ = (C.map _).map _, erw [connected_component.map_comp, induce_hom_comp], refl, }

lemma hom_mk {v : V} (vnL : v ∉ L) (h : K ⊆ L) :
  (G.comp_out_mk vnL).hom h = (G.comp_out_mk (set.not_mem_subset h vnL)) := rfl

lemma hom_inf (C : G.comp_out L) (h : K ⊆ L) (Cinf : (C : set V).infinite) :
  (C.hom h : set V).infinite := set.infinite.mono (C.subset_hom h) Cinf

lemma inf_iff_in_all_ranges {K : finset V} (C : G.comp_out K) :
  (C : set V).infinite ↔ ∀ L (h : K ⊆ L), ∃ D : G.comp_out L, C = D.hom h :=
begin
  classical,
  split,
  { rintro Cinf L h,
    obtain ⟨v,⟨vK,rfl⟩,vL⟩ := set.infinite.nonempty (set.infinite.diff Cinf L.finite_to_set),
    exact ⟨comp_out_mk _ vL, rfl⟩ },
  { rintro h Cfin,
    obtain ⟨D,e⟩ := h (K ∪ Cfin.to_finset) (finset.subset_union_left K Cfin.to_finset),
    obtain ⟨v,vD⟩ := D.nonempty,
    let Ddis := D.disjoint_right,
    simp_rw [finset.coe_union, set.finite.coe_to_finset, set.disjoint_union_left,
             set.disjoint_iff] at Ddis,
    exact Ddis.right ⟨(comp_out.hom_eq_iff_le _ _ _).mp e.symm vD, vD⟩, },
end

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

lemma end_hom_mk_of_mk {s} (sec : s ∈ G.end) {K L : (finset V)ᵒᵖ} (h : L ⟶ K)
  {v : V} (vnL : v ∉ L.unop) (hs : s L = G.comp_out_mk vnL) :
  s K = G.comp_out_mk (set.not_mem_subset (le_of_op_hom h) vnL) :=
begin
  rw [←(sec h), hs],
  apply comp_out.hom_mk,
end

end ends

end simple_graph
