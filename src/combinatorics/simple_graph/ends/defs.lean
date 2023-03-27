/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import category_theory.cofiltered_system
import combinatorics.simple_graph.connectivity
import data.finite.set

/-!
# Ends

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

/--
In an infinite graph, the set of components out of a finite set is nonempty.
-/
instance component_compl_nonempty_of_infinite (G : simple_graph V) [infinite V] (K : finset V) :
  nonempty (G.component_compl K) :=
let ⟨k, kK⟩ := K.finite_to_set.infinite_compl.nonempty in ⟨component_compl_mk _ kK⟩

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

-- This begs for a definition of `connected_component.supp`.
@[simps] def supp_equiv (C : G.component_compl K) :
  C.supp ≃ {v' | connected_component_mk (G.induce Kᶜ) v' = C} :=
{ to_fun := λ v, ⟨⟨v.val, v.prop.some⟩, v.prop.some_spec⟩,
  inv_fun := λ v, ⟨v.val.val, ⟨v.val.prop, by { simpa [component_compl_mk] using v.prop, }⟩⟩,
  left_inv := by { rintro ⟨v, ⟨vnK, rfl⟩⟩, simp only, },
  right_inv := by { rintro ⟨⟨v, vnK⟩, h⟩, simp only [subtype.mk_eq_mk], } }

@[simps] def coe_graph_iso (C : G.component_compl K) :
  C.coe_graph ≃g (G.induce Kᶜ).induce {v' | connected_component_mk (G.induce Kᶜ) v' = C} :=
{ to_equiv := C.supp_equiv,
  map_rel_iff' := λ u v, by simp, }

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

lemma eq_of_subset {C D : G.component_compl K} (h : (C : set V) ⊆ D) : C = D :=
begin
  apply component_compl.pairwise_disjoint.eq,
  simp only [set.not_disjoint_iff_nonempty_inter, set.inter_eq_left_iff_subset.mpr h, C.nonempty],
end

lemma not_subset_right {C : G.component_compl K} : ¬ (C : set V) ⊆ K :=
begin
  obtain ⟨v, vnK, rfl⟩ := C.exists_eq_mk,
  exact λ h, vnK (h $ component_compl_mk_mem _ vnK)
end

/--
Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
lemma mem_of_adj : ∀ {C : G.component_compl K} (c d : V), c ∈ C → d ∉ K → G.adj c d → d ∈ C :=
λ C c d ⟨cnK, h⟩ dnK cd,
  ⟨ dnK, by { rw [←h, connected_component.eq], exact adj.reachable cd.symm, } ⟩

lemma eq_of_adj {C D: G.component_compl K} (c d : V) (cC : c ∈ C) (dD : d ∈ D) (a : G.adj c d) :
  C = D := by
begin
  obtain ⟨_, _, rfl⟩ := cC,
  obtain ⟨_, _, rfl⟩ := dD,
  apply quot.sound, apply adj.reachable, exact a,
end

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

protected lemma connected (C : G.component_compl K) : C.coe_graph.connected :=
(induce_induce G Kᶜ {v : Kᶜ | (G.induce Kᶜ).connected_component_mk v = C}).connected_iff.mp
  C.connected

/--
The unique `C : G.component_compl K` containing the set `D`.
-/
noncomputable def of_connected_disjoint_right {D : set V}
  (Dc : (G.induce D).connected) (Dd : disjoint K D) : G.component_compl K :=
component_compl_mk G (set.disjoint_right.mp Dd Dc.nonempty.some.prop)

lemma subset_of_connected_disjoint_right {D : set V}
  (Dc : (G.induce D).connected) (Dd : disjoint K D) : D ⊆ of_connected_disjoint_right Dc Dd :=
begin
  have : ∀ {u w : D} (p : (G.induce D).walk w u), u = Dc.nonempty.some
           → ↑w ∈ of_connected_disjoint_right Dc Dd, by
  { rintro _ _ p e,
    induction p with _ _ _ _ a q ih,
    { refine e.symm ▸ component_compl_mk_mem _ _, },
    { obtain ⟨_, b⟩ := ih e,
      rw [←b, ←component_compl_mk_eq_of_adj G (set.disjoint_right.mp Dd p_u.prop) _ a],
      apply component_compl_mk_mem, } },
  exact λ w wD, this (Dc.preconnected ⟨w, wD⟩ Dc.nonempty.some).some rfl,
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

lemma hom_eq_of_connected_disjoint_right  (C : G.component_compl L) (h : K ⊆ L) :
  C.hom h = of_connected_disjoint_right C.connected (C.disjoint_right.mono_left h) :=
begin
  rw [hom_eq_iff_not_disjoint, set.not_disjoint_iff],
  refine ⟨_, C.nonempty.some_spec, subset_of_connected_disjoint_right _ _ C.nonempty.some_spec⟩,
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

variables (G)

/-
For a locally finite preconnected graph, the number of components outside of any finite set
is finite.
-/
instance component_compl_finite [locally_finite G] [Gpc : fact $ preconnected G] (K : finset V) :
  finite (G.component_compl K) :=
begin
  classical,
  rcases K.eq_empty_or_nonempty with rfl|h,
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  { dsimp [component_compl],
    rw set.compl_empty,
    haveI := @finite.of_subsingleton _ Gpc.out.subsingleton_connected_component,
    exact finite.of_equiv _ (induce_univ_iso G).connected_component_equiv.symm, },
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  { let touch : G.component_compl K → {v : V | ∃ k : V, k ∈ K ∧ G.adj k v} :=
      λ C, let p := C.exists_adj_boundary_pair Gpc.out h in
        ⟨p.some.1, p.some.2, p.some_spec.2.1, p.some_spec.2.2.symm⟩,
    -- `touch` is injective
    have touch_inj : touch.injective := λ C D h', component_compl.pairwise_disjoint.eq
      (set.not_disjoint_iff.mpr ⟨touch C, (C.exists_adj_boundary_pair Gpc.out h).some_spec.1,
                                 h'.symm ▸ (D.exists_adj_boundary_pair Gpc.out h).some_spec.1⟩),
    -- `touch` has finite range
    haveI : finite (set.range touch), by
    { refine @subtype.finite _ (set.finite.to_subtype _) _,
      have : {v : V | ∃ (k : V), k ∈ K ∧ G.adj k v} = finset.bUnion K (λ v, G.neighbor_finset v), by
      { ext v,
        simp only [set.mem_Union, exists_prop, set.mem_set_of_eq, finset.coe_bUnion,
                  finset.mem_coe, mem_neighbor_finset], },
      rw this,
      apply finset.finite_to_set, },
    -- hence `touch` has a finite domain
    apply finite.of_injective_finite_range touch_inj, },
end

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

lemma component_compl.infinite_iff_in_eventual_range {G : simple_graph V} {K : (finset V)ᵒᵖ}
  (C : G.component_compl_functor.obj K) :
  C.supp.infinite ↔ C ∈ G.component_compl_functor.eventual_range K :=
begin
  simp only [C.infinite_iff_in_all_ranges, category_theory.functor.eventual_range,
             set.mem_Inter, set.mem_range, component_compl_functor_map],
  exact ⟨λ h Lop KL, h Lop.unop (le_of_op_hom KL), λ h L KL, h (opposite.op L) (op_hom_of_le KL)⟩,
end

lemma component_compl_functor_to_eventual_ranges_obj_eq
  [is_cofiltered_or_empty (finset V)ᵒᵖ] {G : simple_graph V} {K : (finset V)ᵒᵖ} :
  G.component_compl_functor.to_eventual_ranges.obj K =
  { C : G.component_compl K.unop | C.supp.infinite } :=
begin
  apply congr_arg subtype (funext $ λ x, eq.symm $ propext _),
  apply component_compl.infinite_iff_in_eventual_range,
end

end ends

end simple_graph
