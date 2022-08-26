import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic
import .mathlib
import .connected

open function finset set classical simple_graph.walk relation

local attribute [instance] prop_decidable

universes u v w

noncomputable theory

namespace simple_graph


variables  {V : Type u}
variables (G : simple_graph V)  (K : set V)


-- Some variation of this should surely be included in mathlib ?!
lemma connected_component.connected (C : G.connected_component) :
(G.induce {v : V | connected_component_mk G v = C}).connected :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v,
  let C := {v_1 : V | G.connected_component_mk v_1 = G.connected_component_mk v},
  rw connected_iff,
  fsplit,
  { suffices : ∀ u : C, (G.induce C).reachable u ⟨v,by {simp only [mem_set_of_eq],}⟩,
    { exact λ u w, (this u).trans (this w).symm, },
    rintro ⟨u,uv⟩,
    simp only [mem_set_of_eq, connected_component.eq] at uv,
    obtain ⟨uv'⟩ := uv,
    induction uv' with a b c d e f g,
    { refl, },
    { --have : c ∈ C, by {simp at uv ⊢, constructor, exact f,},
      simp only [mem_set_of_eq, connected_component.eq] at *,
      constructor,
      apply walk.cons, rotate,
      exact (g ⟨f⟩).some,
      simp only [comap_adj, embedding.coe_subtype, subtype.coe_mk],
      exact e,}},
  { simp, use v, }
end



def out : simple_graph V := {
  adj := λ u v, u ∉ K ∧ v ∉ K ∧ G.adj u v,
  symm := by {rintro u v a, tauto, },
  loopless := by {rintro u a, exact G.loopless u a.2.2,}}

lemma out.sub (G : simple_graph V)  (K : set V) : out G K ≤ G := λ u v a, a.2.2

lemma out.mono (G : simple_graph V)  (K L : set V) (h : K ⊆ L) : G.out L ≤ G.out K :=
λ u v ⟨unL,vnL,uav⟩, ⟨(λ uK, unL (h uK)), (λ vK, (vnL (h vK))), uav⟩

lemma out.reachable_mono (G : simple_graph V)  (K L : set V) (h : K ⊆ L) (u v : V) :
  (G.out L).reachable u v → (G.out K).reachable u v :=
begin
  rw [reachable_iff_refl_trans_gen,reachable_iff_refl_trans_gen],
  apply refl_trans_gen.mono,
  apply out.mono,
  exact h,
end

def comp_out := (G.out K).connected_component

@[reducible, simp] def comp_out.supp {G : simple_graph V} {K : set V} (C : G.comp_out K) :=
  {v : V | connected_component_mk (G.out K) v = C}



instance {G : simple_graph V} {K : set V} : set_like (G.comp_out K) V :=
⟨ comp_out.supp
, by
  { refine @connected_component.ind₂ _ _ (λ (C D : G.comp_out K), C.supp = D.supp → C = D) _,
    rintros v w, simp only [comp_out.supp, connected_component.eq], rintro eq,
    change v ∈ {u | (out G K).reachable u w}, rw ←eq, simp only [mem_set_of_eq],} ⟩

@[simp] lemma comp_out.mem_supp_iff {G : simple_graph V} {K : set V}
  {v : V} {C : comp_out G K} :
(v ∈ C) ↔ connected_component_mk (out G K) v = C :=
begin
  simp only [set_like.has_mem,has_mem.mem,coe,coe_to_lift,lift_t,has_lift_t.lift,coe_t,has_coe_t.coe,set_like.coe],
  refl,
end

def inf_comp_out := { C : comp_out G K // (C : set V).infinite }
def fin_comp_out := { C : comp_out G K // (C : set V).finite }

namespace comp_out

variables {G}
variables {K}  {L : set V} {KL : K ⊆ L}

@[simp] lemma nempty (C : G.comp_out K) : (C : set V).nonempty := by
{ refine C.ind _,
  rintro v,
  use v,
  simp,}

def of_vertex (G : simple_graph V) (K : set V)  (v : V) : G.comp_out K := connected_component_mk (out G K) v
def of_vertex_mem (v : V) : v ∈ (of_vertex G K v : set V) := by {dsimp only [of_vertex], simp,}


@[protected]
lemma disjoint (C D : G.comp_out K) (ne : C ≠ D) : disjoint (C : set V) (D : set V) :=
begin
  revert C D,
  refine connected_component.ind₂ _,
  rintro v w ne,
  rintro u,
  simp only [set.inf_eq_inter, mem_inter_eq, set_like.mem_coe, mem_supp_iff,
             connected_component.eq, set.bot_eq_empty, mem_empty_eq, and_imp],
  rintro uv uw,
  simp only [_root_.ne.def, connected_component.eq] at uv uw ne,
  exact ne (uv.symm.trans uw),
end

lemma eq_of_not_disjoint (C D : G.comp_out K) (nd : ¬ disjoint (C : set V) (D : set V)) : C = D :=
begin
  rw set.not_disjoint_iff at nd,
  simp only [set_like.mem_coe, mem_supp_iff] at nd,
  obtain ⟨x,rfl,rfl⟩ := nd, refl,
end

@[simp]
lemma intersects_iff_singleton_in (C : G.comp_out K) : (¬ disjoint K C) ↔ (∃ (k ∈ K), {k} = (C : set V)) :=
begin
  split,
  { revert C,
    refine connected_component.ind _, intro v,
    rintro ndis,
    rw set.not_disjoint_iff at ndis,
    obtain ⟨k,kK,kv⟩ := ndis, use [k,kK],
    simp only [set_like.mem_coe, mem_supp_iff, connected_component.eq] at kv,
    ext,
    simp only [mem_singleton_iff, set_like.mem_coe, mem_supp_iff, connected_component.eq],
    split,
    { rintro e, subst_vars, exact kv, },
    { rintro xv, obtain ⟨kx⟩ := kv.trans xv.symm,
      cases kx,
      { refl, },
      { exfalso, dsimp only [out] at kx_h, exact kx_h.1 kK},
    },
  },
  {rintro ⟨k,kK,e⟩, simp only [←e,kK, set.disjoint_singleton_right, not_true, not_false_iff], }
end

lemma nonadj (C : G.comp_out K) : ¬ (∃ (c d : V), c ∈ C ∧ d ∉ C ∧ c ∉ K ∧ d ∉ K ∧ G.adj c d) :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v,
  rintro ⟨c,d,cC,dnC,cK,dK,cd⟩,
  have cd' : (G.out K).reachable c d := ⟨walk.cons ⟨cK,dK,cd⟩ nil⟩,
  simp at cC dnC,
  exact dnC (cC.symm.trans cd').symm,
end

lemma adj [Gc : G.preconnected] [hK : K.nonempty] (C : G.comp_out K) (dis : disjoint K C) :
  ∃ (ck : V × V), ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.adj ck.1 ck.2 :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v dis,
  let C : G.comp_out K := (G.out K).connected_component_mk v,
  by_contradiction h,
  push_neg at h,
  suffices : set.univ = (C : set V), {
    let k := hK.some,
    have kC := (set.mem_univ k), rw this at kC,
    rw set.disjoint_iff at dis,
    exact dis ⟨hK.some_spec,kC⟩,
  },
  symmetry,
  rw set.eq_univ_iff_forall,
  rintro u,
  by_contradiction unC,
  obtain ⟨p⟩ := Gc v u,
  obtain ⟨x,y,xy,xC,ynC⟩ := walk.pred_adj_non_pred v u p C (by {simp}) unC,
  refine @nonadj V G K C _,
  rw set.disjoint_iff at dis,
  use [x,y,xC,ynC],
  use (λ xK, dis ⟨xK,xC⟩),
  use (λ (yK : y ∈ K), h ⟨x,y⟩ xC yK xy),
  exact xy,
end

lemma connected (C : G.comp_out K) : (G.induce (C : set V)).connected :=
begin
  apply connected.mono,
  show ((G.out K).induce (C : set V)) ≤ (G.induce (C : set V)), by
  { rintro x y a, dsimp [out] at a, dsimp, tauto, },
  show ((G.out K).induce (C : set V)).connected, by apply connected_component.connected,
end

def of_connected_disjoint (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint S K) : G.comp_out K :=
begin
  rw connected_iff at conn,
  exact of_vertex G K conn.right.some,
end

lemma of_connected_disjoint_sub (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint S K) : S ⊆ of_connected_disjoint S conn dis :=
begin
  have : ∀ s t : S, (G.induce S).adj s t → (G.out K).adj s t, by
  { rintro ⟨s,sS⟩ ⟨t,tS⟩ a,
    simp only [subtype.coe_mk, comap_adj, embedding.coe_subtype,out] at a ⊢,
    exact ⟨(λ sK, (set.disjoint_iff).mp dis ⟨sS,sK⟩),(λ tK, (set.disjoint_iff).mp dis ⟨tS,tK⟩),a⟩,},
  have : ∀ s t : S, (G.induce S).reachable s t → (G.out K).reachable s t, by {
    rintro ⟨s,hs⟩ ⟨t,ht⟩ ⟨r⟩,
    constructor,
    induction r,
    { exact nil, },
    { apply walk.cons (this r_u r_v r_h) r_ih,},},
  rw connected_iff at conn,
  rintro s sS,
  dsimp only [of_connected_disjoint,of_vertex],
  simp only [set_like.mem_coe, mem_supp_iff, connected_component.eq],
  exact this ⟨s,sS⟩ conn.right.some (conn.left ⟨s,sS⟩ conn.right.some),
end


section finiteness

def to_thickening_aux (G : simple_graph V) (K : set V) (Gpc : G.preconnected) (Glc : G.locally_finite)
  (Kf : K.finite) (Kn : K.nonempty) : Π (C : G.comp_out K), { x : V | x ∈ (thicken G K) ∧ x ∈ C} :=
begin
  rintro C,
  by_cases h : disjoint K C,
  { let ck := (@adj V G K Gpc Kn C h).some,
    obtain ⟨cC,kK,ack⟩ := (@adj V G K Gpc Kn C h).some_spec,
    use ck.1, dsimp only [thicken],
    split, right,use ck.2, use kK, exact ack.symm, exact cC, },
  { simp only [intersects_iff_singleton_in, exists_prop] at h,
    use h.some, split, left, exact h.some_spec.left,
    rw ←set_like.mem_coe,
    let := h.some_spec.right,
    have : h.some ∈ {h.some}, by apply set.mem_singleton, convert this, symmetry, assumption, -- that's dirty
    },
end

def to_thickening (G : simple_graph V) (K : set V)  (Gpc : G.preconnected) (Glc : G.locally_finite)
  (Kf : K.finite) (Kn : K.nonempty) : G.comp_out K → (thicken G K) :=
λ C, ⟨(to_thickening_aux G K Gpc Glc Kf Kn C).val,(to_thickening_aux G K Gpc Glc Kf Kn C).prop.left⟩

lemma to_thickening_inj  (G : simple_graph V) (K : set V)  (Gpc : G.preconnected) (Glc : G.locally_finite)
  (Kf : K.finite) (Kn : K.nonempty) : function.injective (to_thickening G K Gpc Glc Kf Kn) :=
begin
  rintro C D,
  dsimp [to_thickening, thicken], simp,
  obtain ⟨x,xK,xC⟩ := to_thickening_aux G K Gpc Glc Kf Kn C,
  obtain ⟨y,yK,yD⟩ := to_thickening_aux G K Gpc Glc Kf Kn D,
  simp only [subtype.coe_mk],
  rintro rfl,
  apply eq_of_not_disjoint,
  rw set.not_disjoint_iff,
  exact ⟨x,xC,yD⟩,
end

lemma comp_out_finite  (G : simple_graph V) (K : set V)  (Gpc : G.preconnected) (Glf : G.locally_finite)
  (Kf : K.finite) (Kn : K.nonempty)  :
  finite (G.comp_out K) :=
begin
  haveI : finite (G.thicken K), by {rw set.finite_coe_iff, apply @thicken.finite _ _ Glf _ Kf, },
  apply finite.of_injective (to_thickening G K Gpc Glf Kf Kn),
  apply to_thickening_inj,
end

end finiteness

section back

def back {K L : set V} (h : K ⊆ L) (C : G.comp_out L) : G.comp_out K :=
begin
  fapply @connected_component.lift V (G.out L) _ (λ v, connected_component_mk _ v), rotate,
  exact C,
  rintro v w p pp,
  simp,
  apply out.reachable_mono G K L h,
  exact (⟨p⟩: (G.out L).reachable v w),
end

lemma back_sub {K L : set V} (h : K ⊆ L) (C : G.comp_out L) : (C : set V) ⊆ (C.back h : set V) :=
begin
  refine connected_component.ind _ C,
  rintro v u uv,
  dsimp [back], simp at uv ⊢,
  apply out.reachable_mono G K L h u v uv,
end

@[simp]
lemma eq_back_iff_sub {K L : set V} (h : K ⊆ L) (C : G.comp_out L) (D : G.comp_out K) :
  C.back h = D ↔ (C : set V) ⊆ D :=
begin
  split,
  { rintro rfl, apply back_sub, },
  { rintro sub,
    apply eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    obtain ⟨v,vC⟩ := C.nempty,
    use v,
    exact ⟨C.back_sub h vC ,sub vC⟩,}
end

lemma back_refl_apply {K : set V} (C : G.comp_out K) : C.back (subset_refl K) = C :=
by {refine C.ind _, rintro v, dsimp only [back], refl,}

lemma back_trans_apply {K L M : set V} (kl : K ⊆ L) (lm : L ⊆ M) (C : G.comp_out M) :
  (C.back ‹L ⊆ M›).back ‹K ⊆ L› = C.back (‹K ⊆ L›.trans  ‹L ⊆ M›) :=
by {refine C.ind _, rintro v, dsimp only [back], simp only [connected_component.lift_mk],}

end back

@[reducible]
def inf (C : G.comp_out K) := (C : set V).infinite

section infinite

lemma disjoint_of_inf (C : G.comp_out K) : C.inf → disjoint K C :=
begin
  rintro Cinf,
  by_contra,
  rw intersects_iff_singleton_in at h,
  obtain ⟨k,_,e⟩ := h, unfold inf at Cinf, rw ←e at Cinf,
  exact Cinf (set.finite_singleton k),
end

lemma back_of_inf {K L : set V} (h : K ⊆ L) (C : G.comp_out L) : C.inf → (C.back h).inf :=
begin
  rintro Cinf,
  apply set.infinite.mono,
  exact C.back_sub h,
  exact Cinf,
end

lemma in_all_ranges_of_inf (Kfin : K.finite) (C : G.comp_out K) (Cinf : C.inf) {L : set V} (Lfin : L.finite) (h : K ⊆ L) :
  C ∈ set.range (back h : (G.comp_out L) → (G.comp_out K)) :=
begin
  suffices : ∃ v : V, v ∈ C ∧ v ∉ L,
  { obtain ⟨c,cC,cnL⟩ := this,
    use of_vertex G L c,
    apply eq_of_not_disjoint,
    rw set.not_disjoint_iff, use c, split, rotate, exact cC,
    apply mem_of_mem_of_subset,
    apply @of_vertex_mem V G L,
    apply back_sub,},
  have : ((C : set V) \ L).infinite, by {exact infinite.diff Cinf Lfin,},
  use this.nonempty.some,
  exact this.nonempty.some_spec,
end

lemma inf_of_in_all_ranges (Kfin : K.finite) (C : G.comp_out K) (Cdis : disjoint K C)
  (mem_ranges : ∀ {L : set V} (h : K ⊆ L), C ∈ set.range (back h : (G.comp_out L) → (G.comp_out K))) : C.inf :=
begin
  rintro Cfin,
  let L := K ∪ C,
  have Lfin : L.finite := set.finite.union Kfin Cfin,
  have : K ⊆ L := set.subset_union_left K C,
  obtain ⟨D,e⟩ := mem_ranges ‹K⊆L›,
  simp only [eq_back_iff_sub] at e,
  suffices : (D : set V) = ∅, { have : (D : set V).nonempty, by simp only [nempty], finish,},
  sorry,
  -- trouble here because of singletons…
end

end infinite


end comp_out

end simple_graph
