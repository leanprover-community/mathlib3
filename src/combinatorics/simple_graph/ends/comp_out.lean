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

-- for mathlib?
-- Can probably be golfed heavily!!
lemma connected_component.connected (C : G.connected_component) :
(G.induce {v : V | connected_component_mk G v = C}).connected :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v,
  let C := {v_1 : V | G.connected_component_mk v_1 = G.connected_component_mk v},
  rw connected_iff,
  fsplit,
  { rintro ⟨u,uv⟩ ⟨w,wv⟩,
    simp at uv wv,
    obtain ⟨p⟩ := uv.trans wv.symm,
    constructor,
    suffices : ∀  x ∈ p.support, x ∈ C,
    { apply walk.to_induced,
      exact this, },
    by_contra, push_neg at h,
    obtain ⟨x,xsup,xnC⟩ := h,
    rw walk.mem_support_iff_exists_append at xsup,
    obtain ⟨ux,xw,rfl⟩ := xsup,
    apply xnC,
    let ux' : G.reachable u x := ⟨ux⟩,
    simp,
    exact ux'.symm.trans uv, },
  { simp, use v, }
end


-- Better since it uses fewer lemmas not in mathlib (I guess none at all)
lemma connected_component.connected' (C : G.connected_component) :
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

lemma adj [Gc : G.preconnected] (hK : K.nonempty) (C : G.comp_out K) (dis : disjoint K C) :
  ∃ (c ∈ C) (k ∈ K), G.adj c k :=
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
  apply nonadj,
  use [x,y],
  use [xC,ynC],
  rw set.disjoint_iff at dis,
  use (λ xK, dis ⟨xK,xC⟩),
  use (λ yK, h x xC y yK xy),
  exact xy,
end

lemma connected (C : G.comp_out K) : (G.induce (C : set V)).connected :=
begin
  apply connected.mono,
  show ((G.out K).induce (C : set V)) ≤ (G.induce (C : set V)), by
  { rintro x y a, dsimp [out] at a, dsimp, tauto, },
  show ((G.out K).induce (C : set V)).connected, by apply connected_component.connected',
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


end comp_out

end simple_graph
