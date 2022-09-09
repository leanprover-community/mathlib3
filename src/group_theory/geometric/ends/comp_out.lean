import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic
import .for_mathlib.misc
import .for_mathlib.connected

open function finset set classical simple_graph.walk relation

local attribute [instance] prop_decidable

universes u v w

noncomputable theory

namespace simple_graph

variables  {V : Type u}
variables (G : simple_graph V)  (K : set V)

/--!

## Connected components outside a given set of vertices

One of the crucial ingredients needed for defining the ends of a graph `G` is the notion of
the "connected components outside" a given set of vertices `K`.

The approach taken here (chosen after several iterations) is to first define a suitable subgraph `out`
of the original graph `G` given a set of vertices `K`, which retains the original graph structure
outside of `K` but removes all edges incident to `K`.

The connected components outside `K` are defined to be the connected components of the modified graph `out G K`.
The caveat is that all elements of `K` are singleton connected components in the modified graph, so care has to be
taken to exclude them from theorems. This does not prove to be too much of a problem in practice.
-/

def out : simple_graph V := {
  adj := λ u v, u ∉ K ∧ v ∉ K ∧ G.adj u v,
  symm := by {rintro u v a, tauto, },
  loopless := by {rintro u a, exact G.loopless u a.2.2,}}

-- `out` is a subgraph of the original graph
lemma out.sub (G : simple_graph V)  (K : set V) : out G K ≤ G := λ u v a, a.2.2

-- `out` is a monotonic function of the set that is being removed
lemma out_mono (G : simple_graph V)  {K L : set V} (h : K ⊆ L) : G.out L ≤ G.out K :=
λ u v ⟨unL,vnL,uav⟩, ⟨(λ uK, unL (h uK)), (λ vK, (vnL (h vK))), uav⟩

-- `out` is an isomorphism-invariant construction
def out.iso {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G') (K : set V) :
  G.out K ≃g G'.out (φ '' K) :=
begin
  fsplit, exact φ.1, dsimp only [out],
  rintro u v,
  simp only [injective.mem_set_image (rel_iso.injective φ), rel_iso.coe_fn_to_equiv, and.congr_right_iff],
  rintro unK vnK, apply φ.2,
end

@[simp]
lemma out.iso_eq_apply {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'}
  (φ : G ≃g G') (K : set V) (v : V) : (out.iso φ K) v = φ v := rfl

@[simp]
lemma out.iso_eq_apply_symm {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'}
  (φ : G ≃g G') (K : set V) (v : V') : (out.iso φ K).symm v = φ.symm v := rfl

-- If two vertices are reachable outside a set, then they are reachable outside a smaller one
lemma out.reachable_mono (G : simple_graph V)  (K L : set V) (h : K ⊆ L) (u v : V) :
  (G.out L).reachable u v → (G.out K).reachable u v :=
begin
  rw [reachable_iff_refl_trans_gen,reachable_iff_refl_trans_gen],
  apply refl_trans_gen.mono,
  apply out_mono,
  exact h,
end

lemma out.empty (G : simple_graph V) : G.out ∅ = G := by {ext, obviously,}

def out.walk_conv {G : simple_graph V}  {K L : set V} {u v : V}
  (p : (G.out K).walk u v) (pdis : ∀ x ∈ p.support, x ∉ L) : (G.out L).walk u v :=
begin
  induction p,
  { exact walk.nil },
  { apply walk.cons' p_u p_v p_w,
    { split, apply pdis,
      simp only [support_cons, list.mem_cons_iff, eq_self_iff_true, true_or],
      split, apply pdis,
      simp only [support_cons, list.mem_cons_iff, start_mem_support, or_true],
      exact p_h.2.2, },
    { apply p_ih,
      rintro x xsup, apply pdis,
      simp only [xsup, support_cons, list.mem_cons_iff, or_true], }, },
end

/-- The components outside a given set of vertices `K` -/
@[reducible] def comp_out := (G.out K).connected_component

@[simp] lemma comp_out.mem_supp_iff {G : simple_graph V} {K : set V}
  {v : V} {C : comp_out G K} :
(v ∈ C) ↔ connected_component_mk (out G K) v = C := by {refl,}


namespace comp_out

variables {G}
variables {K}  {L : set V} {KL : K ⊆ L}

/-- Infinite connected components -/
@[reducible]
def inf (C : G.comp_out K) := (C : set V).infinite

/-- Finite connected components -/
@[reducible,protected]
def fin (C : G.comp_out K) := (C : set V).finite

/-- Components that are disjoint from the set `K` that is being removed
  This excludes the "trivial" connected components, i.e., the elements of `K`,
  which are singleton connected components in `out`.
-/
@[reducible]
def dis (C : G.comp_out K) := disjoint K (C : set V)

lemma comp_out.empty : (G.comp_out ∅) = G.connected_component :=
by {unfold comp_out,rw out.empty,}

lemma comp_out.eq_of_eq_set {C D : G.comp_out K} : (C : set V) = ↑D ↔ C = D :=
begin
  sorry,
end

lemma of_empty_is_singleton (Gpc : G.preconnected) : ∀ C : (G.comp_out ∅),  (C : set V) = univ :=
begin
  apply connected_component.of_preconnected,
  rw [out.empty], assumption,
end

lemma of_empty_finite (Gpc : G.preconnected) : finite (G.comp_out ∅) :=
begin
  haveI : subsingleton (G.comp_out ∅), by {
    constructor,
    rintro C D,
    rw connected_component.eq_of_eq_supp, -- why doesn't the `ext` tactic take care of that ?
    transitivity,
    apply of_empty_is_singleton Gpc,
    symmetry,
    apply of_empty_is_singleton Gpc, },
  haveI : fintype (G.comp_out ∅), by {apply fintype.of_subsingleton'},
  apply finite.of_fintype,
end


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
lemma not_dis_iff_singleton_in (C : G.comp_out K) : ¬ C.dis ↔ (∃ (k ∈ K), {k} = (C : set V)) :=
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
  {rintro ⟨k,kK,e⟩, simp only [dis,←e,kK, set.disjoint_singleton_right, not_true, not_false_iff], }
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

-- Every connected component disjoint from `K` has a vertex adjacent to it
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

-- The unique connected component containing a connected set disjoint from `K`
def of_connected_disjoint (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint K S) : G.comp_out K :=
begin
  rw connected_iff at conn,
  exact of_vertex G K conn.right.some.val,
end

lemma of_connected_disjoint_dis (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint K S) : (of_connected_disjoint S conn dis).dis :=
begin
  rw connected_iff at conn,
  by_contra h,
  rw not_dis_iff_singleton_in at h,
  obtain ⟨k,kK,e⟩ := h,
  unfold of_connected_disjoint at e,
  let sC := @of_vertex_mem V G K conn.right.some.val,
  rw ←e at sC,
  simp only [subtype.val_eq_coe, mem_singleton_iff] at sC,
  rw ←sC at kK,
  apply dis, exact ⟨kK,conn.right.some.prop⟩,
end

lemma of_connected_disjoint_sub (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint K S) : S ⊆ of_connected_disjoint S conn dis :=
begin
  have : ∀ s t : S, (G.induce S).adj s t → (G.out K).adj s t, by
  { rintro ⟨s,sS⟩ ⟨t,tS⟩ a,
    simp only [subtype.coe_mk, comap_adj, embedding.coe_subtype,out] at a ⊢,
    exact ⟨(λ sK, (set.disjoint_iff).mp dis ⟨sK,sS⟩),(λ tK, (set.disjoint_iff).mp dis ⟨tK,tS⟩),a⟩,},
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

def to_thickening_aux (G : simple_graph V) (K : finset V) (Gpc : G.preconnected) (Glc : G.locally_finite)
  (Kn : K.nonempty) : Π (C : G.comp_out K), { x : V | x ∈ (thicken G K) ∧ x ∈ C} :=
begin
  rintro C,
  by_cases h : C.dis,
  { let ck := (@adj V G K Gpc Kn C h).some,
    obtain ⟨cC,kK,ack⟩ := (@adj V G K Gpc Kn C h).some_spec,
    use ck.1, dsimp only [thicken],
    split, right,use ck.2, use kK, exact ack.symm, exact cC, },
  { simp only [not_dis_iff_singleton_in, exists_prop] at h,
    use h.some, split, left, exact h.some_spec.left,
    rw ←set_like.mem_coe,
    let := h.some_spec.right,
    have : h.some ∈ {h.some}, by apply set.mem_singleton, convert this, symmetry, assumption, -- that's dirty
    },
end

-- A vertex of a component contained in the unit thickening of `K`
def to_thickening (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glc : G.locally_finite)
  (Kn : K.nonempty) : G.comp_out K → (thicken G K) :=
λ C, ⟨(to_thickening_aux G K Gpc Glc Kn C).val,(to_thickening_aux G K Gpc Glc Kn C).prop.left⟩

lemma to_thickening_inj  (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glc : G.locally_finite)
  (Kn : K.nonempty) : function.injective (to_thickening G K Gpc Glc Kn) :=
begin
  rintro C D,
  dsimp [to_thickening, thicken], simp,
  obtain ⟨x,xK,xC⟩ := to_thickening_aux G K Gpc Glc Kn C,
  obtain ⟨y,yK,yD⟩ := to_thickening_aux G K Gpc Glc Kn D,
  simp only [subtype.coe_mk],
  rintro rfl,
  apply eq_of_not_disjoint,
  rw set.not_disjoint_iff,
  exact ⟨x,xC,yD⟩,
end

-- A locally finite graph has finitely many components outside a finite set
lemma comp_out_finite  (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glf : G.locally_finite) :
  finite (G.comp_out K) :=
begin
    by_cases Kn : K.nonempty,
  -- nonempty case
  haveI : finite (G.thicken K), by {rw set.finite_coe_iff, apply @thicken.finite _ _ Glf _, },
  apply finite.of_injective (to_thickening G K Gpc Glf Kn),
  apply to_thickening_inj,
  -- empty case
  rw finset.not_nonempty_iff_eq_empty at Kn,
  rw Kn,
  rw finset.coe_empty,
  exact of_empty_finite Gpc,
end

lemma fin_comp_out_finite (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glf : G.locally_finite) : finite ({C : G.comp_out K // C.fin}) := by {
  refine finite.to_subtype _,
  refine finite.subset _ _,
  exact univ,
  refine finite_univ_iff.mpr _,
  exact comp_out_finite G K Gpc Glf,
  obviously,}

lemma fin_comp_out_finset (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glf : G.locally_finite) : finset (G.comp_out K) := (set.finite.to_finset (set.finite_coe_iff.mp (fin_comp_out_finite G K Gpc Glf)))

lemma inf_comp_out_finite (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glf : G.locally_finite) : finite ({C : G.comp_out K // C.inf}) := by {
  refine finite.to_subtype _,
  refine finite.subset _ _,
  exact univ,
  refine finite_univ_iff.mpr _,
  exact comp_out_finite G K Gpc Glf,
  obviously,}

lemma inf_comp_out_finset (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected) (Glf : G.locally_finite) (Kn : K.nonempty) : finset (G.comp_out K) := (set.finite.to_finset (set.finite_coe_iff.mp (inf_comp_out_finite G K Gpc Glf)))

end finiteness


section back

/-- Every connected component outside a given set is contained in a unique connected component outside a smaller set.
  `back` takes a component outside a set `L` to a component outside a set `K`, when `K ⊆ L`. -/
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

@[simp]
lemma back_refl_apply {K : set V} (C : G.comp_out K) : C.back (subset_refl K) = C :=
by {refine C.ind _, rintro v, dsimp only [back], refl,}

@[simp]
lemma back_trans_apply {K L M : set V} (kl : K ⊆ L) (lm : L ⊆ M) (C : G.comp_out M) :
  (C.back ‹L ⊆ M›).back ‹K ⊆ L› = C.back (‹K ⊆ L›.trans  ‹L ⊆ M›) :=
by {refine C.ind _, rintro v, dsimp only [back], simp only [connected_component.lift_mk],}

end back


section dis

lemma back_of_dis {K L : set V} (h : K ⊆ L) (C : G.comp_out L) : C.dis → (C.back h).dis :=
begin
  rintro Cdis,
  dsimp only [dis] at Cdis ⊢,
  by_contra h',
  simp at h',
  obtain ⟨k,kK,backk⟩ := h',
  let c := C.nempty.some,
  let cC := C.nempty.some_spec,
  have cL : c ∈ L, by {
    refine mem_of_mem_of_subset _ (by { simp, exact mem_of_mem_of_subset kK h } : {k} ⊆ L),
    refine mem_of_mem_of_subset cC _,
    rw backk,
    apply C.back_sub h,},
  rw set.disjoint_iff at Cdis,
  exact Cdis ⟨cL,cC⟩,
end

end dis


section infinite

lemma dis_of_inf (C : G.comp_out K) : C.inf → C.dis :=
begin
  rintro Cinf,
  by_contra,
  rw not_dis_iff_singleton_in at h,
  obtain ⟨k,_,e⟩ := h, unfold inf at Cinf, rw ←e at Cinf,
  exact Cinf (set.finite_singleton k),
end

lemma exists_inf [infinite V] (G : simple_graph V) (K : finset V)  (Gpc : G.preconnected)
  (Glf : G.locally_finite) : ∃ C : G.comp_out K, C.inf :=
begin

  by_contra h, push_neg at h,
  have : set.univ = ⋃ (C : G.comp_out K), (C : set V), by {
    symmetry,
    rw set.eq_univ_iff_forall, rintro x, use of_vertex G K x,
    simp only [of_vertex, mem_range_self, set_like.mem_coe, mem_supp_iff, true_and],},
  have : (@set.univ V).finite, by {
    rw this,
    haveI : finite (G.comp_out K), by apply comp_out_finite G K Gpc Glf,
    apply set.finite_Union,
    simp_rw set.not_infinite at h,
    exact h,},
  apply set.infinite_univ this,

end

lemma back_of_inf {K L : set V} (h : K ⊆ L) (C : G.comp_out L) : C.inf → (C.back h).inf :=
begin
  rintro Cinf,
  apply set.infinite.mono,
  exact C.back_sub h,
  exact Cinf,
end

lemma in_all_ranges_of_inf {K : finset V} (C : G.comp_out K) (Cinf : C.inf) :
  ∀ {L : finset V} (h : K ⊆ L), ∃ (D : G.comp_out L), D.dis ∧  D.back h = C :=
begin
  rintro L h,
  suffices : ∃ v : V, v ∈ C ∧ v ∉ L,
  { obtain ⟨c,cC,cnL⟩ := this,
    use of_vertex G L c, split,
    { by_contra notdis,
      rw not_dis_iff_singleton_in at notdis,
      obtain ⟨k,l,r⟩ := notdis,
      have ck : c ∈ {k}, by {rw r,apply of_vertex_mem,},
      simp only [mem_singleton_iff] at ck,
      rw ←ck at l,
      exact cnL l,},
    { apply eq_of_not_disjoint,
      rw set.not_disjoint_iff, use c, split, rotate, exact cC,
      apply mem_of_mem_of_subset,
      apply @of_vertex_mem V G L,
      apply back_sub,},},
  have : ((C : set V) \ L).infinite, by {apply infinite.diff Cinf, exact to_finite L,},
  use this.nonempty.some,
  exact this.nonempty.some_spec,
end

lemma inf_of_in_all_ranges {K : finset V} (C : G.comp_out K)
  (mem_ranges : ∀ {L : finset V} (h : K ⊆ L), ∃ (D : G.comp_out L), D.dis ∧  D.back h = C) : C.inf :=
begin
  rintro Cfin,
  let L_ := (K : set V) ∪ C,
  have L_fin : L_.finite := set.finite.union (to_finite K) Cfin,
  let L : finset V := set.finite.to_finset L_fin,
  have : K ⊆ L := by {rw ← finset.coe_subset, simp only [finite.coe_to_finset, set.subset_union_left],},
  obtain ⟨D,dis,e⟩ := mem_ranges ‹K ⊆ L›,
  simp only [eq_back_iff_sub] at e,
  suffices : (D : set V) = ∅, { have : (D : set V).nonempty, by simp only [nempty], finish,},
  have : disjoint (C : set V) D := disjoint.mono_left (by simp) dis,
  rw set.disjoint_iff_inter_eq_empty at this,
  rw ←this,
  symmetry,
  rw set.inter_eq_right_iff_subset,
  exact e,
end

end infinite


section misc

def equiv_of_iso {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) : G.comp_out K ≃ G'.comp_out (φ '' K) :=
begin
  apply connected_component.equiv_of_iso,
  apply out.iso,
end

lemma equiv_of_iso.image{V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) (C : G.comp_out K) : (φ '' C) = (equiv_of_iso φ K C) :=
begin
  refine C.ind _,
  rintro v,
  dsimp only [equiv_of_iso, connected_component.equiv_of_iso,out.iso],
  simp only [rel_iso.coe_fn_mk, rel_iso.coe_fn_to_equiv, equiv.coe_fn_mk, connected_component.lift_mk],
  ext,
  simp only [set.mem_image, set_like.mem_coe, mem_supp_iff, connected_component.eq],
  split,
  rintro ⟨y,⟨yv⟩,rfl⟩, exact ⟨yv.map ((out.iso φ K).to_hom)⟩,
  rintro ⟨yv⟩, use φ.symm x, refine ⟨_,by simp only [rel_iso.apply_symm_apply]⟩,
  constructor,
  convert yv.map (out.iso φ K).symm.to_hom,
  change v = (out.iso φ K).symm (φ v),
  rw out.iso_eq_apply_symm φ K, simp only [rel_iso.symm_apply_apply],
end

lemma equiv_of_iso.dis {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) (C : G.comp_out K) : C.dis ↔ (equiv_of_iso φ K C).dis :=
begin
  dsimp only [dis],
  simp only [←equiv_of_iso.image],
  symmetry,
  apply disjoint_image_iff,
  exact rel_iso.injective φ,
end

lemma equiv_of_iso.inf {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) (C : G.comp_out K) : C.inf ↔ (equiv_of_iso φ K C).inf :=
begin
  dsimp only [inf],
  simp only [←equiv_of_iso.image],
  symmetry,
  apply infinite_image_iff,
  refine injective.inj_on _ ↑C,
  exact rel_iso.injective φ,
end


section extend

variables (G) (Gpc : G.preconnected) (Glf : G.locally_finite)
          (k : finset V) (kn : k.nonempty) (Kc : (G.induce (k : set V)).connected)

/-- Given a finite set of vertices `K`, `extend_with_fin` gives the
  union of `K` with all the finite components in its complement.  -/
-- Possible enhancement: Using the `simple_graph` namesppace to allow for nice syntax
def extend_with_fin (G : simple_graph V) (Gpc : G.preconnected) (Glf : G.locally_finite) (k : finset V) (kn : k.nonempty) : finset V :=
begin
  let finite_pieces : set V := set.Union (λ c : {C : G.comp_out k // C.fin}, (c : set V)),
  have : finite_pieces.finite := by {
    haveI comps_fin : finite {C : G.comp_out k // C.fin} := fin_comp_out_finite G k Gpc Glf,
    haveI fin_comps : ∀ (c : {C : G.comp_out k // C.fin}), finite (↑c : set V) := by {
      rintro ⟨c, cfin⟩, dsimp [comp_out.fin] at *,
      rw ← set.finite_coe_iff at cfin, exact cfin,},
    rw ← set.finite_coe_iff,
    apply @finite.set.finite_Union _ _ comps_fin coe fin_comps,
  },
  exact k ∪ ‹finite_pieces.finite›.to_finset,
end

lemma extend_with_fin.def : ∀ x, x ∈ (extend_with_fin G Gpc Glf k kn) ↔ (x ∈ k) ∨ (∃ (c : G.comp_out k) (cfin : c.fin), x ∈ c) := sorry

lemma extend_with_fin.sub : k ⊆ extend_with_fin G Gpc Glf k kn :=
begin
  dsimp [extend_with_fin],
  exact subset_union_left k _,
end

lemma extend_with_fin.dis_iff_comp_inf {C : G.comp_out ↑(extend_with_fin G Gpc Glf k kn)} : C.dis ↔ C.inf :=
begin
  dsimp only [dis],
  split,
  { intros hdis hinf,
    apply hdis,
    sorry, -- every component is non-empty, so the point in the component will do
    sorry
  }, {
    rintros Cinf v ⟨hvextend, hvC⟩,
    show false, apply Cinf, clear Cinf,
    sorry -- it follows from cases on `hvextend` that `v` is contained in a finite component, and as components are disjoint, that must be `C` itself
  }
end

lemma extend_with_fin.inf_of_dis_extend {C : G.comp_out ↑k} : C.inf → disjoint (extend_with_fin G Gpc Glf k kn : set V) (C : set V) := sorry


lemma connected_of_all_adj {α : Type*} {k : finset V} (kconn : (G.induce ↑k).connected)
  {S : α → set V} {hS_fin : set.finite (set.Union S)} (hS_conn : ∀ {A : α},
  (G.induce (S A)).connected) : (∀ {A : α}, (∃ (ck : V × V), ck.1 ∈ S A ∧ ck.2 ∈ k ∧ G.adj ck.1 ck.2) ∨ (S A ⊆ ↑k)) →
    (G.induce ↑(k ∪ hS_fin.to_finset)).connected :=
begin
  intro h,
  rw connected_iff,
  split, {
    rintros vv ww,
    have hv := vv.prop, have hw := ww.prop,
    simp at hv hw,
    cases hv, cases hw,
    {
      sorry,
    }, {
      sorry,
    }, cases hw, {
      sorry,
    }, {
      sorry
    },
  },  {
    apply set.nonempty_coe_sort.mpr,
    apply set.nonempty.mono, rotate,
    rw [← set.nonempty_coe_sort],
    exact ((connected_iff _).mp kconn).2,
    simp, }
end


lemma extend_with_fin.connected (kconn : (G.induce ↑k).connected) :
  (G.induce ↑(extend_with_fin G Gpc Glf k kn)).connected :=
begin
  dsimp [extend_with_fin],
  apply connected_of_all_adj _ kconn,
  { rintro ⟨C, Cfin⟩, dsimp, exact connected C,},
  { rintro ⟨C, Cfin⟩,
    by_cases disjoint (k : set V) (C : set V),
    {left, apply @adj _ _ _ _ _,
      dsimp [coe_b, has_coe.coe],
      all_goals {assumption},},
    { right, dsimp,
      simp at h,
      rcases h with ⟨k_, hk_k, hk_C⟩,
      rw ← hk_C, simp, assumption, } },
end

lemma extend_with_fin.components_spec :
  ∀ (C : set V), (∃ D : (G.comp_out k), D.inf ∧  C = D) ↔ (∃ (D : G.comp_out (extend_with_fin G Gpc Glf k kn)), D.dis ∧ C = D) :=
begin
  intro C,
  split,
  { rintro ⟨D, Dinf, DC⟩,
    use D.lift (connected_component_mk _) (by {
      intros v w p hp, simp only [connected_component.eq], apply nonempty.intro,
      sorry -- this is just a "coercion" of the path `p`
    }),
    have Ddis := extend_with_fin.inf_of_dis_extend G Gpc Glf k kn Dinf,
    -- elaborate procedure to get rid of the `lift`
    revert D, intro D, refine D.ind _,
    intros v Dinf DC Ddis, simp only [connected_component.lift_mk],
    split,
    { intros w hw,
      simp only [set.inf_eq_inter, mem_inter_eq, mem_coe, set_like.mem_coe, mem_supp_iff, connected_component.eq] at hw,
      cases hw with hwextend hwpath,
      show false, apply Ddis,
      simp, split,
      apply hwextend,
      sorry, -- a path coercion
      },
    { ext, simp only [set_like.mem_coe, mem_supp_iff, connected_component.eq],
      split,
      {  sorry, -- (harder) path coercion
      },
      {sorry} -- "coercion" of the path
     }
  },
  { rintro ⟨D, Ddis, DC⟩,
    use D.back (extend_with_fin.sub _ _ _ _ _),
    split,
    { apply back_of_inf,
      rw [extend_with_fin.dis_iff_comp_inf] at Ddis,
      exact Ddis, },
    { rw DC,
      apply eq.symm,
      show (back _ D : set V) = ↑D,
      suffices : back _ D = D, from by sorry {rw [comp_out.eq_of_eq_set]},
      rw eq_back_iff_sub,
      simp only [coe_subset, finset.subset.refl], }}
end

lemma extend_connected_with_fin_bundled  :
  {k' : finset V | k ⊆ k'
                 ∧ (G.induce (k' : set V)).connected
                 ∧ ∀ C : (G.comp_out k'), C.dis → C.inf} :=
begin
  /- This lemma is a combination of previously stated facts bundled together -/
  have kn : k.nonempty, by {sorry {rw ←set.nonempty_coe_sort, rw connected_iff at Kc, exact Kc.2,}},
  sorry {use extend_with_fin G K,
  use extend_with_fin.sub G K,
  use extend_with_fin.finite Gpc Glf Kf Kn,
  use extend_with_fin.connected G K Kc,
  rintro C Cdis,
  obtain ⟨D,Dinf,e⟩ := (extend_with_fin.components_spec G K C).mpr ⟨C,Cdis,rfl⟩,
  unfold inf, rw e, exact Dinf,}
end

end extend

end misc

end comp_out


/-- The components outside `K` that are disjoint from `K`
  This is essentially all the components apart from the singleton connected components corresponding
  to elements of `K`.
 -/
def dis_comp_out := {C : G.comp_out K // disjoint K C}
instance dis_comp_out_comp_out (G : simple_graph V) (K : set V) :
  has_coe (G.dis_comp_out K) (G.comp_out K) := ⟨λ x, x.val⟩


-- Here can refine most of the constructions for `comp_out`
namespace dis_comp_out

variables {G}
variables {K}  {L : set V}

-- Maybe todo: all the lemmas about disjointness and stuff, but maybe unneeded here.
lemma dis (C : G.dis_comp_out K) : disjoint K C := C.prop

lemma of_empty_is_singleton (Gpc : G.preconnected) : ∀ C : (G.dis_comp_out ∅), (C : set V) = univ :=
begin
  rintro C,
  apply comp_out.of_empty_is_singleton Gpc,
end


section back

/-- Given a connected component outside a set `L`, `back` gives the unique component
  outside a smaller set `K` that the given component is contained in. -/
def back {K L : set V} (h : K ⊆ L) : G.dis_comp_out L →  G.dis_comp_out K :=
  set.maps_to.restrict (comp_out.back h) {C : G.comp_out L | C.dis} {C : G.comp_out K | C.dis}
    (comp_out.back_of_dis h)

@[simp]
lemma back_iff {K L : set V} (h : K ⊆ L) (C : G.dis_comp_out L) (D : G.dis_comp_out K) :
  C.back h = D ↔ (C.val.back h) = D.val := by
{ dsimp only [back,maps_to.restrict,subtype.map],simp only [subtype.val_eq_coe],
  have : D = ⟨D.val,D.prop⟩ := subtype.eq rfl,
  rw [this, subtype.mk_eq_mk],
  split,rintro e, exact e, rintro e, exact e,}

@[simp]
lemma back_refl_apply  (C : G.dis_comp_out K) : C.back (subset_refl K) = C :=
by {ext,dsimp only [back], dsimp, simp only [comp_out.back_refl_apply],}

@[simp]
lemma back_trans_apply {K L M : set V} (kl : K ⊆ L) (lm : L ⊆ M) (C : G.dis_comp_out M) :
  (C.back ‹L ⊆ M›).back ‹K ⊆ L› = C.back (‹K ⊆ L›.trans  ‹L ⊆ M›) :=
by {ext, dsimp only [back], dsimp, simp only [comp_out.back_trans_apply],}

lemma back_of_inf  {K L : set V} (h : K ⊆ L) (C : G.dis_comp_out L) (Cinf : C.val.inf) :
  (C.back h).val.inf := by {dsimp [back], apply comp_out.back_of_inf, exact Cinf,}

end back

/-- A component outside `K` is infinite if and only if it is in the range of
    all the `back` functions for each `L` containing `K` -/
lemma inf_iff_in_all_ranges  {K : finset V} (C : G.dis_comp_out K) :
  C.val.inf ↔ ∀ (L : finset V) (h : K ⊆ L), C ∈ set.range (@back _ G _ _ h) :=
begin
  rcases C with ⟨C,Cdis⟩,
  simp only [set.mem_range, back_iff, subtype.val_eq_coe],
  split,
  { rintro Cinf L h,
    obtain ⟨D,Ddis,rfl⟩ := comp_out.in_all_ranges_of_inf C Cinf h,
    use [D,Ddis],refl,},
  { rintro h',
    apply comp_out.inf_of_in_all_ranges,
    rintro L h,
    obtain ⟨⟨D,Ddis⟩,rfl⟩ := h' L h, use [D,Ddis], refl,}
end

end dis_comp_out

/-- The infinite connected components outside a given set `K` -/
def inf_comp_out := {C : G.dis_comp_out K // (C : G.comp_out K).inf}
instance inf_comp_out_dis_comp_out (G : simple_graph V) (K : set V) :
  has_coe (G.inf_comp_out K) (G.dis_comp_out K) := ⟨λ x, x.val⟩

-- Here can refine most of the constructions for `comp_out`
namespace inf_comp_out

variables {G} {K} {L : set V}

lemma of_empty_is_subsingleton (Gpc : G.preconnected) : subsingleton (G.inf_comp_out ∅) :=
begin
  constructor,
  rintro C D,
  ext,
  rw connected_component.eq_of_eq_supp,
  transitivity set.univ,
  apply comp_out.of_empty_is_singleton Gpc,
  symmetry,
  apply comp_out.of_empty_is_singleton Gpc,
end

-- probably follows from clever uses of `bij_on` and restriction to subtypes, but let's bruteforce
def equiv_of_iso {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) : G.inf_comp_out K ≃ G'.inf_comp_out (φ '' K) :=
begin
  fsplit,
  { rintro ⟨⟨C,Cdis⟩,Cinf⟩,
    use comp_out.equiv_of_iso φ K C,
    apply (comp_out.equiv_of_iso.dis φ K C).mp Cdis,
    apply (comp_out.equiv_of_iso.inf φ K C).mp Cinf,},
  { rintro ⟨⟨D,Ddis⟩,Dinf⟩,
    use (comp_out.equiv_of_iso φ K).symm D,
    let := (comp_out.equiv_of_iso.dis φ K (((comp_out.equiv_of_iso φ K).symm) D)),
    dsimp only [comp_out.dis] at this, rw this,
    rw equiv.apply_symm_apply (comp_out.equiv_of_iso φ K) D,
    exact Ddis,
    let := (comp_out.equiv_of_iso.inf φ K (((comp_out.equiv_of_iso φ K).symm) D)),
    dsimp only [comp_out.inf] at this ⊢, simp only [subtype.coe_mk], rw this,
    rw equiv.apply_symm_apply (comp_out.equiv_of_iso φ K) D,
    exact Dinf,}, -- very very ugly story
  { dsimp only [left_inverse],rintro ⟨⟨C,Cdis⟩,Cinf⟩, simp only [equiv.symm_apply_apply],  },
  { dsimp only [function.right_inverse, left_inverse],
    rintro ⟨⟨C,Cdis⟩,Cinf⟩, simp only [equiv.apply_symm_apply],  }


end

lemma equiv_of_iso.image {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) (C : G.inf_comp_out K) : (φ '' C) = (equiv_of_iso φ K C) :=
begin
  rcases C with ⟨⟨C,Cdis⟩,Cinf⟩,
  simp only [coe_coe, subtype.coe_mk],
  exact comp_out.equiv_of_iso.image φ K C,
end

def back {K L : set V} (h : K ⊆ L) : G.inf_comp_out L →  G.inf_comp_out K :=
  set.maps_to.restrict (dis_comp_out.back h) {C : G.dis_comp_out L | C.val.inf} {C : G.dis_comp_out K | C.val.inf}
    (dis_comp_out.back_of_inf h)

@[simp]
lemma back_iff {K L : set V} (h : K ⊆ L) (C : G.inf_comp_out L) (D : G.inf_comp_out K) :
  C.back h = D ↔ (C.val.back h) = D.val :=
begin
  rcases C with ⟨⟨C,Cdis⟩,Cinf⟩,
  rcases D with ⟨⟨D,Ddis⟩,Dinf⟩,
  dsimp only [back],
  rw [←subtype.coe_inj,set.maps_to.coe_restrict_apply],
  simp only [subtype.coe_mk],
end

lemma eq_back_iff_sub {K L : set V} (h : K ⊆ L) (C : G.inf_comp_out L) (D : G.inf_comp_out K) :
  C.back h = D ↔ (C : set V) ⊆ D :=
begin
  simp only [back_iff, subtype.val_eq_coe, dis_comp_out.back_iff, comp_out.eq_back_iff_sub, coe_coe],
end


lemma back_sub {K L : set V} (h : K ⊆ L) (C : G.inf_comp_out L)  :
  (C : set V) ⊆ C.back h :=
begin
  rw ←eq_back_iff_sub,
end

@[simp]
lemma back_refl_apply  (C : G.inf_comp_out K) : C.back (subset_refl K) = C :=
begin
  simp only [back_iff, dis_comp_out.back_refl_apply],
end

@[simp]
lemma back_trans_apply {K L M : set V} (kl : K ⊆ L) (lm : L ⊆ M) (C : G.inf_comp_out M) :
  (C.back ‹L ⊆ M›).back ‹K ⊆ L› = C.back (‹K ⊆ L›.trans  ‹L ⊆ M›) :=
begin
  rw back_iff,
  apply dis_comp_out.back_trans_apply,
end


lemma cofinite_to_equiv_unit (Glf : locally_finite G) (Gpc : G.preconnected) (K : set V)
  (D : set V) (Ddis : disjoint K D) (Dconn : (G.induce D).connected)
  (Dinf : D.infinite) (Dcof : (D ᶜ).finite ) :
  (G.inf_comp_out K) ≃ unit :=
begin
  let C := comp_out.of_connected_disjoint D Dconn Ddis,
  let Cinf := set.infinite.mono (comp_out.of_connected_disjoint_sub D Dconn Ddis) Dinf,
  haveI : unique (G.inf_comp_out K), by
  { use ⟨⟨C,comp_out.dis_of_inf C Cinf⟩,Cinf⟩,
    rintro ⟨⟨C',C'dis⟩,C'inf⟩,
    dsimp only [default],
    rw [subtype.mk_eq_mk,subtype.mk_eq_mk],
    apply comp_out.eq_of_not_disjoint,
    sorry, /-some tiring set "algebra" -/},
  apply equiv.equiv_punit,
end

end inf_comp_out

end simple_graph
