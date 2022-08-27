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

--mathlib
@[reducible, simp] def connected_component.supp {G : simple_graph V} (C : G.connected_component) :=
  {v : V | connected_component_mk G v = C}

--mathlib
@[ext] lemma connected_component.eq_of_eq_supp (C D : G.connected_component) : C = D ↔ C.supp = D.supp :=
begin
  split,
  { intro h, subst h, },
  { refine connected_component.ind₂ _ C D,
    intros v w h,
    simp_rw [set.ext_iff] at h,
    apply (h v).mp, dsimp [connected_component.supp],
    refl,}
end

--mathlib
instance : set_like G.connected_component V := {
  coe := connected_component.supp,
  coe_injective' := by {intros C D, apply (connected_component.eq_of_eq_supp _ _ _).mpr, } }

-- Some variation of this should surely be included in mathlib ?!
--mathlib
lemma connected_component.connected (C : G.connected_component) :
(G.induce C.supp).connected :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v,
  let comp := (G.connected_component_mk v).supp,
  rw connected_iff,
  fsplit,
  { suffices : ∀ u : comp, (G.induce comp).reachable u ⟨v, by {dsimp [comp], refl,}⟩,
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
  { simp [connected_component.supp], use v, }
end

-- mathlib
def connected_component.equiv_of_iso {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'}
  (φ : G ≃g G') : G.connected_component ≃ G'.connected_component :=
begin
  fsplit,
  { fapply connected_component.lift,
    { rintro v, exact connected_component_mk G' (φ v),},
    { rintro v w p pp, simp only [connected_component.eq], constructor, exact p.map φ.to_hom,}},

  { fapply connected_component.lift,
    { rintro v, exact connected_component_mk G (φ.symm v),},
    { rintro v w p pp, simp only [connected_component.eq], constructor, exact p.map φ.symm.to_hom,}},
  { dsimp only [function.right_inverse,function.left_inverse],
    apply connected_component.ind,
    simp only [connected_component.eq, connected_component.lift_mk, rel_iso.symm_apply_apply],
    rintro v, refl},
  { dsimp only [function.right_inverse,function.left_inverse],
    apply connected_component.ind,
    simp only [connected_component.eq, connected_component.lift_mk, rel_iso.symm_apply_apply],
    rintro v, simp only [rel_iso.apply_symm_apply], }
end

def out : simple_graph V := {
  adj := λ u v, u ∉ K ∧ v ∉ K ∧ G.adj u v,
  symm := by {rintro u v a, tauto, },
  loopless := by {rintro u a, exact G.loopless u a.2.2,}}

lemma out.sub (G : simple_graph V)  (K : set V) : out G K ≤ G := λ u v a, a.2.2

lemma out.mono (G : simple_graph V)  (K L : set V) (h : K ⊆ L) : G.out L ≤ G.out K :=
λ u v ⟨unL,vnL,uav⟩, ⟨(λ uK, unL (h uK)), (λ vK, (vnL (h vK))), uav⟩

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


lemma out.reachable_mono (G : simple_graph V)  (K L : set V) (h : K ⊆ L) (u v : V) :
  (G.out L).reachable u v → (G.out K).reachable u v :=
begin
  rw [reachable_iff_refl_trans_gen,reachable_iff_refl_trans_gen],
  apply refl_trans_gen.mono,
  apply out.mono,
  exact h,
end

lemma out.empty (G : simple_graph V) : G.out ∅ = G := by {ext, obviously,}


@[reducible] def comp_out := (G.out K).connected_component

@[simp] lemma comp_out.mem_supp_iff {G : simple_graph V} {K : set V}
  {v : V} {C : comp_out G K} :
(v ∈ C) ↔ connected_component_mk (out G K) v = C := by {refl,}

namespace comp_out

variables {G}
variables {K}  {L : set V} {KL : K ⊆ L}

@[reducible]
def inf (C : G.comp_out K) := (C : set V).infinite

@[reducible]
def fin (C : G.comp_out K) := (C : set V).finite

@[reducible]
def dis (C : G.comp_out K) := disjoint K (C : set V)


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

lemma exists_inf [infinite V] (G : simple_graph V) (K : set V)  (Gpc : G.preconnected)
  (Glf : G.locally_finite) (Kf : K.finite) (Kn : K.nonempty) : ∃ C : G.comp_out K, C.inf :=
begin
  by_contra h, push_neg at h,
  have : set.univ = ⋃ (C : G.comp_out K), (C : set V), by {
    symmetry,
    rw set.eq_univ_iff_forall, rintro x, use of_vertex G K x,
    simp only [of_vertex, mem_range_self, set_like.mem_coe, mem_supp_iff, true_and],},
  have : (@set.univ V).finite, by {
    rw this,
    haveI : finite (G.comp_out K), by apply comp_out_finite G K Gpc Glf Kf Kn,
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

lemma in_all_ranges_of_inf (Kfin : K.finite) (C : G.comp_out K) (Cinf : C.inf)
  {L : set V} (Lfin : L.finite) (h : K ⊆ L) :
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

lemma inf_of_in_all_ranges (Kfin : K.finite) (C : G.comp_out K)
  (mem_ranges : ∀ {L : set V} (Lfin : L.finite) (h : K ⊆ L), ∃ (D : G.comp_out L), D.dis ∧  D.back h = C) : C.inf :=
begin
  rintro Cfin,
  let L := K ∪ C,
  have Lfin : L.finite := set.finite.union Kfin Cfin,
  have : K ⊆ L := set.subset_union_left K C,
  obtain ⟨D,dis,e⟩ := mem_ranges Lfin ‹K⊆L›,
  simp only [eq_back_iff_sub] at e,
  suffices : (D : set V) = ∅, { have : (D : set V).nonempty, by simp only [nempty], finish,},
  have : disjoint (C : set V) D := disjoint.mono_left (set.subset_union_right K C) dis,
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

lemma equiv_of_isom.image{V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
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

lemma equiv_of_isom.dis {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) (C : G.comp_out K) : C.dis ↔ (equiv_of_iso φ K C).dis :=
begin
  dsimp only [dis],
  simp only [←equiv_of_isom.image],
  symmetry,
  apply disjoint_image_iff,
  exact rel_iso.injective φ,
end

lemma equiv_of_isom.inf {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
 (K : set V) (C : G.comp_out K) : C.inf ↔ (equiv_of_iso φ K C).inf :=
begin
  dsimp only [inf],
  simp only [←equiv_of_isom.image],
  symmetry,
  apply infinite_image_iff,
  refine injective.inj_on _ ↑C,
  exact rel_iso.injective φ,
end



-- Possible enhancement: Using the `simple_graph` namesppace to allow for nice syntax
def extend_with_fin (G : simple_graph V) (K : set V) : set V := K ∪ (⋃ (C : G.comp_out K) (h : C.fin), (C : set V))

lemma extend_with_fin.eq (G : simple_graph V) (K : set V) : G.comp_out (extend_with_fin G K) = (G.out K).comp_out (⋃ (C : G.comp_out K) (h : C.fin), (C : set V)) :=
begin
  dsimp [extend_with_fin, comp_out],
  sorry -- maybe it should be an isomorphism
end


lemma extend_with_fin.finite (Gpc : G.preconnected) (Glf : G.locally_finite) (Kf : K.finite) (Kn : K.nonempty):
  (extend_with_fin G K).finite :=
begin
  apply set.finite.union Kf,
  haveI : finite (G.comp_out K), by apply comp_out_finite G K Gpc Glf Kf Kn,
  apply set.finite_Union,
  rintro C,
  apply set.finite_Union, exact id,
end

lemma extend_with_fin.sub (G : simple_graph V) (K : set V) : K ⊆ extend_with_fin G K := by
{ dsimp [extend_with_fin],exact subset_union_left K (⋃ (C : comp_out G K) (h : C.fin), ↑C), }

lemma extend_with_fin.connected (G : simple_graph V) (K : set V) (Kconn : (G.induce K).connected) :
  (G.induce (extend_with_fin G K)).connected :=
begin
  dsimp [extend_with_fin],
  sorry,
end

lemma extend_with_fin.components_spec (G : simple_graph V) (K : set V) :
  ∀ (C : set V), (∃ D : (G.comp_out K), D.inf ∧  C = D) ↔ (∃ (D : G.comp_out (extend_with_fin G K)), C = D) := sorry

-- A restatement of the above lemma
lemma extends_with_fin.inf_components_iso (G : simple_graph V) (K : set V) :
  subtype (@comp_out.inf V G K) ≃ G.comp_out (extend_with_fin G K) := {
  to_fun := λ ⟨C, Cinf⟩, C.lift (λ v, connected_component_mk _ v) (by {
    intros v w p hpath,
    simp, apply nonempty.intro,
    sorry, -- the path is exactly `p`
  }),
  inv_fun := λ C, ⟨C.back (extend_with_fin.sub _ _), by {
    apply infinite.mono,
    apply back_sub,
    intro Cfin,
    sorry,
  }⟩,
  left_inv := by {
    simp [left_inverse],
    refine connected_component.ind _,
    intros v hinf w,
    simp,
    sorry, -- this can be stated as a general lemma for any set and its superset
  },
  right_inv := by {
    simp [function.right_inverse, left_inverse],
    refine connected_component.ind _,
    intro v, sorry,
  }}

end misc

end comp_out


def dis_comp_out := {C : G.comp_out K // disjoint K C}
instance dis_comp_out_comp_out (G : simple_graph V) (K : set V) :
  has_coe (G.dis_comp_out K) (G.comp_out K) := ⟨λ x, x.val⟩

-- Here can refine most of the constructions for `comp_out`
namespace dis_comp_out

variables {G}
variables {K}  {L : set V}

-- Maybe todo: all the lemmas about disjointness and stuff, but maybe unneeded here.
lemma dis (C : G.dis_comp_out K) : disjoint K C := C.prop

section back

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

end back

end dis_comp_out

def inf_comp_out := {C : G.dis_comp_out K // (C : G.comp_out K).inf}
instance inf_comp_out_dis_comp_out (G : simple_graph V) (K : set V) :
  has_coe (G.inf_comp_out K) (G.dis_comp_out K) := ⟨λ x, x.val⟩

-- Here can refine most of the constructions for `comp_out`
namespace inf_comp_out

-- todo: define `back` once again similarly as above, plus properties.


end inf_comp_out

end simple_graph
