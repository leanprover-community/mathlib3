import data.set.finite
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.prod
import .for_mathlib.misc
import .comp_out
import .ends
import .functoriality

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph

open simple_graph

variables  {V : Type u}
           (G : simple_graph V)
           (Gpc: G.preconnected)
           (Glf : locally_finite G)



section finite

/--
An finite graph has no ends.

Note that local finiteness follows from `finite V`
-/
lemma no_end_of_finite_graph [finite V] : (Ends G) ≃ empty :=
begin
  have Vfin : (@set.univ V).finite := set.finite_univ,
  transitivity,
  exact Ends_equiv_Endsinfty G,
  apply @equiv.equiv_empty _ _,
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  obtain ⟨⟨C,Ccomp⟩,Cinf⟩ := f (set.finite.to_finset Vfin),
  exact Cinf (set.finite.subset Vfin (set.subset_univ C)),
end

end finite


section infinite

include G Gpc Glf
/--
An infinite graph has at least one end.
-/
lemma end_of_infinite_graph [infinite V] : (Ends G).nonempty :=
begin
  haveI := ComplComp_fintype G Glf Gpc,
  haveI := ComplComp_nonempty G Glf Gpc,
  exact inverse_system.nonempty_sections_of_fintype_inverse_system' (ComplComp G),
end

end infinite


section nat

def gℕ : simple_graph ℕ := simple_graph.from_rel (λ n m, m = n.succ)

lemma gℕadjs : ∀m n, gℕ.adj m n ↔ (n = m+1 ∨ m = n+1) := by
{ rintro m n, split,
 { rintro ⟨ne,rfl|rfl⟩,
   { left,refl, },
   { right,refl, },},
   rintro (rfl|rfl),
   { split, exact (nat.succ_ne_self m).symm, left, dsimp only, refl, },
   { split, exact (nat.succ_ne_self n), right, dsimp only, refl, },}


lemma gℕlf : locally_finite gℕ :=
begin
  dsimp [locally_finite,neighbor_set,adj],
  rintro n,
  refine (set.finite.subset {m | m ≤ n+1}.to_finite _).fintype,
  rintro m ⟨ne,rfl|rfl⟩,
  simp only [mem_set_of_eq],
  simp only [mem_set_of_eq],
  exact le_trans (nat.le_succ m) (nat.le_succ m.succ),
end

lemma gℕpc : gℕ.preconnected :=
begin
  suffices : ∀ n : ℕ, gℕ.reachable n 0,
  { rintro m n, transitivity 0, exact this m, symmetry, exact this n, },
  rintro n, induction n,
  { reflexivity, },
  transitivity n_n, rotate, exact n_ih,
  constructor, refine walk.cons _ nil,
  rw gℕadjs, right, refl,
end
lemma gℕc : gℕ.connected := by {rw connected_iff, use gℕpc, use nonempty_of_inhabited,}


lemma gt_iso (m : ℕ) : gℕ ≃g (gℕ.induce {n : ℕ | n > m}) :=
begin
  use (λ n, ⟨n+m+1, by {simp only [gt_iff_lt, mem_set_of_eq],rw [add_comm n m,add_assoc],
  apply nat.lt_add_of_zero_lt_left, simp only [nat.succ_pos'],} ⟩),
  use (λ ⟨n,nm⟩, n-m-1) ,
  { rintro x, simp only,
    rw nat.succ_sub,
    simp only [add_tsub_cancel_right, nat.succ_sub_succ_eq_sub, tsub_zero],
    simp only [le_add_iff_nonneg_left, zero_le'], },
  { rintro ⟨x,xm⟩,
    simp only [subtype.mk_eq_mk],
    rw nat.sub_sub,
    rw add_assoc,
    rw nat.sub_add_cancel,
    rw nat.succ_le_iff, exact xm, },
  { rintro u v,
    simp only [equiv.coe_fn_mk, comap_adj, embedding.coe_subtype, subtype.coe_mk],
    split,
    { rintro ⟨ne,l|r⟩,
      split, simpa only [_root_.ne.def, add_left_inj] using ne,
      left, rw [←nat.succ_add,←nat.succ_add] at l,
      simpa only [add_left_inj] using l,
      split, simpa only [_root_.ne.def, add_left_inj] using ne,
      right, rw [←nat.succ_add,←nat.succ_add] at r,
      simpa only [add_left_inj] using r,},
    { rintro ⟨ne,rfl|rfl⟩,
      split, simpa only [_root_.ne.def, add_left_inj] using ne,
      left, rw [nat.succ_add,nat.succ_add],
      split, simpa only [_root_.ne.def, add_left_inj] using ne,
      right, rw [nat.succ_add,nat.succ_add],},}
end

lemma gt_connected (m : ℕ) : (gℕ.induce {n : ℕ | n > m}).connected := (iso.connected (gt_iso m)).mp gℕc

/--
The Cayley graph of the natural numbers wrt generator set `1` is one-ended.
-/
lemma ends_nat : (Ends gℕ) ≃ unit :=
begin

  suffices H : ∀ K : finset ℕ, ∃ D : set ℕ, disjoint (K : set ℕ) D ∧ (gℕ.induce D).connected ∧ D.infinite ∧ (D ᶜ).finite,
  { obtain ⟨dis,conn,inf,cof⟩ := (H ∅).some_spec,
    have : (ComplInfComp gℕ).obj ∅ ≃ unit, from
    inf_comp_out.cofinite_to_equiv_unit gℕlf gℕpc ∅ _ dis conn inf cof,
    transitivity, exact (Ends_equiv_Endsinfty gℕ),
    transitivity, rotate, exact this,

    apply Endsinfty_eventually_constant gℕ gℕlf gℕpc ∅,
    rintro L LL,
    transitivity, rotate, exact this.symm,
    obtain ⟨dis,conn,inf,cof⟩ := (H L).some_spec,
    exact inf_comp_out.cofinite_to_equiv_unit gℕlf gℕpc L _ dis conn inf cof, },


  intro K,
  have : ∃ m : ℕ, ∀ k ∈ K, m ≥ k, by
  { by_cases h : K.nonempty,
    { let m := K.max,
      rcases finset.max_of_nonempty h with ⟨a,e⟩,
      use a,
      rintro k kK,
      simp only [ge_iff_le],
      exact le_max_of_mem kK e,},
    { use 0, rintro k kK, exfalso,
      simp only [finset.not_nonempty_iff_eq_empty] at h,
      rw h at kK,
      simp only [finset.not_mem_empty] at kK,
      exact kK,},},

  rcases this with ⟨m,mtop⟩,
  let L := {n : ℕ | n > m },
  have Ldis : disjoint L K, by
  { rintro x ⟨xL,xK⟩,
    simp only [mem_set_of_eq, gt_iff_lt] at xL,
    specialize mtop x xK,
    exact (not_le_of_lt xL) mtop, },
  have Lcof : (L ᶜ).finite, by
  { dsimp only [compl,boolean_algebra.compl,boolean_algebra.core.compl],
    simp only [mem_set_of_eq, not_lt],
    apply set.finite_le_nat },
  -- There is no set.infinite_gt_nat ??
  have Linf : L.infinite, by {apply set.infinite_of_finite_compl Lcof,},
  have Lconn := gt_connected m,

  use [L,Ldis.symm,Lconn,Linf,Lcof],
end

end nat


section product

variables  {V' : Type v}
           (G' : simple_graph V')
           (Gpc': G'.preconnected)
           (Glf' : locally_finite G')


/--
If both `G` and `G'` are infinite connected graphs, then removing a finite box
from their product leaves the rest connected.
-/
private lemma finprod_compl_connected
  [infinite V] [infinite V']
  (K : finset V) (K' : finset V') :
  ((G □ G').induce (finset.product K K' : set (V × V') )ᶜ).connected :=
begin

  let VV := V × V',
  let GG := G □ G',
  let L := finset.product K K',
  let D := (L :set (V × V')) ᶜ,

  have memD_iff : ∀ x : VV, x ∈ D ↔ x.1 ∉ K ∨ x.2 ∉ K', by
  { rintro x,
    rw ←not_iff_not,
    push_neg,
    rw set.mem_compl_iff,
    simp,},

  -- V is infinite, K is finite
  let k : V, by sorry,
  let kK : k ∉ K, by sorry,
  let k' : V', by sorry,
  let kK' : k' ∉ K', by sorry,

  rw connected_iff, split, rotate,
  -- nonempty below
  { constructor, fconstructor,
    exact ⟨k,k'⟩,
    simp only [coe_product, mem_compl_eq, prod_mk_mem_set_prod_eq,
               mem_coe, not_and],
    rintro, use kK',},

  -- now connected
  rintros ⟨⟨x,x'⟩,xinD⟩ ⟨⟨y,y'⟩,yinD⟩,

  have : (∃ (z z': VV)
          (u : GG.walk ⟨x,x'⟩ z)
          (v : GG.walk z z')
          (w : GG.walk z' ⟨y,y'⟩),
          (u.support.to_finset : set VV) ⊆ D
        ∧ (v.support.to_finset : set VV) ⊆ D
        ∧ (w.support.to_finset : set VV) ⊆ D), by
  { have : ∀ x ∉ K,
            ∀ {y y' : V'} (w : G'.walk y y'), ((walk.box_prod_right G x w).support.to_finset : set VV) ⊆ D, by {
      rintros x xnotin y y' w,
      rw [simple_graph.walk.support_box_prod_right,list.map_to_finset],
      rintro p q,
      simp only [coe_image, set.mem_image, mem_coe, list.mem_to_finset] at q,
      rcases q with ⟨v,⟨vin,rfl⟩⟩,
      apply (memD_iff ⟨x,v⟩).mpr,
      left, exact xnotin,},

    have : ∀ x ∉ K',
            ∀ {y y' : V} (w : G.walk y y'), ((walk.box_prod_left G' x w).support.to_finset : set VV) ⊆ D, by
    { rintros x xnotin y y' w,
      rw [simple_graph.walk.support_box_prod_left,list.map_to_finset],
      rintro p q,
      simp only [coe_image, set.mem_image, mem_coe, list.mem_to_finset] at q,
      rcases q with ⟨v,⟨vin,rfl⟩⟩,
      apply (memD_iff ⟨v,x⟩).mpr,
      right, exact xnotin,},

    rcases (memD_iff ⟨x,x'⟩).mp xinD with xnot|xnot',
    { rcases (memD_iff ⟨y,y'⟩).mp yinD with ynot|ynot',
      { -- pffh too much woooork
        -- we need in some cases to make use of k or k' defined above.
        -- That's why we need a concatenation of three paths and not just two.
        sorry,
      },
      { sorry },
    },
    { rcases (memD_iff ⟨y,y'⟩).mp yinD with ynot|ynot',
      { sorry },
      { sorry },
    }

  },

  rcases this with ⟨z,z',u,v,w,uD,vD,wD⟩,
  let uvw := (u.append v).append w,
  have uvwD : (uvw.support.to_finset : set VV) ⊆ D, by
  { simp only [walk.support_append, uD, list.to_finset_append, coe_union, set.union_subset_iff,
               true_and],
    split,
    apply subset.trans _ vD, simp only [coe_subset, list.to_finset_tail],
    apply subset.trans _ wD, simp only [coe_subset, list.to_finset_tail], },
  constructor,
  fapply walk.to_induced, exact uvw,
  rintro a as,
  have : a ∈ (uvw.support.to_finset : set VV), by
  { rw finset.mem_coe, rw list.mem_to_finset, exact as, },
  apply mem_of_mem_of_subset this uvwD,
end

include Glf Glf'
lemma GGlf : locally_finite (G □ G') := by
{
  rintro ⟨g,g'⟩,
  have : (G □ G').neighbor_set ⟨g,g'⟩ =
    ((λ x, (⟨x,g'⟩ : V × V')) '' (G.neighbor_set g)) ∪
    ((λ x', (⟨g,x'⟩ : V × V')) '' (G'.neighbor_set g')), by
  { ext ⟨x,x'⟩,
    simp only [mem_neighbor_set, box_prod_adj, mem_union_eq, set.mem_image, prod.mk.inj_iff,
               exists_eq_right_right],
    simp_rw and_comm _ (g' = x'),
    simp only [exists_eq_right_right],tauto,},
  rw this,
  apply set.finite.fintype,
  apply set.finite.union;
  apply set.finite.image;
  apply set.finite.intro,
  exact Glf g,
  exact Glf' g',
}

include Gpc Gpc'
lemma ends_product [infinite V] [infinite V'] : Ends  (G □ G') ≃ unit :=
begin

  let VV := V × V',
  let GG := G □ G',
  let GGpc := simple_graph.preconnected.box_prod Gpc Gpc',
  let GGlf' := (GGlf G Glf G' Glf'),

  suffices H : ∀ K : finset VV, ∃ D : set VV, disjoint (K : set VV) D ∧ (GG.induce D).connected ∧ D.infinite ∧ (D ᶜ).finite,
  { obtain ⟨dis,conn,inf,cof⟩ := (H ∅).some_spec,
    have : (ComplInfComp GG).obj ∅ ≃ unit, from
    inf_comp_out.cofinite_to_equiv_unit GGlf' GGpc ∅ _ dis conn inf cof,
    transitivity, exact (Ends_equiv_Endsinfty GG),
    transitivity, rotate, exact this,

    apply Endsinfty_eventually_constant GG GGlf' GGpc ∅,
    rintro L LL,
    transitivity, rotate, exact this.symm,
    obtain ⟨dis,conn,inf,cof⟩ := (H L).some_spec,
    exact inf_comp_out.cofinite_to_equiv_unit GGlf' GGpc L _ dis conn inf cof, },


  rintros K,
  let L := finset.product (finset.image prod.fst K) (finset.image prod.snd K),
  have : K ⊆ L, from subset_product,
  let D := (L : set VV) ᶜ,
  have Dcof : (D ᶜ).finite, by
  { have : D ᶜ = L, by {simp},
    rw this, exact L.finite_to_set,},
  have Ddis : disjoint D K, from disjoint_compl_left_iff.mpr (‹K⊆L›),
  have Dinf : D.infinite, by {apply set.infinite_of_finite_compl,exact Dcof, },
  have Dconn : (GG.induce D).connected,
    from finprod_compl_connected G G' _ _,

  use [D,Ddis.symm,Dconn,Dinf,Dcof],
end

end product


section quasi_isometry

variables  {V' : Type v}
           (G' : simple_graph V')
           (Gpc': G'.preconnected)
           (Glf' : locally_finite G')


include Glf Gpc
lemma cofinite_of_coarse_Lipschitz_inv (φ : V → V') (ψ : V' → V) (m : ℕ) (mge : m ≥ 1)
  (φψ : ∀ (v : V), G.dist (ψ $ φ v) v ≤ m)
  (φl : coarse_Lipschitz G G' φ m) (ψl : coarse_Lipschitz G' G ψ m) : cofinite φ :=
begin
  have : ∀ v : V, {u | G.dist v u ≤ m}.finite := λ v, simple_graph.finite_balls G Gpc Glf v m,
  rintro x,
  dsimp only [set.preimage],
  simp only [mem_singleton_iff],
  fapply set.finite.subset (this (ψ x)),
  rintro y φyx, simp only [mem_set_of_eq] at φyx,
  rcases φyx with rfl,
  exact (φψ y),
end

include Gpc' Glf'
lemma qi_invariance (φ : V → V') (ψ : V' → V) (m : ℕ) (mge : m ≥ 1)
  (φψ : ∀ (v : V), G.dist (ψ $ φ v) v ≤ m) (ψφ : ∀ (v : V'), G'.dist (φ $ ψ v) v ≤ m)
  (φl : coarse_Lipschitz G G' φ m) (ψl : coarse_Lipschitz G' G ψ m) :
  Endsinfty G ≃ Endsinfty G' :=
begin
  haveI : locally_finite G := Glf,
  have mmm : m ≤ m*m, by {exact nat.le_mul_self m,},
  have φcof : cofinite φ := cofinite_of_coarse_Lipschitz_inv G Gpc Glf G' φ ψ m mge φψ φl ψl,
  have ψcof : cofinite ψ := cofinite_of_coarse_Lipschitz_inv G' Gpc' Glf' G ψ φ m mge ψφ ψl φl,
  have φc := coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' φ m φl φcof,
  have ψc := coarse.of_coarse_Lipschitz_of_cofinite G' G Gpc ψ m ψl ψcof,
  have φψcl : coarse_close G' G' (φ ∘ ψ) id, by
  { apply coarse_close.of_close_of_coarse_Lipschitz_of_cofinite G' Gpc' G' Gpc' (φ∘ψ) id (m*m),
    { apply coarse_Lipschitz.comp, exact ψl, exact φl, },
    { apply coarse_Lipschitz.id G' (m*m) (mge.le.trans mmm), },
    { apply cofinite.comp ψcof φcof,},
    { apply cofinite.id, },
    { rintro v, apply (ψφ v).trans mmm,}, },
  have ψφcl : coarse_close G G (ψ ∘ φ) id := by
  { apply coarse_close.of_close_of_coarse_Lipschitz_of_cofinite G Gpc G Gpc (ψ∘φ) id (m*m),
    { apply coarse_Lipschitz.comp, exact φl, exact ψl, },
    { apply coarse_Lipschitz.id G (m*m) (mge.le.trans mmm), },
    { apply cofinite.comp φcof ψcof,},
    { apply cofinite.id, },
    { rintro v, apply (φψ v).trans mmm,}, },
  fsplit,
  exact coarse.Endsinfty G G' φc,
  exact coarse.Endsinfty G' G ψc,
  { rintro e,
    rw [←coarse.Endsinfty_comp_apply,
        coarse_close.Endsinfty.eq' G G ψφcl (coarse.comp G G' G φc ψc) (coarse.id G),
        coarse.Endsinfty_id_apply],},
  { rintro e,
    rw [←coarse.Endsinfty_comp_apply,
        coarse_close.Endsinfty.eq' G' G' φψcl (coarse.comp G' G G' ψc φc) (coarse.id G'),
        coarse.Endsinfty_id_apply],},
end



end quasi_isometry


end simple_graph
