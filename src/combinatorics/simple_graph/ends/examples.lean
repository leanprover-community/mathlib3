import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import combinatorics.simple_graph.prod
import .mathlib
import .comp_out
import .end_limit_construction
--import .functoriality

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


namespace ends

open simple_graph

variables  {V : Type u}
           (G : simple_graph V)
           (Gpc: G.preconnected)
           (Glf : locally_finite G)



section finite


-- Locally_finite follows from finiteness
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
lemma end_of_infinite_graph [infinite V] : (Ends G).nonempty :=
begin
  haveI := ComplComp_fintype G Glf Gpc,
  haveI := ComplComp_nonempty G Glf Gpc,
  exact inverse_system.nonempty_sections_of_fintype_inverse_system' (ComplComp G),
end

end infinite


section nat

def gℕ : simple_graph ℕ := simple_graph.from_rel (λ n m, m = n.succ)

lemma gℕlf : locally_finite gℕ := sorry
lemma gℕpc : gℕ.preconnected := sorry
lemma gℕc : gℕ.connected := sorry


lemma gt_iso (m : ℕ) : gℕ ≃g (gℕ.induce {n : ℕ | n > m}) :=
begin
  use (λ n, ⟨n+m+1,sorry⟩),
  use (λ ⟨n,nm⟩, n-m-1),
  sorry, sorry,
  rintro a b, simp,
  sorry,
end

lemma gt_connected (m : ℕ) : (gℕ.induce {n : ℕ | n > m}).connected := (iso.connected (gt_iso m)).mp gℕc


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
      simp,
      exact le_max_of_mem kK e,},
    {use 0,rintro k kK,exfalso, simp at h, rw h at kK,simp at kK, exact kK,},},

  rcases this with ⟨m,mtop⟩,
  let L := {n : ℕ | n > m },
  have Ldis : disjoint L K, by { rw set.disjoint_iff, rintro x ⟨xL,xK⟩, simp at xL, simp, specialize mtop x xK, simp at mtop, exact (not_le_of_lt xL) mtop, },
  have Lcof : (L ᶜ).finite, by {dsimp [compl,boolean_algebra.compl],simp, apply set.finite_le_nat},
  -- There is no set.infinite_gt_nat ??
  have Linf : L.infinite, by {apply set.infinite_of_finite_compl,exact Lcof, },
  have Lconn := gt_connected m,

  use [L,Ldis.symm,Lconn,Linf,Lcof],
end

end nat


section product

variables  {V' : Type v}
           (G' : simple_graph V')
           (Gpc': G'.preconnected)
           (Glf' : locally_finite G')



private lemma finprod_compl_connected
  [infinite V] [infinite V']
  (K : finset V) (K' : finset V') :
  ((G □ G').induce (finset.product K K' : set (V × V') )ᶜ).connected :=
begin
  /-
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

  rintros ⟨x,x'⟩ xinD ⟨y,y'⟩ yinD,

  have :(∃ (z z': VV)
          (u : GG.walk ⟨x,x'⟩ z)
          (v : GG.walk z z')
          (w : GG.walk z' ⟨y,y'⟩),
          (u.support.to_finset : set VV) ⊆ D
        ∧ (v.support.to_finset : set VV) ⊆ D
        ∧ (w.support.to_finset : set VV) ⊆ D), by
  { have : ∀ x ∉ K,
            ∀ {y y' : V'} (w : G'.walk y y'), ((walk.box_prod_right G x w).support.to_finset : set VV) ⊆ D, by {
      rintros x xnotin y y' w,
      rw simple_graph.walk.support_box_prod_right,
      rw list.map_to_finset,
      rintro p q,
      simp at q,
      rcases q with ⟨v,⟨vin,rfl⟩⟩,
      apply (memD_iff ⟨x,v⟩).mpr,
      left, exact xnotin,},

    have : ∀ x ∉ K',
            ∀ {y y' : V} (w : G.walk y y'), ((walk.box_prod_left G' x w).support.to_finset : set VV) ⊆ D, by
    { rintros x xnotin y y' w,
      rw simple_graph.walk.support_box_prod_left,
      rw list.map_to_finset,
      rintro p q,
      simp at q,
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
  use (u.append v).append w,
  rw [walk.support_append,list.to_finset_append,walk.support_append,list.to_finset_append],
  rw [finset.coe_union,finset.coe_union],

  have vD' := set.subset.trans (list.to_finset_tail v.support) vD,
  have wD' := set.subset.trans (list.to_finset_tail w.support) wD,
  exact set.union_subset (set.union_subset uD vD') wD',
  -/
  sorry
end

instance GGlf : locally_finite (G □ G') := by sorry

include Gpc Gpc'
lemma ends_product [infinite V] [infinite V'] : Ends  (G □ G') ≃ unit :=
begin

  let VV := V × V',
  let GG := G □ G',
  let GGpc := simple_graph.preconnected.box_prod Gpc Gpc',
  let GGlf : locally_finite (G □ G') := sorry,

  suffices H : ∀ K : finset VV, ∃ D : set VV, disjoint (K : set VV) D ∧ (GG.induce D).connected ∧ D.infinite ∧ (D ᶜ).finite,
  { obtain ⟨dis,conn,inf,cof⟩ := (H ∅).some_spec,
    have : (ComplInfComp GG).obj ∅ ≃ unit, from
    inf_comp_out.cofinite_to_equiv_unit GGlf GGpc ∅ _ dis conn inf cof,
    transitivity, exact (Ends_equiv_Endsinfty GG),
    transitivity, rotate, exact this,

    apply Endsinfty_eventually_constant GG GGlf GGpc ∅,
    rintro L LL,
    transitivity, rotate, exact this.symm,
    obtain ⟨dis,conn,inf,cof⟩ := (H L).some_spec,
    exact inf_comp_out.cofinite_to_equiv_unit GGlf GGpc L _ dis conn inf cof, },


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

/-
lemma qi_invariance (φ : V → V') (ψ : V' → V) (m : ℕ)
  (φψ : ∀ (v : V), G.dist (ψ $ φ v) v ≤ m) (ψφ : ∀ (v : V'), G'.dist (φ $ ψ v) v ≤ m)
  (φl : coarse_Lipschitz G G' φ m) (ψl : coarse_Lipschitz G' G ψ m) :
  Endsinfty G Gpc ≃ Endsinfty G' Gpc' := sorry
-- First step: ψ and φ are cofinite :
-- Then everything should follow from `.functoriality.lean`
-/


end quasi_isometry


end ends


end simple_graph
