import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import combinatorics.simple_graph.prod
import .mathlib
import .reachable_outside
import .ends

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


variables  {V : Type u}
           (G : simple_graph V)
           {V' : Type v}
           (G' : simple_graph V')
           {V'' : Type w}
           (G'' : simple_graph V'')

namespace ends

open ro_component
open simple_graph

lemma ends_product [Vnempty : nonempty V] [Vnempty' : nonempty V']
  [locally_finite G] [locally_finite G']
  (Gpc :G.preconnected) (Gpc' : G'.preconnected)
  (Vinf : set.infinite (@set.univ V)) (V'inf : set.infinite (@set.univ V'))
: ends  (box_prod G  G') (simple_graph.preconnected.box_prod Gpc Gpc') ≃ true :=
begin

  let VV := V × V',
  let GG := G □ G',
  let GGpc := simple_graph.preconnected.box_prod Gpc Gpc',
  haveI : locally_finite GG, by sorry,
  haveI all_fin : ∀ K : finset VV, fintype (inf_ro_components GG K), from
     λ K, inf_components_finite' GG GGpc K,
  suffices : ∀ K : finset VV, (inf_ro_components GG K) ≃ true,
  {
    have all_inj : ∀ (K L : finset VV) (KL : K ⊆ L), injective (bwd_map GG GGpc KL), by
    { rintros K L KL,
      sorry, -- we have true ≃ inf_ro_components GG L → inf_ro_components GG K ≃ true
      -- this composes to a surjection, since all functions are, and thus to an injection, because
      -- all maps true -> true are injection, thus bwd is also an injection.
    },
    have lol := eval_bijective GG GGpc ∅ (λ L hL, all_inj ∅ L hL),
    exact (equiv.of_bijective _ lol).trans (this ∅),
  },

  rintros K,
  let L := finset.product (finset.image prod.fst K) (finset.image prod.snd K),
  have : K ⊆ L, from subset_product,
  let D := (L : set VV) ᶜ,
  have memD_iff : ∀ x : VV, x ∈ D ↔ x.1 ∉ (finset.image prod.fst K) ∨ x.2 ∉ (finset.image prod.snd K), by
  {
    rintro x,
    rw ←not_iff_not,
    push_neg,
    rw set.mem_compl_iff,
    simp,},
  have Ddis : disjoint D K, from disjoint_compl_left_iff.mpr (‹K⊆L›),
  have Dinf : D.infinite, by sorry, -- VV is infinite, L is finite, V\L is infinite.
  have Dconn : subconnected GG D, by {
    rintros ⟨x,x'⟩ xinD ⟨y,y'⟩ yinD,

    have :(∃ (z z': VV)
             (u : GG.walk ⟨x,x'⟩ z)
             (v : GG.walk z z')
             (w : GG.walk z' ⟨y,y'⟩),
             (u.support.to_finset : set VV) ⊆ D
           ∧ (v.support.to_finset : set VV) ⊆ D
           ∧ (w.support.to_finset : set VV) ⊆ D), by {

      have : ∀ x ∉ (finset.image prod.fst K),
             ∀ {y y' : V'} (w : G'.walk y y'), ((walk.box_prod_right G x w).support.to_finset : set VV) ⊆ D, by {
        rintros x xnotin y y' w,
        rw simple_graph.walk.support_box_prod_right,
        rw list.map_to_finset,
        rintro p q,
        simp at q,
        rcases q with ⟨v,⟨vin,rfl⟩⟩,
        apply (memD_iff ⟨x,v⟩).mpr,
        left, exact xnotin,},

      have : ∀ x ∉ (finset.image prod.snd K),
             ∀ {y y' : V} (w : G.walk y y'), ((walk.box_prod_left G' x w).support.to_finset : set VV) ⊆ D, by {
        rintros x xnotin y y' w,
        rw simple_graph.walk.support_box_prod_left,
        rw list.map_to_finset,
        rintro p q,
        simp at q,
        rcases q with ⟨v,⟨vin,rfl⟩⟩,
        apply (memD_iff ⟨v,x⟩).mpr,
        right, exact xnotin,},

      rcases (memD_iff ⟨x,x'⟩).mp xinD with xnot|xnot',
        { rcases (memD_iff ⟨y,y'⟩).mp yinD with ynot|ynot',
          {
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
  },
  -- If I do a `rcases … with ⟨C,Ccomp⟩` here I get elimination out of prop issues, why does this ↓ work?
  let C := (ro_component.of_subconnected_disjoint GG K D (set.infinite.nonempty Dinf) Ddis Dconn).some,
  obtain ⟨Ccomp,DC⟩ := (ro_component.of_subconnected_disjoint GG K D (set.infinite.nonempty Dinf) Ddis Dconn).some_spec,
  have Cinf := set.infinite.mono DC Dinf,
  suffices : ∀ C' ∈ inf_ro_components GG K, C' = C, {
    use [(λ _, trivial)
        ,(λ _, ⟨C,Ccomp,Cinf⟩)
        ,(λ lol,  subtype.coe_inj.mp ((this lol.val lol.prop).symm))
        ,(λ _, rfl)],},
  rintros C' ⟨Ccomp',Cinf'⟩,
  suffices : (C ∩ C').nonempty, {
    rcases this with ⟨x,xC,xC'⟩,
    apply eq_of_common_mem GG K C' C Ccomp' Ccomp x xC' xC},
  by_contradiction,
  have : C' ⊆ L, by {
    rw set.not_nonempty_iff_eq_empty at h,
    rw ←set.disjoint_iff_inter_eq_empty at h,
    have := @disjoint.mono_left _ _ _ D C C' DC h,
    rw ←set.disjoint_compl_right_iff_subset,
    exact this.symm,
  },
  exact Cinf' (set.finite.subset L.finite_to_set this),
end

end ends

end simple_graph
