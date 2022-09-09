import data.set.finite
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import data.setoid.partition

import .for_mathlib.misc
import .comp_out
import .for_mathlib.fintype_inverse_systems
import .ends
import .for_mathlib.connected


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
           (Glf : locally_finite G)
           (Gpc : preconnected G)


namespace comp_out

include Glf Gpc
lemma nicely_arranged (H K : set V) (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E E' : G.comp_out H) (Einf : E.inf) (Einf' : E'.inf) (En : E ≠ E')
  (F : G.comp_out K) (Finf : F.inf)
  (H_F : (H : set V) ⊆ F)
  (K_E : (K : set V) ⊆ E) : (E' : set V) ⊆ F :=
begin
  by_cases KE' : (K ∩ E').nonempty,
  { rcases KE' with ⟨v,v_in⟩,
    have vE' : v ∈ E', from ((set.mem_inter_iff v K E').mp v_in).right,
    have vE : v ∈ E, from  K_E ((set.mem_inter_iff v K E').mp v_in).left,
    exfalso,
    apply En,
    apply eq_of_not_disjoint E E',
    rw set.not_disjoint_iff, use [v,vE,vE'],},
  { have KdisE': disjoint K E', by { rw set.disjoint_iff_inter_eq_empty,rw set.not_nonempty_iff_eq_empty at KE', exact KE', },
    have : ∃ F' : comp_out G K, (E' : set V) ⊆ F' ∧ F'.inf, by {
      let F' := of_connected_disjoint (E' : set V) (E'.connected) KdisE',
      let sub := of_connected_disjoint_sub (E' : set V) (E'.connected) KdisE',
      have F'inf : F'.inf, from set.infinite.mono sub Einf',
      use [F',sub,F'inf],
    },
    rcases this with ⟨F',sub,inf⟩,
    by_cases Fe : F' = F,
    { exact Fe ▸ sub,},
    { rcases @comp_out.adj V G H Gpc Hnempty E' (E'.dis_of_inf Einf') with ⟨⟨v,h⟩,vE',hH,a⟩,
      have : h ∈ F, from H_F hH,
      exfalso,
      apply F.nonadj,
      use [h, v],
      refine ⟨this,_,_,_,a.symm⟩,
      { rintro vF,
        apply Fe,
        apply eq_of_not_disjoint, rw set.not_disjoint_iff, use [v,sub vE', vF], },
      { rintro hK,
        have : ¬ disjoint K F, by {rw  set.not_disjoint_iff, use [h,hK,this],},
        exact this (F.dis_of_inf Finf), },
      { rintro vK, rw [set.not_nonempty_iff_eq_empty,←set.subset_empty_iff] at KE',
        apply KE',
        exact ⟨vK,vE'⟩, },
    },
  },
end

end comp_out

namespace inf_comp_out

include Glf Gpc
lemma bwd_map_non_inj (H K : finset V) (C : G.inf_comp_out H)
  (D D' : G.inf_comp_out K)
  (Ddist : D ≠ D')
  (h : (D : set V) ⊆ C) (h' : (D' : set V) ⊆ C) :
  ¬ injective (@inf_comp_out.back _ G _ _ (finset.subset_union_left H K : H ⊆ H ∪ K)) :=
begin
  rcases inf_comp_out.back_surjective G Glf Gpc (finset.subset_union_right H K) D  with ⟨E,rfl⟩,
  rcases inf_comp_out.back_surjective G Glf Gpc (finset.subset_union_right H K) D' with ⟨E',rfl⟩,
  have Edist : E ≠ E', by {rintro Eeq, rw Eeq at Ddist,exact Ddist (refl _)},
  have : E.back (finset.subset_union_left H K) = E'.back (finset.subset_union_left H K), by {
    have EsubC : (E : set V) ⊆ C, by {refine  set.subset.trans _ h, apply back_sub,},
    have E'subC : (E' : set V) ⊆ C, by {refine  set.subset.trans _ h', apply back_sub,},
    rw ←eq_back_iff_sub (finset.subset_union_left H K) at EsubC,
    rw ←eq_back_iff_sub (finset.subset_union_left H K) at E'subC,
    rw [EsubC,E'subC],
  },
  rintro inj,
  exact Edist (inj this),
end

lemma nicely_arranged_bwd_map_not_inj (H K : finset V) (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E : G.inf_comp_out H) (inf_comp_H_large : fin 3 ↪ (G.inf_comp_out H))
  (F : G.inf_comp_out K)
  (H_F : (H : set V) ⊆ F)
  (K_E : (K : set V) ⊆ E) :
  ¬ injective (@inf_comp_out.back _ G _ _ (finset.subset_union_left K H : K ⊆ K ∪ H)) :=
begin
 have : ∃ E₁ E₂ : G.inf_comp_out H, E ≠ E₁ ∧ E ≠ E₂ ∧ E₁ ≠ E₂, by
  { let E₀ := inf_comp_H_large 0,
    let E₁ := inf_comp_H_large 1,
    let E₂ := inf_comp_H_large 2,
    by_cases h : E = E₀,
    { use [E₁,E₂], rw h, simp,split,apply fin.ne_of_vne,simp,apply fin.ne_of_vne, simp,},
    { by_cases k : E = E₁,
      { use [E₀,E₂], rw k, simp,split,apply fin.ne_of_vne,simp,apply fin.ne_of_vne, simp,},
      { use [E₀,E₁], simp, exact ⟨h,k⟩,},
    },
  },
  rcases this with ⟨E₁, E₂, h₀₁, h₀₂, h₁₂⟩,
  rw [ne.def,←subtype.coe_inj,←subtype.coe_inj,←ne.def] at h₀₁ h₀₂,
  apply bwd_map_non_inj G Glf Gpc K H F E₁ E₂ h₁₂ _ _,
  {apply comp_out.nicely_arranged G Glf Gpc H K Hnempty Knempty E E₁ E.prop E₁.prop h₀₁ F F.prop H_F K_E,},
  {apply comp_out.nicely_arranged G Glf Gpc H K Hnempty Knempty E E₂ E.prop E₂.prop h₀₂ F F.prop H_F K_E,},
end

end inf_comp_out

namespace comp_out

lemma of_connected_disjoint.eq {K K' : set V} (KeK' : K = K') (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint K S) :
  (of_connected_disjoint S conn dis : set V) = (of_connected_disjoint S conn (by {rw KeK' at dis, exact dis}) : set V) :=
begin
  induction KeK',
  refl,
end

end comp_out

/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
include Gpc Glf
lemma good_autom_back_not_inj
  (auts : ∀ K : finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : finset V)
  (inf_comp_H_large : fin 3 ↪ (G.inf_comp_out K)) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),
    ¬ injective (inf_comp_out.back hL : G.inf_comp_out L → G.inf_comp_out K') :=
begin
  haveI Kn : K.nonempty,
  { rw nonempty_iff_ne_empty,
    by_contradiction h, rw h at inf_comp_H_large,
    have e : fin 3 ↪ (G.inf_comp_out ∅), by
    { apply inf_comp_H_large,},
    haveI := inf_comp_out.of_empty_is_subsingleton Gpc,
    have := e.inj' (subsingleton.elim (e 0) (e 1)),
    finish,},
  let Kp := (finset.extend_to_connected G Gpc K Kn).val,
  obtain ⟨KKp,Kpc⟩ := (finset.extend_to_connected G Gpc K Kn).prop,

  haveI Kpn := set.nonempty.mono KKp Kn,
  obtain ⟨K',KK',Kc',inf⟩ := @comp_out.extend_connected_with_fin_bundled V G Kp,
  rcases auts K' with ⟨φ,φgood⟩,

  let φK' := finset.image φ K',
  have φK'eq : φ '' (K' : set V) = φK', by {symmetry, apply finset.coe_image,},

  let K'n := finset.nonempty.mono (KKp.trans KK') Kn,
  let φK'n := finset.nonempty.image K'n φ,
  let L := K' ∪ φK',
  use [K',L,KKp.trans KK',finset.subset_union_left  K' (φK')],

  have φK'c : (G.induce (φK' : set V)).connected, by
  { rw ←φK'eq,
    rw ←iso.connected (iso.induce_restrict φ K'),
    exact Kc',},

  let E := comp_out.of_connected_disjoint (φK' : set V) φK'c (finset.disjoint_coe.mpr φgood),
  let Edis := comp_out.of_connected_disjoint_dis (φK' : set V) φK'c (finset.disjoint_coe.mpr φgood),
  let Esub := comp_out.of_connected_disjoint_sub (φK' : set V) φK'c (finset.disjoint_coe.mpr φgood),

  let F := comp_out.of_connected_disjoint (K' : set V) Kc' (finset.disjoint_coe.mpr φgood.symm),
  let Fdis := comp_out.of_connected_disjoint_dis (K' : set V) Kc' (finset.disjoint_coe.mpr φgood.symm),
  let Fsub := comp_out.of_connected_disjoint_sub (K' : set V) Kc' (finset.disjoint_coe.mpr φgood.symm),


  have Einf : E.inf := inf E Edis,
  have Finf : F.inf, by {
    rw [comp_out.inf,
        comp_out.of_connected_disjoint.eq G φK'eq.symm,
        ←comp_out.inf],

    let e := (comp_out.equiv_of_iso φ K'),

    rw [←e.right_inv (comp_out.of_connected_disjoint ↑K' Kc' _),
        equiv.to_fun_as_coe,
        ←comp_out.equiv_of_iso.inf φ K' (e.inv_fun (comp_out.of_connected_disjoint ↑K' Kc' _))],
    apply inf,
    rw [comp_out.equiv_of_iso.dis φ K' (e.inv_fun (comp_out.of_connected_disjoint ↑K' Kc' _)),
        ←equiv.to_fun_as_coe,
        e.right_inv (comp_out.of_connected_disjoint ↑K' Kc' _)],
    apply comp_out.of_connected_disjoint_dis, },


  apply inf_comp_out.nicely_arranged_bwd_map_not_inj G Glf Gpc φK' K' (φK'n) (K'n) ⟨⟨F,Fdis⟩,Finf⟩ _ ⟨⟨E,Edis⟩,Einf⟩ Esub Fsub,
  have e := (inf_comp_out.equiv_of_iso φ K'),
  apply inf_comp_H_large.trans,
  rw φK'eq at e,
  refine function.embedding.trans _ e.to_embedding,
  apply function.embedding.of_surjective,
  exact inf_comp_out.back_surjective G Glf Gpc (KKp.trans KK'),
end


lemma Freudenthal_Hopf
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K)) :
  (fin 3 ↪ Endsinfty G) → (Endsinfty G).infinite :=
begin

  -- Assume we have at least three ends, but finitely many
  intros many_ends finite_ends,

  -- Boring boilerplate
  haveI : fintype (ComplInfComp G).sections := finite.fintype finite_ends,
  haveI : Π (j : finset V), fintype ((ComplInfComp G).obj j) := ComplInfComp_fintype  G Glf Gpc,
  have surj : inverse_system.is_surjective (ComplInfComp G) := ComplInfComp.surjective G Glf Gpc,

  -- By finitely many ends, and since the system is nice, there is some K such that each inf_comp_out_back to K is injective
  obtain ⟨K,top⟩ := inverse_system.sections_fintype_to_injective (ComplInfComp G) surj,
  -- Since each inf_comp_out_back to K is injective, the map from sections to K is also injective
  let inj' := inverse_system.sections_injective (ComplInfComp G) K top,

  -- Because we have at least three ends and enough automorphisms, we can apply `good_autom_bwd_map_not_inj`
  -- giving us K ⊆ K' ⊆ L with the inf_comp_out_back from L to K' not injective.
  obtain ⟨K',L,KK',K'L,bwd_K_not_inj⟩ := (good_autom_back_not_inj G Glf Gpc auts K (many_ends.trans ⟨_,inj'⟩)),
  -- which is in contradiction with the fact that all inf_comp_out_back to K are injective
  apply bwd_K_not_inj,
  -- The following is just that if f ∘ g is injective, then so is g
  rintro x y eq,
  apply top ⟨L,by {exact KK'.trans K'L,}⟩,
  simp only [ComplInfComp.map],
  have eq' := congr_arg (inf_comp_out.back KK') eq,
  simp only [inf_comp_out.back_trans_apply] at eq',
  exact eq',
end

end simple_graph
