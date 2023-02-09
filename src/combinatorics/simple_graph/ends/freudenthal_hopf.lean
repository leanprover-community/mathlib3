import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.properties

open classical function category_theory opposite

universes u v w

noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph

variables  {V : Type u} (G : simple_graph V)

namespace component_compl

open simple_graph


lemma nicely_arranged (H K : set V)
  (Gpc : G.preconnected)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E E' : G.component_compl H)
  (Einf : E.supp.infinite) (Einf' : E'.supp.infinite)
  (En : E ≠ E')
  (F : G.component_compl K) (Finf : F.supp.infinite)
  (H_F : H ⊆ F)
  (K_E : K ⊆ E) : (E' : set V) ⊆ F :=
begin
  have KE' : (K ∩ E') ⊆ ∅ := λ v ⟨vK, vE'⟩,
    En (component_compl.pairwise_disjoint.eq (set.not_disjoint_iff.mpr ⟨v, K_E vK, vE'⟩)),
  obtain ⟨F', sub, inf⟩ : ∃ F' : component_compl G K, (E' : set V) ⊆ F' ∧ F'.supp.infinite, by
  { obtain ⟨v, vnH, rfl⟩ := E'.exists_eq_mk,
    /-
    TODO : How to do properly?
    Originally was `comp_out.of_connected_disjoint` but that means we need to talk about `connected`
    which is a pain.
    -/
    have : (G.component_compl_mk vnH).supp ⊆
            (G.component_compl_mk (λ vK, KE' ⟨vK, component_compl_mk_mem _ _⟩)).supp, by sorry,
    exact ⟨component_compl_mk _ (λ vK, KE' ⟨vK, component_compl_mk_mem _ _⟩),
            this, Einf'.mono this⟩, },
    have : F' = F, by
    { obtain ⟨⟨v, h⟩, vE', hH, a⟩:= exists_adj_boundary_pair Gpc Hnempty E',
      exact component_compl.eq_of_adj v h (sub vE') (H_F hH) a, },
    exact this ▸ sub,

end

lemma bwd_map_non_inj
  [locally_finite G]
  (Gpc : G.preconnected)
  (H K : (finset V)ᵒᵖ)
  (C : G.component_compl_functor.obj H)
  (Cinf : C.supp.infinite)
  (D D' : G.component_compl_functor.obj K)
  (Dinf : D.supp.infinite) (Dinf' : D'.supp.infinite)
  (Ddist : D ≠ D')
  (h : D.supp ⊆ C.supp) (h' : D'.supp ⊆ C.supp) :
  ¬ (injective $
    G.component_compl_functor.to_eventual_ranges.map
      (op_hom_of_le $ finset.subset_union_left H.unop K.unop : op (H.unop ∪ K.unop) ⟶ H)) :=
begin
  classical,
  rw component_compl.infinite_iff_in_eventual_range at Dinf Dinf',
  obtain ⟨E, hE⟩ :=
    functor.surjective_to_eventual_ranges _ (G.component_compl_functor_is_mittag_leffler Gpc)
      (op_hom_of_le $ finset.subset_union_right H.unop K.unop : op (H.unop ∪ K.unop) ⟶ K) ⟨D,Dinf⟩,
  obtain ⟨E', hE'⟩ :=
    functor.surjective_to_eventual_ranges _ (G.component_compl_functor_is_mittag_leffler Gpc)
      (op_hom_of_le $ finset.subset_union_right H.unop K.unop : op (H.unop ∪ K.unop) ⟶ K) ⟨D',Dinf'⟩,
  simp only [subtype.ext_iff_val, functor.to_eventual_ranges_map, subtype.val_eq_coe,
             set.maps_to.coe_restrict_apply, component_compl_functor_map] at hE hE',
  subst_vars,
  refine λ inj, (by { rintro rfl, exact Ddist rfl, } : E ≠ E') (inj _),
  obtain ⟨E, _⟩ := E,
  obtain ⟨E', _⟩ := E',
  dsimp only [component_compl_functor, functor.to_eventual_ranges, functor.eventual_range] at *,
  simp only [subtype.ext_iff_val, subtype.val_eq_coe, set.maps_to.coe_restrict_apply, subtype.coe_mk],
  rw [(hom_eq_iff_le _ _ _).mpr ((E.subset_hom _).trans h),
      (hom_eq_iff_le _ _ _).mpr ((E'.subset_hom _).trans h')],
end

lemma nicely_arranged_bwd_map_not_inj (H K : finset V) (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E : G.inf_component_compl H) (inf_comp_H_large : fin 3 ↪ (G.inf_component_compl H))
  (F : G.inf_component_compl K)
  (H_F : (H : set V) ⊆ F)
  (K_E : (K : set V) ⊆ E) :
  ¬ injective (@inf_component_compl.back _ G _ _ (finset.subset_union_left K H : K ⊆ K ∪ H)) :=
begin
 have : ∃ E₁ E₂ : G.inf_component_compl H, E ≠ E₁ ∧ E ≠ E₂ ∧ E₁ ≠ E₂, by
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
  {apply component_compl.nicely_arranged G Glf Gpc H K Hnempty Knempty E E₁ E.prop E₁.prop h₀₁ F F.prop H_F K_E,},
  {apply component_compl.nicely_arranged G Glf Gpc H K Hnempty Knempty E E₂ E.prop E₂.prop h₀₂ F F.prop H_F K_E,},
end


namespace component_compl

lemma of_connected_disjoint.eq {K K' : set V} (KeK' : K = K') (S : set V)
  (conn : (G.induce S).connected) (dis : disjoint K S) :
  (of_connected_disjoint S conn dis : set V) = (of_connected_disjoint S conn (by {rw KeK' at dis, exact dis}) : set V) :=
begin
  induction KeK',
  refl,
end

end component_compl

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
  (inf_comp_H_large : fin 3 ↪ (G.inf_component_compl K)) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),
    ¬ injective (inf_component_compl.back hL : G.inf_component_compl L → G.inf_component_compl K') :=
begin
  haveI Kn : K.nonempty,
  { rw nonempty_iff_ne_empty,
    by_contradiction h, rw h at inf_comp_H_large,
    have e : fin 3 ↪ (G.inf_component_compl ∅), by
    { apply inf_comp_H_large,},
    haveI := inf_component_compl.of_empty_is_subsingleton Gpc,
    have := e.inj' (subsingleton.elim (e 0) (e 1)),
    finish,},
  let Kp := (finset.extend_to_connected G Gpc K Kn).val,
  obtain ⟨KKp,Kpc⟩ := (finset.extend_to_connected G Gpc K Kn).prop,

  haveI Kpn := set.nonempty.mono KKp Kn,
  obtain ⟨K',KK',Kc',inf⟩ := @component_compl.extend_connected_with_fin_bundled V G Kp,
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

  let E := component_compl.of_connected_disjoint (φK' : set V) φK'c (finset.disjoint_coe.mpr φgood),
  let Edis := component_compl.of_connected_disjoint_dis (φK' : set V) φK'c (finset.disjoint_coe.mpr φgood),
  let Esub := component_compl.of_connected_disjoint_sub (φK' : set V) φK'c (finset.disjoint_coe.mpr φgood),

  let F := component_compl.of_connected_disjoint (K' : set V) Kc' (finset.disjoint_coe.mpr φgood.symm),
  let Fdis := component_compl.of_connected_disjoint_dis (K' : set V) Kc' (finset.disjoint_coe.mpr φgood.symm),
  let Fsub := component_compl.of_connected_disjoint_sub (K' : set V) Kc' (finset.disjoint_coe.mpr φgood.symm),


  have Einf : E.inf := inf E Edis,
  have Finf : F.inf, by {
    rw [component_compl.inf,
        component_compl.of_connected_disjoint.eq G φK'eq.symm,
        ←component_compl.inf],

    let e := (component_compl.equiv_of_iso φ K'),

    rw [←e.right_inv (component_compl.of_connected_disjoint ↑K' Kc' _),
        equiv.to_fun_as_coe,
        ←component_compl.equiv_of_iso.inf φ K' (e.inv_fun (component_compl.of_connected_disjoint ↑K' Kc' _))],
    apply inf,
    rw [component_compl.equiv_of_iso.dis φ K' (e.inv_fun (component_compl.of_connected_disjoint ↑K' Kc' _)),
        ←equiv.to_fun_as_coe,
        e.right_inv (component_compl.of_connected_disjoint ↑K' Kc' _)],
    apply component_compl.of_connected_disjoint_dis, },


  apply inf_component_compl.nicely_arranged_bwd_map_not_inj G Glf Gpc φK' K' (φK'n) (K'n) ⟨⟨F,Fdis⟩,Finf⟩ _ ⟨⟨E,Edis⟩,Einf⟩ Esub Fsub,
  have e := (inf_component_compl.equiv_of_iso φ K'),
  apply inf_comp_H_large.trans,
  rw φK'eq at e,
  refine function.embedding.trans _ e.to_embedding,
  apply function.embedding.of_surjective,
  exact inf_component_compl.back_surjective G Glf Gpc (KKp.trans KK'),
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

  -- By finitely many ends, and since the system is nice, there is some K such that each inf_component_compl_back to K is injective
  obtain ⟨K,top⟩ := inverse_system.sections_fintype_to_injective (ComplInfComp G) surj,
  -- Since each inf_component_compl_back to K is injective, the map from sections to K is also injective
  let inj' := inverse_system.sections_injective (ComplInfComp G) K top,

  -- Because we have at least three ends and enough automorphisms, we can apply `good_autom_bwd_map_not_inj`
  -- giving us K ⊆ K' ⊆ L with the inf_component_compl_back from L to K' not injective.
  obtain ⟨K',L,KK',K'L,bwd_K_not_inj⟩ := (good_autom_back_not_inj G Glf Gpc auts K (many_ends.trans ⟨_,inj'⟩)),
  -- which is in contradiction with the fact that all inf_component_compl_back to K are injective
  apply bwd_K_not_inj,
  -- The following is just that if f ∘ g is injective, then so is g
  rintro x y eq,
  apply top ⟨L,by {exact KK'.trans K'L,}⟩,
  simp only [ComplInfComp.map],
  have eq' := congr_arg (inf_component_compl.back KK') eq,
  simp only [inf_component_compl.back_trans_apply] at eq',
  exact eq',
end

end simple_graph
