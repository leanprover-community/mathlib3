import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.properties

open classical function category_theory opposite

universes u v w

noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph

variables  {V : Type u} {G : simple_graph V}

open component_compl

lemma nicely_arranged {H K : set V}
  (Gpc : G.preconnected)
  (Hnempty : H.nonempty) --(Knempty : K.nonempty)
  (E E' : G.component_compl H)
  (Einf : E.supp.infinite) (Einf' : E'.supp.infinite)
  (En : E ≠ E')
  (F : G.component_compl K) (Finf : F.supp.infinite)
  (H_F : H ⊆ F)
  (K_E : K ⊆ E) : (E' : set V) ⊆ F :=
begin
  have KE' : (K ∩ E') ⊆ ∅ := λ v ⟨vK, vE'⟩,
    En (component_compl.pairwise_disjoint.eq (set.not_disjoint_iff.mpr ⟨v, K_E vK, vE'⟩)),
  obtain ⟨F', sub, inf⟩ : ∃ F' : component_compl G K, (E' : set V) ⊆ F' ∧ F'.supp.infinite :=
    ⟨ component_compl.of_connected_disjoint_right E'.connected (set.disjoint_iff.mpr KE'),
      component_compl.subset_of_connected_disjoint_right _ _,
      Einf'.mono (component_compl.subset_of_connected_disjoint_right _ _)⟩,
  have : F' = F, by
  { obtain ⟨⟨v, h⟩, vE', hH, a⟩:= exists_adj_boundary_pair Gpc Hnempty E',
    exact component_compl.eq_of_adj v h (sub vE') (H_F hH) a, },
  exact this ▸ sub,
end

lemma bwd_map_non_inj
  [locally_finite G]
  (Gpc : G.preconnected)
  {H K : (finset V)ᵒᵖ}
  {C : G.component_compl_functor.to_eventual_ranges.obj H}
  {D D' : G.component_compl_functor.to_eventual_ranges.obj K}
  (Ddist : D ≠ D')
  (h : D.val.supp ⊆ C.val.supp) (h' : D'.val.supp ⊆ C.val.supp) :
  ¬ (injective $
    G.component_compl_functor.to_eventual_ranges.map
      (op_hom_of_le $ finset.subset_union_left H.unop K.unop : op (H.unop ∪ K.unop) ⟶ H)) :=
begin
  obtain ⟨E, hE⟩ :=
    functor.surjective_to_eventual_ranges _ (G.component_compl_functor_is_mittag_leffler Gpc)
      (op_hom_of_le $ finset.subset_union_right H.unop K.unop : op (H.unop ∪ K.unop) ⟶ K) D,
  obtain ⟨E', hE'⟩ :=
    functor.surjective_to_eventual_ranges _ (G.component_compl_functor_is_mittag_leffler Gpc)
      (op_hom_of_le $ finset.subset_union_right H.unop K.unop : op (H.unop ∪ K.unop) ⟶ K) D',
  subst_vars,
  refine λ inj, (by { rintro rfl, exact Ddist rfl, } : E ≠ E') (inj _),
  obtain ⟨E, _⟩ := E,
  obtain ⟨E', _⟩ := E',
  dsimp only [component_compl_functor, functor.to_eventual_ranges, functor.eventual_range] at *,
  simp only [subtype.ext_iff_val, subtype.val_eq_coe, set.maps_to.coe_restrict_apply, subtype.coe_mk],
  rw [(hom_eq_iff_le _ _ _).mpr ((E.subset_hom _).trans h),
      (hom_eq_iff_le _ _ _).mpr ((E'.subset_hom _).trans h')],
end


lemma nicely_arranged_bwd_map_not_inj
  [locally_finite G]
  (Gpc : G.preconnected)
  {H K : (finset V)ᵒᵖ}
  (Hnempty : (unop H).nonempty)
  {E : G.component_compl_functor.to_eventual_ranges.obj H}
  {inf_comp_H_large : fin 3 ↪ (G.component_compl_functor.to_eventual_ranges.obj H)}
  {F : G.component_compl_functor.to_eventual_ranges.obj K}
  (H_F : (H.unop : set V) ⊆ F.val.supp)
  (K_E : (K.unop : set V) ⊆ E.val.supp) :
  ¬ (injective $
    G.component_compl_functor.to_eventual_ranges.map
      (op_hom_of_le $ finset.subset_union_left K.unop H.unop : op (K.unop ∪ H.unop) ⟶ K)) :=
begin
  obtain ⟨E₁, E₂, h₀₁, h₀₂, h₁₂⟩ :
    ∃ E₁ E₂ : G.component_compl_functor.to_eventual_ranges.obj H, E ≠ E₁ ∧ E ≠ E₂ ∧ E₁ ≠ E₂, by
  { let E₀ := inf_comp_H_large 0,
    let E₁ := inf_comp_H_large 1,
    let E₂ := inf_comp_H_large 2,
    by_cases h : E = E₀,
    { use [E₁,E₂],
      simp only [h, embedding_like.apply_eq_iff_eq, fin.eq_iff_veq, fin.val_zero', fin.val_one,
                 fin.val_two, ne.def, zero_eq_bit0, nat.one_ne_zero, nat.zero_ne_one, not_false_iff,
                 nat.one_ne_bit0, and_self], },
    { by_cases k : E = E₁,
      { use [E₀,E₂],
        simp only [h, k, embedding_like.apply_eq_iff_eq, fin.eq_iff_veq, fin.val_zero', fin.val_one,
                 fin.val_two, ne.def, zero_eq_bit0, nat.one_ne_zero, nat.zero_ne_one, not_false_iff,
                 nat.one_ne_bit0, and_self], },
      { use [E₀,E₁],
        simp only [ne.def, embedding_like.apply_eq_iff_eq, fin.zero_eq_one_iff, nat.bit1_eq_one,
        nat.one_ne_zero, not_false_iff, and_true], exact ⟨h, k⟩, }, }, },

  apply @bwd_map_non_inj V G _ Gpc _ _ F E₁ E₂ h₁₂ _ _,
  { apply @nicely_arranged _ _ _ _ Gpc Hnempty E.val E₁.val,
    any_goals
    { rw infinite_iff_in_eventual_range },
    exacts [E.prop, E₁.prop, λ h, h₀₁ (subtype.eq h), F.prop, H_F, K_E], },
  { apply @nicely_arranged _ _ _ _ Gpc Hnempty E.val E₂.val,
    any_goals
    { rw infinite_iff_in_eventual_range },
    exacts [E.prop, E₂.prop, λ h, h₀₂ (subtype.eq h), F.prop, H_F, K_E], },
end

/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_back_not_inj
  (auts : ∀ K : finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : (finset V)ᵒᵖ)
  {inf_comp_H_large : fin 3 ↪ (G.component_compl_functor.to_eventual_ranges.obj K)} :
  ∃ (K' L : (finset V)ᵒᵖ) (hK' : K' ⟶ K') (hL : L ⟶ K'),
    ¬ (injective $ G.component_compl_functor.to_eventual_ranges.map hL) :=
begin
  sorry,
  /-
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
  -/
end


lemma Freudenthal_Hopf
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K)) :
  (fin 3 ↪ G.end) → G.end.infinite :=
begin
  sorry
  /-
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
  -/
end

end simple_graph
