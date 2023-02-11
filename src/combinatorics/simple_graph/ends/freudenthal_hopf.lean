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

lemma _root_.fin.fin3_embedding_iff {α : Type*} :
  nonempty (fin 3 ↪ α) ↔ ∃ (a₀ a₁ a₂ : α), a₀ ≠ a₁ ∧ a₀ ≠ a₂ ∧ a₁ ≠ a₂ := sorry

lemma _root_.fin.fin3_embedding_iff' {α : Type*} (a : α):
  nonempty (fin 3 ↪ α) ↔ ∃ (a₁ a₂ : α), a ≠ a₁ ∧ a ≠ a₂ ∧ a₁ ≠ a₂ :=
begin
  split,
  rintro ⟨e⟩,
  { by_cases h : a = e 0,
    { use [e 1, e 2],
      simp only [h, embedding_like.apply_eq_iff_eq, fin.eq_iff_veq, fin.val_zero', fin.val_one,
                 fin.val_two, ne.def, zero_eq_bit0, nat.one_ne_zero, nat.zero_ne_one, not_false_iff,
                 nat.one_ne_bit0, and_self], },
    { by_cases k : a = e 1,
      { use [e 0, e 2],
        simp only [h, k, embedding_like.apply_eq_iff_eq, fin.eq_iff_veq, fin.val_zero', fin.val_one,
                 fin.val_two, ne.def, zero_eq_bit0, nat.one_ne_zero, nat.zero_ne_one, not_false_iff,
                 nat.one_ne_bit0, and_self], },
      { use [e 0, e 1],
        simp only [h, k, ne.def, embedding_like.apply_eq_iff_eq, fin.zero_eq_one_iff,
                   nat.bit1_eq_one, nat.one_ne_zero, not_false_iff, and_true],  }, }, },
  { rintro ⟨a₁,a₂,h₁,h₂,h⟩,
    refine ⟨⟨λ i, [a,a₁,a₂].nth_le i.val i.prop, _⟩⟩,
    have : list.nodup [a,a₁,a₂], by simp [h, h₁, h₂],
    rintro ⟨i,hi⟩ ⟨j,hj⟩,
    simp [list.nodup.nth_le_inj_iff this], },
end

lemma nicely_arranged_bwd_map_not_inj
  [locally_finite G]
  (Gpc : G.preconnected)
  {H K : (finset V)ᵒᵖ}
  (Hnempty : (unop H).nonempty)
  {E : G.component_compl_functor.to_eventual_ranges.obj H}
  {F : G.component_compl_functor.to_eventual_ranges.obj K}
  (H_F : (H.unop : set V) ⊆ F.val.supp)
  (K_E : (K.unop : set V) ⊆ E.val.supp)
  {hK : fin 3 ↪ (G.component_compl_functor.to_eventual_ranges.obj H)} :
  ¬ (injective $
    G.component_compl_functor.to_eventual_ranges.map
      (op_hom_of_le $ finset.subset_union_left K.unop H.unop : op (K.unop ∪ H.unop) ⟶ K)) :=
begin
  obtain ⟨E₁, E₂, h₀₁, h₀₂, h₁₂⟩ := (fin.fin3_embedding_iff' E).mp ⟨hK⟩,
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


-- TODO: fit somewhere
lemma _root_.fin.embedding_subsingleton {n : ℕ} {α : Type*} [subsingleton α] (e : fin n ↪ α) :
  n ≤ 1 :=
begin
  by_contra' h,
  simpa using e.inj' (subsingleton.elim (e ⟨0,zero_lt_one.trans h⟩) (e ⟨1,h⟩)),
end

/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does L, and
  bwd_map ‹L⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_back_not_inj
  [locally_finite G]
  (Gpc : G.preconnected)
  (auts : ∀ K : finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : (finset V)ᵒᵖ)
  {hK : fin 3 ↪ (G.component_compl_functor.to_eventual_ranges.obj K)} :
  ∃ (L M : (finset V)ᵒᵖ) (hL : L ⟶ K) (hM : M ⟶ L),
    ¬ (injective $ G.component_compl_functor.to_eventual_ranges.map hM) :=
begin
  have Kn : K.unop.nonempty,
  { by_contradiction h,
    rw finset.not_nonempty_iff_eq_empty at h,
    simp only [unop_eq_iff_eq_op.mp h, component_compl_functor, functor.to_eventual_ranges,
               functor.eventual_range] at hK,
    dsimp [functor.eventual_range, component_compl] at hK,
    replace hK := hK.trans ⟨_, subtype.coe_injective⟩,
    rw [set.compl_empty] at hK,
    replace hK := hK.trans (connected_component.iso (induce_univ_iso G)).to_embedding,
    haveI := Gpc.subsingleton_connected_component,
    exact nat.not_succ_le_zero _ (nat.le_of_succ_le_succ (fin.embedding_subsingleton hK)), },

  -- TODO: make this into a lemma for `component_compl` : it's lots of work
  obtain ⟨L,KL,Lc,inf⟩ : ∃ (L : finset V), K.unop ⊆ L ∧ (G.induce (L : set V)).connected ∧
                              ∀ C : G.component_compl L, C.supp.infinite := sorry,
  obtain ⟨φ,φh⟩ := auts L,
  have Ln : L.nonempty := finset.nonempty.mono KL Kn,
  let φL := L.image φ,
  have φLc : (G.induce (φL : set V)).connected, by
  { rw [finset.coe_image, ←(induce.iso φ).connected_iff], exact Lc, },

  refine ⟨op L, op (L ∪ φL), op_hom_of_le KL, op_hom_of_le (finset.subset_union_left _ _), _⟩,

  let lol : (G.induce (L : set V)ᶜ) ≃g
            (G.induce (φL : set V)ᶜ), by
  { have : (φL : set V)ᶜ = φ '' (L : set V)ᶜ, by
      simp only [set.image_compl_eq φ.bijective, finset.coe_image],
    rw [this],
    apply induce.iso, },

  let E := of_connected_disjoint_right φLc (finset.disjoint_coe.mpr φh),
  let Esub := subset_of_connected_disjoint_right φLc (finset.disjoint_coe.mpr φh),
  let F := of_connected_disjoint_right Lc (finset.disjoint_coe.mpr φh.symm),
  let Fsub := subset_of_connected_disjoint_right Lc (finset.disjoint_coe.mpr φh.symm),
  have φinf : ∀ C : G.component_compl φL, C.supp.infinite, by
  { simp_rw ←set.infinite_coe_iff at inf ⊢,
    rintro C,
    rw [←(connected_component.iso lol).right_inv C, equiv.infinite_iff],
    exact inf ((connected_component.iso lol).symm C),
    transitivity,
    { apply component_compl.supp_equiv, },
    transitivity,
    { symmetry, exact (connected_component.apply_iso_equiv lol _), },
    { symmetry, apply component_compl.supp_equiv, }, },

  apply @nicely_arranged_bwd_map_not_inj V G _ Gpc (op φL) (op L) (Ln.image φ) ⟨F,_⟩ ⟨E,_⟩ Esub Fsub _,
  exact (@component_compl.infinite_iff_in_eventual_range V G (op φL) F).mp (φinf F),
  exact (@component_compl.infinite_iff_in_eventual_range V G (op L) E).mp (inf E),

  have eL: G.component_compl_functor.to_eventual_ranges.obj (op L) ≃
         G.component_compl_functor.to_eventual_ranges.obj (op φL), by
  { simp_rw component_compl_functor_to_eventual_ranges_obj_eq,
    refine ((equiv.subtype_univ_equiv inf).trans (connected_component.iso lol)).trans (equiv.subtype_univ_equiv φinf).symm, },
  have iK: G.component_compl_functor.to_eventual_ranges.obj K ↪
         G.component_compl_functor.to_eventual_ranges.obj (op L), by
  { refine function.embedding.of_surjective
      (G.component_compl_functor.to_eventual_ranges.map $ op_hom_of_le KL) _,
    apply G.component_compl_functor.surjective_to_eventual_ranges,
    exact G.component_compl_functor_is_mittag_leffler Gpc, },
  exact (hK.trans iK).trans eL.to_embedding,
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
  -- giving us K ⊆ L ⊆ L with the inf_component_compl_back from L to L not injective.
  obtain ⟨L,L,KL,LL,bwd_K_not_inj⟩ := (good_autom_back_not_inj G Glf Gpc auts K (many_ends.trans ⟨_,inj'⟩)),
  -- which is in contradiction with the fact that all inf_component_compl_back to K are injective
  apply bwd_K_not_inj,
  -- The following is just that if f ∘ g is injective, then so is g
  rintro x y eq,
  apply top ⟨L,by {exact KL.trans LL,}⟩,
  simp only [ComplInfComp.map],
  have eq' := congr_arg (inf_component_compl.back KL) eq,
  simp only [inf_component_compl.back_trans_apply] at eq',
  exact eq',
  -/
end

end simple_graph
