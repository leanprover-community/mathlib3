import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.properties

open classical function category_theory opposite

universes u v w

noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph
namespace component_compl

variables {V : Type u} {G : simple_graph V} [Gpc : fact G.preconnected]

include Gpc

lemma subset_of_nicely_arranged
  (H K : set V)
  (Hnempty : H.nonempty)
  (E E' : G.component_compl H)
  (Einf' : E'.supp.infinite)
  (En : E ≠ E')
  (F : G.component_compl K)
  (H_F : H ⊆ F)
  (K_E : K ⊆ E) : (E' : set V) ⊆ F :=
begin
  have KE' : (K ∩ E') ⊆ ∅ := λ v ⟨vK, vE'⟩,
    En (component_compl.pairwise_disjoint.eq (set.not_disjoint_iff.mpr ⟨v, K_E vK, vE'⟩)),
  obtain ⟨F', sub, inf⟩ : ∃ F' : component_compl G K, (E' : set V) ⊆ F' ∧ F'.supp.infinite :=
    ⟨ of_connected_disjoint_right E'.connected (set.disjoint_iff.mpr KE'),
      subset_of_connected_disjoint_right _ _,
      Einf'.mono (subset_of_connected_disjoint_right _ _)⟩,
  have : F' = F, by
  { obtain ⟨⟨v, h⟩, vE', hH, a⟩:= exists_adj_boundary_pair Gpc.out Hnempty E',
    exact eq_of_adj v h (sub vE') (H_F hH) a, },
  exact this ▸ sub,
end

variables [locally_finite G]

lemma hom_not_injective
  {H K : (finset V)ᵒᵖ}
  (C : G.component_compl_functor.to_eventual_ranges.obj H)
  (D D' : G.component_compl_functor.to_eventual_ranges.obj K)
  (Ddist : D ≠ D')
  (h : D.val.supp ⊆ C.val.supp) (h' : D'.val.supp ⊆ C.val.supp) :
  ¬ (injective $
    G.component_compl_functor.to_eventual_ranges.map
      (op_hom_of_le $ finset.subset_union_left H.unop K.unop : op (H.unop ∪ K.unop) ⟶ H)) :=
begin
  obtain ⟨E, hE⟩ :=
    functor.surjective_to_eventual_ranges _ G.component_compl_functor_is_mittag_leffler
      (op_hom_of_le $ finset.subset_union_right H.unop K.unop : op (H.unop ∪ K.unop) ⟶ K) D,
  obtain ⟨E', hE'⟩ :=
    functor.surjective_to_eventual_ranges _ G.component_compl_functor_is_mittag_leffler
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

omit Gpc
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

include Gpc
lemma hom_not_injective_of_nicely_arranged
  {H K : (finset V)ᵒᵖ}
  (Hnempty : (unop H).nonempty)
  (E : G.component_compl_functor.to_eventual_ranges.obj H)
  (F : G.component_compl_functor.to_eventual_ranges.obj K)
  (H_F : (H.unop : set V) ⊆ F.val.supp)
  (K_E : (K.unop : set V) ⊆ E.val.supp)
  {hK : fin 3 ↪ (G.component_compl_functor.to_eventual_ranges.obj H)} :
  ¬ (injective $
    G.component_compl_functor.to_eventual_ranges.map
      (op_hom_of_le $ finset.subset_union_left K.unop H.unop : op (K.unop ∪ H.unop) ⟶ K)) :=
begin
  obtain ⟨E₁, E₂, h₀₁, h₀₂, h₁₂⟩ := (fin.fin3_embedding_iff' E).mp ⟨hK⟩,
  apply hom_not_injective F E₁ E₂ h₁₂ _ _,
  { apply subset_of_nicely_arranged _ _ Hnempty E.val E₁.val,
    any_goals
    { rw infinite_iff_in_eventual_range },
    exacts [E₁.prop, λ h, h₀₁ (subtype.eq h), H_F, K_E], },
  { apply subset_of_nicely_arranged _ _ Hnempty E.val E₂.val,
    any_goals
    { rw infinite_iff_in_eventual_range },
    exacts [E₂.prop, λ h, h₀₂ (subtype.eq h), H_F, K_E], },
end


omit Gpc
-- TODO: fit somewhere
lemma _root_.fin.embedding_subsingleton {n : ℕ} {α : Type*} [subsingleton α] (e : fin n ↪ α) :
  n ≤ 1 :=
begin
  by_contra' h,
  simpa using e.inj' (subsingleton.elim (e ⟨0,zero_lt_one.trans h⟩) (e ⟨1,h⟩)),
end
include Gpc

/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does L, and
  bwd_map ‹L⊆L› is not injective, hence the graph has more than three ends.
-/
lemma hom_not_injective_of_enough_automorphisms_of_many_components
  (auts : ∀ K : finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : (finset V)ᵒᵖ)
  (hK : fin 3 ↪ (G.component_compl_functor.to_eventual_ranges.obj K)) :
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
    replace hK := hK.trans (induce_univ_iso G).connected_component_equiv.to_embedding,
    haveI := Gpc.out.subsingleton_connected_component,
    exact nat.not_succ_le_zero _ (nat.le_of_succ_le_succ (fin.embedding_subsingleton hK)), },

  obtain ⟨L,KL,Lc,inf⟩ := exists_saturated_connected_extension G Kn,
  obtain ⟨φ,φh⟩ := auts L,
  let φL := L.image φ,
  have φLc : (G.induce (φL : set V)).connected, by
  { rw [finset.coe_image, ←(induce.iso φ).connected_iff], exact Lc, },

  refine ⟨op L, op (L ∪ φL), op_hom_of_le KL, op_hom_of_le (finset.subset_union_left _ _), _⟩,

  let lol : (G.induce (L : set V)ᶜ) ≃g (G.induce (φL : set V)ᶜ), by
  { rw (by simp only [set.image_compl_eq φ.bijective, finset.coe_image] :
          (φL : set V)ᶜ = φ '' (L : set V)ᶜ),
    apply induce.iso, },

  have φinf : ∀ C : G.component_compl φL, C.supp.infinite, by
  { simp_rw ←set.infinite_coe_iff at inf ⊢,
    rintro C,
    rw [←lol.connected_component_equiv.right_inv C, equiv.infinite_iff],
    exact inf (lol.connected_component_equiv.symm C),
    exact (component_compl.supp_equiv _).trans
      ((connected_component.iso_equiv_supp lol.connected_component_equiv _).symm.trans
        (component_compl.supp_equiv _).symm), },

  apply @hom_not_injective_of_nicely_arranged V G Gpc _ (op φL) (op L) ((Kn.mono KL).image φ) ⟨_, _⟩ ⟨_, _⟩
    (subset_of_connected_disjoint_right φLc (finset.disjoint_coe.mpr φh))
    (subset_of_connected_disjoint_right Lc (finset.disjoint_coe.mpr φh.symm)) _,
  exact (@component_compl.infinite_iff_in_eventual_range V G (op φL) _).mp (φinf _),
  exact (@component_compl.infinite_iff_in_eventual_range V G (op L) _).mp (inf _),

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

lemma Freudenthal_Hopf [Vi : infinite V]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (many_ends : fin 3 ↪ G.end) : G.end.infinite :=
begin
  intros finite_ends,
  let Gccf := G.component_compl_functor,
  -- Gccf has nonempty sections and nonempty sets at each K
  haveI := finite_ends.fintype,
  haveI := fintype.of_equiv G.end (Gccf.to_eventual_ranges_sections_equiv).symm,
  haveI := G.component_compl_functor_to_eventual_ranges_finite,
  haveI := λ j, component_compl_functor_to_eventual_ranges_nonempty_of_infinite G Gpc j,
  -- Gccf is a "surjective" system
  have surj : ∀ ⦃i j⦄ (f : i ⟶ j), function.surjective _ :=
    functor.surjective_to_eventual_ranges _ (G.component_compl_functor_is_mittag_leffler Gpc),
  -- All the maps of Gccf to `K` are injective, and `Gccf K` has at least 3 components.
  obtain ⟨K,top⟩ := Gccf.to_eventual_ranges.eventually_injective surj,
  let inj' := Gccf.to_eventual_ranges.eval_section_injective_of_eventually_injective top,
  let inj'' := (many_ends.trans (Gccf.to_eventual_ranges_sections_equiv).symm.to_embedding).trans
                 ⟨_, (inj' K (𝟙 K))⟩,
  -- But there is a point above `K` from which the `Gccf` is not injective.
  -- Derive a contradiction
  obtain ⟨L,M,KL,LM,LM_not_inj⟩ :=
    hom_not_injective_of_enough_automorphisms_of_many_components Gpc auts K inj'',
  refine LM_not_inj (@injective.of_comp _ _ _ (Gccf.to_eventual_ranges.map KL) _ _),
  rw [←types_comp,←functor.map_comp],
  apply top,
end

lemma good_automs_of_infinite_transitive
  [Vi : infinite V] [locally_finite G]
  (Gpc : G.preconnected)
  (trans : ∀ (x y : V), ∃ φ : G ≃g G, φ x = y) (K :finset V) :
  ∃ φ : G ≃g G, disjoint K (K.image φ) :=
begin
  sorry,
  -- assume K has diameter m,
  -- take x in K, and some y at distance ≥2m from x.
end

end component_compl
end simple_graph
#lint
