/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.category.Top
import category_theory.glue_data

/-!
# Gluing Topological spaces

Given a family of gluing data (see `category_theory/glue_data`), we can then glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `Top.glue_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `Top.glue_data.ι_eq_iff_rel`.

## Main results

* `Top.glue_data.is_open_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `Top.glue_data.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `Top.glue_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.glue_data.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.glue_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.glue_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.glue_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.glue_data.ι_open_embedding`: Each of the `ι i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory

universes v u
open category_theory.limits
namespace Top

/--
A family of gluing data consists of
1. An index type `ι`
2. An object `U i` for each `i : ι`.
3. An object `V i j` for each `i j : ι`.
4. A open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.
-/
@[nolint has_inhabited_instance]
structure glue_data extends glue_data Top :=
  (f_open : ∀ i j, open_embedding (f i j))
  (f_mono := λ i j, (Top.mono_iff_injective _).mpr (f_open i j).to_embedding.inj)

namespace glue_data

variable (D : glue_data.{u})

local notation `𝖣` := D.to_glue_data

lemma π_surjective : function.surjective 𝖣 .π :=
(Top.epi_iff_surjective 𝖣 .π).mp infer_instance

lemma is_open_iff (U : set 𝖣 .glued) : is_open U ↔ ∀ i, is_open (𝖣 .ι i ⁻¹' U) :=
begin
  delta category_theory.glue_data.ι,
  simp_rw ← multicoequalizer.ι_sigma_π 𝖣 .diagram,
  rw ← (homeo_of_iso (multicoequalizer.iso_coequalizer 𝖣 .diagram).symm).is_open_preimage,
  rw [coequalizer_is_open_iff, colimit_is_open_iff],
  refl
end

lemma ι_jointly_surjective (x : 𝖣 .glued) : ∃ i (y : D.U i), 𝖣 .ι i y = x :=
𝖣 .ι_jointly_surjective (forget Top) x

/--
An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Top.glue_data.ι_eq_iff_rel`.
-/
def rel (a b : Σ i, ((D.U i : Top) : Type*)) : Prop :=
  a = b ∨ ∃ (x : D.V (a.1, b.1)) , D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

lemma rel_equiv : equivalence D.rel :=
⟨ λ x, or.inl (refl x),
  begin
    rintros a b (⟨⟨⟩⟩|⟨x,e₁,e₂⟩),
    exacts [or.inl rfl, or.inr ⟨D.t _ _ x, by simp [e₁, e₂]⟩]
  end,
  begin
    rintros ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ (⟨⟨⟩⟩|⟨x,e₁,e₂⟩), exact id,
    rintro (⟨⟨⟩⟩|⟨y,e₃,e₄⟩), exact or.inr ⟨x,e₁,e₂⟩,
    let z := (pullback_iso_prod_subtype (D.f j i) (D.f j k)).inv ⟨⟨_,_⟩, e₂.trans e₃.symm⟩,
    have eq₁ : (D.t j i) ((pullback.fst : _ ⟶ D.V _) z) = x := by simp,
    have eq₂ : (pullback.snd : _ ⟶ D.V _) z = y := pullback_iso_prod_subtype_inv_snd_apply _ _ _,
    clear_value z,
    right,
    use (pullback.fst : _ ⟶ D.V (i, k)) (D.t' _ _ _ z),
    dsimp only at *,
    substs e₁ e₃ e₄ eq₁ eq₂,
    have h₁ : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j,
    { rw ← 𝖣 .t_fac_assoc, congr' 1, exact pullback.condition },
    have h₂ : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i =
      pullback.snd ≫ D.t j k ≫ D.f k j,
    { rw ← 𝖣 .t_fac_assoc,
      apply @epi.left_cancellation _ _ _ _ (D.t' k j i),
      rw [𝖣 .cocycle_assoc, 𝖣 .t_fac_assoc, 𝖣 .t_inv_assoc],
      exact pullback.condition.symm },
    exact ⟨continuous_map.congr_fun h₁ z, continuous_map.congr_fun h₂ z⟩
  end⟩

open category_theory.limits.walking_parallel_pair

lemma eqv_gen_of_π_eq {x y : ∐ D.U} (h : 𝖣 .π x = 𝖣 .π y) :
  eqv_gen (types.coequalizer_rel 𝖣 .diagram.fst_sigma_map 𝖣 .diagram.snd_sigma_map) x y :=
begin
  delta glue_data.π multicoequalizer.sigma_π at h,
  simp_rw comp_app at h,
  replace h := (Top.mono_iff_injective (multicoequalizer.iso_coequalizer 𝖣 .diagram).inv).mp _ h,
  let diagram := parallel_pair 𝖣 .diagram.fst_sigma_map 𝖣 .diagram.snd_sigma_map ⋙ forget _,
  have : colimit.ι diagram one x = colimit.ι diagram one y,
  { rw ←ι_preserves_colimits_iso_hom,
    simp [h] },
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ =
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ :=
    (congr_arg (colim.map (diagram_iso_parallel_pair diagram).hom
    ≫ (colimit.iso_colimit_cocone (types.coequalizer_colimit _ _)).hom) this : _),
  simp only [eq_to_hom_refl, types_comp_apply, colimit.ι_map_assoc,
    diagram_iso_parallel_pair_hom_app, colimit.iso_colimit_cocone_ι_hom, types_id_apply] at this,
  exact quot.eq.1 this,
  apply_instance
end

lemma ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
  𝖣 .ι i x = 𝖣 .ι j y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
begin
  split,
  { delta glue_data.ι,
    simp_rw ← multicoequalizer.ι_sigma_π,
    intro h,
    rw ← (show _ = sigma.mk i x,
      from concrete_category.congr_hom (sigma_iso_sigma D.U).inv_hom_id _),
    rw ← (show _ = sigma.mk j y,
      from concrete_category.congr_hom (sigma_iso_sigma D.U).inv_hom_id _),
    change inv_image D.rel (sigma_iso_sigma D.U).hom _ _,
    simp only [Top.sigma_iso_sigma_inv_apply],
    rw ← (inv_image.equivalence _ _ D.rel_equiv).eqv_gen_iff,
    refine eqv_gen.mono _ (D.eqv_gen_of_π_eq h : _),
    rintros _ _ ⟨x⟩,
    rw ← (show (sigma_iso_sigma _).inv _ = x,
      from concrete_category.congr_hom (sigma_iso_sigma _).hom_inv_id x),
    generalize : (sigma_iso_sigma D.V).hom x = x',
    obtain ⟨⟨i,j⟩,y⟩ := x',
    unfold inv_image multispan_index.fst_sigma_map multispan_index.snd_sigma_map,
    simp only [opens.inclusion_to_fun, Top.comp_app, sigma_iso_sigma_inv_apply,
      category_theory.limits.colimit.ι_desc_apply, cofan.mk_ι_app,
      sigma_iso_sigma_hom_ι_apply, continuous_map.to_fun_eq_coe],
    erw [sigma_iso_sigma_hom_ι_apply, sigma_iso_sigma_hom_ι_apply],
    exact or.inr ⟨y, by { dsimp [glue_data.diagram], simp }⟩ },
  { rintro (⟨⟨⟩⟩|⟨z,e₁,e₂⟩),
    refl, dsimp only at *, subst e₁, subst e₂, simp }
end

lemma ι_injective (i : D.J) : function.injective (𝖣 .ι i) :=
begin
  intros x y h,
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩|⟨_,e₁,e₂⟩),
  { refl },
  { dsimp only at *, cases e₁, cases e₂, simp }
end

instance ι_mono (i : D.J) : mono (𝖣 .ι i) :=
(Top.mono_iff_injective _).mpr (D.ι_injective _)

local attribute [elementwise] is_iso.hom_inv_id is_iso.inv_hom_id

lemma image_inter (i j : D.J) :
  set.range (𝖣 .ι i) ∩ set.range (𝖣 .ι j) = set.range (D.f i j ≫ 𝖣 .ι _) :=
begin
  ext x,
  split,
  { rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩,
    obtain (⟨⟨⟩⟩|⟨y,e₁,e₂⟩) := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm),
    { exact ⟨inv (D.f i i) x₁, by simp [eq₁]⟩ },
    { dsimp only at *, substs e₁ eq₁, exact ⟨y, by simp⟩ } },
  { rintro ⟨x, hx⟩,
    exact ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), by simp [← hx]⟩⟩ }
end

lemma preimage_range (i j : D.J) :
  𝖣 .ι j ⁻¹' (set.range (𝖣 .ι i)) = set.range (D.f j i) :=
by rw [← set.preimage_image_eq (set.range (D.f j i)) (D.ι_injective j), ← set.image_univ,
      ← set.image_univ, ←set.image_comp, ←coe_comp, set.image_univ,set.image_univ,
      ← image_inter, set.preimage_range_inter]

lemma preimage_image_eq_image (i j : D.J) (U : set (𝖣 .U i)) :
  𝖣 .ι j ⁻¹' (𝖣 .ι i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) :=
begin
  have : D.f _ _ ⁻¹' (𝖣 .ι j ⁻¹' (𝖣 .ι i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U,
  { ext x,
    conv_rhs { rw ← set.preimage_image_eq U (D.ι_injective _) },
    generalize : 𝖣 .ι i '' U = U',
    simp },
  rw [← this, set.image_preimage_eq_inter_range],
  symmetry,
  apply set.inter_eq_self_of_subset_left,
  rw ← D.preimage_range i j,
  exact set.preimage_mono (set.image_subset_range _ _),
end

lemma preimage_image_eq_image' (i j : D.J) (U : set (𝖣 .U i)) :
𝖣 .ι j ⁻¹' (𝖣 .ι i '' U) = (D.t i j ≫ D.f _ _) '' ((D.f _ _) ⁻¹' U) :=
begin
  convert D.preimage_image_eq_image i j U using 1,
  rw [coe_comp, coe_comp, ← set.image_image],
  congr' 1,
  rw [← set.eq_preimage_iff_image_eq, set.preimage_preimage],
  change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _,
  rw 𝖣 .t_inv_assoc,
  rw ← is_iso_iff_bijective,
  apply (forget Top).map_is_iso
end

lemma open_image_open (i : D.J) (U : opens (𝖣 .U i)) : is_open (𝖣 .ι i '' U) :=
begin
  rw is_open_iff,
  intro j,
  rw preimage_image_eq_image,
  apply (D.f_open _ _).is_open_map,
  apply (D.t j i ≫ D.f i j).continuous_to_fun.is_open_preimage,
  exact U.property
end

lemma ι_open_embedding (i : D.J) : open_embedding (𝖣 .ι i) :=
open_embedding_of_continuous_injective_open
  (𝖣 .ι i).continuous_to_fun (D.ι_injective i) (λ U h, D.open_image_open i ⟨U, h⟩)

end glue_data

end Top
