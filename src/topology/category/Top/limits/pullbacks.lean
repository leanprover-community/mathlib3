/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import topology.category.Top.limits.products
import category_theory.concrete_category.elementwise

/-!
# Pullbacks in the category of topological spaces.

-/

open topological_space
open category_theory
open category_theory.limits

universes u v w

noncomputable theory

namespace Top

variables {J : Type v} [small_category J]

section pullback

variables {X Y Z : Top.{u}}

/-- The first projection from the pullback. -/
abbreviation pullback_fst (f : X ⟶ Z) (g : Y ⟶ Z) : Top.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
⟨prod.fst ∘ subtype.val⟩

/-- The second projection from the pullback. -/
abbreviation pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z) : Top.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
⟨prod.snd ∘ subtype.val⟩

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) : pullback_cone f g :=
pullback_cone.mk (pullback_fst f g) (pullback_snd f g) (by { ext ⟨x, h⟩, simp [h] })

/-- The constructed cone is a limit. -/
def pullback_cone_is_limit (f : X ⟶ Z) (g : Y ⟶ Z) :
  is_limit (pullback_cone f g) := pullback_cone.is_limit_aux' _
begin
  intro s,
  split, swap,
  exact { to_fun := λ x, ⟨⟨s.fst x, s.snd x⟩,
    by simpa using concrete_category.congr_hom s.condition x⟩ },
  refine ⟨_,_,_⟩,
  { ext, delta pullback_cone, simp },
  { ext, delta pullback_cone, simp },
  { intros m h₁ h₂,
    ext x,
    { simpa using concrete_category.congr_hom h₁ x },
    { simpa using concrete_category.congr_hom h₂ x } }
end

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullback_iso_prod_subtype (f : X ⟶ Z) (g : Y ⟶ Z) :
  pullback f g ≅ Top.of { p : X × Y // f p.1 = g p.2 } :=
(limit.is_limit _).cone_point_unique_up_to_iso (pullback_cone_is_limit f g)

@[simp, reassoc] lemma pullback_iso_prod_subtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).inv ≫ pullback.fst = pullback_fst f g :=
by simpa [pullback_iso_prod_subtype]

@[simp] lemma pullback_iso_prod_subtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
  (x : { p : X × Y // f p.1 = g p.2 }) :
  (pullback.fst : pullback f g ⟶ _) ((pullback_iso_prod_subtype f g).inv x) = (x : X × Y).fst :=
concrete_category.congr_hom (pullback_iso_prod_subtype_inv_fst f g) x

@[simp, reassoc] lemma pullback_iso_prod_subtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).inv ≫ pullback.snd = pullback_snd f g :=
by simpa [pullback_iso_prod_subtype]

@[simp] lemma pullback_iso_prod_subtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z)
  (x : { p : X × Y // f p.1 = g p.2 }) :
  (pullback.snd : pullback f g ⟶ _) ((pullback_iso_prod_subtype f g).inv x) = (x : X × Y).snd :=
concrete_category.congr_hom (pullback_iso_prod_subtype_inv_snd f g) x

lemma pullback_iso_prod_subtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).hom ≫ pullback_fst f g = pullback.fst :=
by rw [←iso.eq_inv_comp, pullback_iso_prod_subtype_inv_fst]

lemma pullback_iso_prod_subtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).hom ≫ pullback_snd f g = pullback.snd :=
by rw [←iso.eq_inv_comp, pullback_iso_prod_subtype_inv_snd]

@[simp] lemma pullback_iso_prod_subtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z}
  (x : pullback f g) : (pullback_iso_prod_subtype f g).hom x =
    ⟨⟨(pullback.fst : pullback f g ⟶ _) x, (pullback.snd : pullback f g ⟶ _) x⟩,
      by simpa using concrete_category.congr_hom pullback.condition x⟩ :=
begin
  ext,
  exacts [concrete_category.congr_hom (pullback_iso_prod_subtype_hom_fst f g) x,
    concrete_category.congr_hom (pullback_iso_prod_subtype_hom_snd f g) x]
end

lemma pullback_topology {X Y Z : Top.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback f g).topological_space =
    induced (pullback.fst : pullback f g ⟶ _) X.topological_space ⊓
      induced (pullback.snd : pullback f g ⟶ _) Y.topological_space :=
begin
  let homeo := homeo_of_iso (pullback_iso_prod_subtype f g),
  refine homeo.inducing.induced.trans _,
  change induced homeo (induced _ (_ ⊓ _)) = _,
  simpa [induced_compose]
end

lemma range_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  set.range (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) =
  { x | (limits.prod.fst ≫ f) x = (limits.prod.snd ≫ g) x } :=
begin
  ext x,
  split,
  { rintros ⟨y, rfl⟩,
    simp only [←comp_apply, set.mem_set_of_eq],
    congr' 1,
    simp [pullback.condition] },
  { intro h,
    use (pullback_iso_prod_subtype f g).inv ⟨⟨_, _⟩, h⟩,
    apply concrete.limit_ext,
    rintro ⟨⟨⟩⟩; simp, }
end

lemma inducing_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inducing ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
⟨by simp [prod_topology, pullback_topology, induced_compose, ←coe_comp]⟩

lemma embedding_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  embedding ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
⟨inducing_pullback_to_prod f g, (Top.mono_iff_injective _).mp infer_instance⟩

/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
lemma range_pullback_map {W X Y Z S T : Top} (f₁ : W ⟶ S) (f₂ : X ⟶ S)
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : mono i₃]
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  set.range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
    (pullback.fst : pullback g₁ g₂ ⟶ _) ⁻¹' (set.range i₁) ∩
      (pullback.snd : pullback g₁ g₂ ⟶ _) ⁻¹' (set.range i₂) :=
begin
  ext,
  split,
  { rintro ⟨y, rfl⟩, simp, },
  rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩,
  have : f₁ x₁ = f₂ x₂,
  { apply (Top.mono_iff_injective _).mp H₃,
    simp only [←comp_apply, eq₁, eq₂],
    simp only [comp_apply, hx₁, hx₂],
    simp only [←comp_apply, pullback.condition] },
  use (pullback_iso_prod_subtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩,
  apply concrete.limit_ext,
  rintros (_|_|_),
  { simp only [Top.comp_app, limit.lift_π_apply, category.assoc, pullback_cone.mk_π_app_one,
      hx₁, pullback_iso_prod_subtype_inv_fst_apply, subtype.coe_mk],
    simp only [← comp_apply],
    congr,
    apply limit.w _ walking_cospan.hom.inl },
  { simp [hx₁] },
  { simp [hx₂] },
end

lemma pullback_fst_range {X Y S : Top} (f : X ⟶ S) (g : Y ⟶ S) :
  set.range (pullback.fst : pullback f g ⟶ _) = { x : X | ∃ y : Y, f x = g y} :=
begin
  ext x,
  split,
  { rintro ⟨y, rfl⟩,
    use (pullback.snd : pullback f g ⟶ _) y,
    exact concrete_category.congr_hom pullback.condition y },
  { rintro ⟨y, eq⟩,
    use (Top.pullback_iso_prod_subtype f g).inv ⟨⟨x, y⟩, eq⟩,
    simp },
end

lemma pullback_snd_range {X Y S : Top} (f : X ⟶ S) (g : Y ⟶ S) :
  set.range (pullback.snd : pullback f g ⟶ _) = { y : Y | ∃ x : X, f x = g y} :=
begin
  ext y,
  split,
  { rintro ⟨x, rfl⟩,
    use (pullback.fst : pullback f g ⟶ _) x,
    exact concrete_category.congr_hom pullback.condition x },
  { rintro ⟨x, eq⟩,
    use (Top.pullback_iso_prod_subtype f g).inv ⟨⟨x, y⟩, eq⟩,
    simp },
end

/--
If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗      ↗
  X  ⟶  Z
-/
lemma pullback_map_embedding_of_embeddings {W X Y Z S T : Top}
  (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z}
  (H₁ : embedding i₁) (H₂ : embedding i₂) (i₃ : S ⟶ T)
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
begin
  refine embedding_of_embedding_compose (continuous_map.continuous_to_fun _)
    (show continuous (prod.lift pullback.fst pullback.snd : pullback g₁ g₂ ⟶ Y ⨯ Z), from
      continuous_map.continuous_to_fun _) _,
  suffices : embedding
    (prod.lift pullback.fst pullback.snd ≫ limits.prod.map i₁ i₂ : pullback f₁ f₂ ⟶ _),
  { simpa [←coe_comp] using this },
  rw coe_comp,
  refine embedding.comp (embedding_prod_map H₁ H₂)
    (embedding_pullback_to_prod _ _)
end

/--
If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.
  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗       ↗
  X  ⟶  Z
-/
lemma pullback_map_open_embedding_of_open_embeddings {W X Y Z S T : Top}
  (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z}
  (H₁ : open_embedding i₁) (H₂ : open_embedding i₂) (i₃ : S ⟶ T) [H₃ : mono i₃]
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  open_embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
begin
  split,
  { apply pullback_map_embedding_of_embeddings
      f₁ f₂ g₁ g₂ H₁.to_embedding H₂.to_embedding i₃ eq₁ eq₂ },
  { rw range_pullback_map,
    apply is_open.inter; apply continuous.is_open_preimage,
    continuity,
    exacts [H₁.open_range, H₂.open_range] }
end

lemma snd_embedding_of_left_embedding {X Y S : Top}
  {f : X ⟶ S} (H : embedding f) (g : Y ⟶ S) :
  embedding ⇑(pullback.snd : pullback f g ⟶ Y) :=
begin
  convert (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).embedding.comp
    (pullback_map_embedding_of_embeddings f g (𝟙 _) g H
      (homeo_of_iso (iso.refl _)).embedding (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

lemma fst_embedding_of_right_embedding {X Y S : Top}
  (f : X ⟶ S) {g : Y ⟶ S} (H : embedding g) :
  embedding ⇑(pullback.fst : pullback f g ⟶ X) :=
begin
  convert (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).embedding.comp
    (pullback_map_embedding_of_embeddings f g f (𝟙 _)
      (homeo_of_iso (iso.refl _)).embedding H (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

lemma embedding_of_pullback_embeddings {X Y S : Top}
  {f : X ⟶ S} {g : Y ⟶ S} (H₁ : embedding f) (H₂ : embedding g) :
  embedding (limit.π (cospan f g) walking_cospan.one) :=
begin
  convert H₂.comp (snd_embedding_of_left_embedding H₁ g),
  erw ←coe_comp,
  congr,
  exact (limit.w _ walking_cospan.hom.inr).symm
end

lemma snd_open_embedding_of_left_open_embedding {X Y S : Top}
  {f : X ⟶ S} (H : open_embedding f) (g : Y ⟶ S) :
  open_embedding ⇑(pullback.snd : pullback f g ⟶ Y) :=
begin
  convert (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).open_embedding.comp
    (pullback_map_open_embedding_of_open_embeddings f g (𝟙 _) g H
      (homeo_of_iso (iso.refl _)).open_embedding (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

lemma fst_open_embedding_of_right_open_embedding {X Y S : Top}
  (f : X ⟶ S) {g : Y ⟶ S} (H : open_embedding g) :
  open_embedding ⇑(pullback.fst : pullback f g ⟶ X) :=
begin
  convert (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).open_embedding.comp
    (pullback_map_open_embedding_of_open_embeddings f g f (𝟙 _)
      (homeo_of_iso (iso.refl _)).open_embedding H (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
lemma open_embedding_of_pullback_open_embeddings {X Y S : Top}
  {f : X ⟶ S} {g : Y ⟶ S} (H₁ : open_embedding f) (H₂ : open_embedding g) :
  open_embedding (limit.π (cospan f g) walking_cospan.one) :=
begin
  convert H₂.comp (snd_open_embedding_of_left_open_embedding H₁ g),
  erw ←coe_comp,
  congr,
  exact (limit.w _ walking_cospan.hom.inr).symm
end

lemma fst_iso_of_right_embedding_range_subset {X Y S : Top} (f : X ⟶ S) {g : Y ⟶ S}
  (hg : embedding g) (H : set.range f ⊆ set.range g) : is_iso (pullback.fst : pullback f g ⟶ X) :=
begin
  let : (pullback f g : Top) ≃ₜ X :=
    (homeomorph.of_embedding _ (fst_embedding_of_right_embedding f hg)).trans
    { to_fun := coe,
      inv_fun := (λ x, ⟨x,
        by { rw pullback_fst_range, exact ⟨_, (H (set.mem_range_self x)).some_spec.symm⟩ }⟩),
      left_inv := λ ⟨_,_⟩, rfl,
      right_inv := λ x, rfl },
  convert is_iso.of_iso (iso_of_homeo this),
  ext,
  refl
end

lemma snd_iso_of_left_embedding_range_subset {X Y S : Top} {f : X ⟶ S} (hf : embedding f)
  (g : Y ⟶ S) (H : set.range g ⊆ set.range f) : is_iso (pullback.snd : pullback f g ⟶ Y) :=
begin
  let : (pullback f g : Top) ≃ₜ Y :=
    (homeomorph.of_embedding _ (snd_embedding_of_left_embedding hf g)).trans
    { to_fun := coe,
      inv_fun := (λ x, ⟨x,
        by { rw pullback_snd_range, exact ⟨_, (H (set.mem_range_self x)).some_spec⟩ }⟩),
      left_inv := λ ⟨_,_⟩, rfl,
      right_inv := λ x, rfl },
  convert is_iso.of_iso (iso_of_homeo this),
  ext,
  refl
end

lemma pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : set X) :
  (pullback.snd : pullback f g ⟶ _) '' ((pullback.fst : pullback f g ⟶ _) ⁻¹' U) =
    g ⁻¹' (f '' U) :=
begin
  ext x,
  split,
  { rintros ⟨y, hy, rfl⟩,
    exact ⟨(pullback.fst : pullback f g ⟶ _) y, hy,
    concrete_category.congr_hom pullback.condition y⟩ },
  { rintros ⟨y, hy, eq⟩,
    exact ⟨(Top.pullback_iso_prod_subtype f g).inv ⟨⟨_,_⟩, eq⟩, by simpa, by simp⟩ },
end

lemma pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : set Y) :
  (pullback.fst : pullback f g ⟶ _) '' ((pullback.snd : pullback f g ⟶ _) ⁻¹' U) =
    f ⁻¹' (g '' U) :=
begin
  ext x,
  split,
  { rintros ⟨y, hy, rfl⟩,
    exact ⟨(pullback.snd : pullback f g ⟶ _) y, hy,
    (concrete_category.congr_hom pullback.condition y).symm⟩ },
  { rintros ⟨y, hy, eq⟩,
    exact ⟨(Top.pullback_iso_prod_subtype f g).inv ⟨⟨_,_⟩,eq.symm⟩, by simpa, by simp⟩ },
end

end pullback



lemma coinduced_of_is_colimit {F : J ⥤ Top.{max v u}} (c : cocone F) (hc : is_colimit c) :
  c.X.topological_space = ⨆ j, (F.obj j).topological_space.coinduced (c.ι.app j) :=
begin
  let homeo := homeo_of_iso (hc.cocone_point_unique_up_to_iso (colimit_cocone_is_colimit F)),
  ext,
  refine homeo.symm.is_open_preimage.symm.trans (iff.trans _ is_open_supr_iff.symm),
  exact is_open_supr_iff
end

lemma colimit_topology (F : J ⥤ Top.{max v u}) :
  (colimit F).topological_space = ⨆ j, (F.obj j).topological_space.coinduced (colimit.ι F j) :=
coinduced_of_is_colimit _ (colimit.is_colimit F)

lemma colimit_is_open_iff (F : J ⥤ Top.{max v u}) (U : set ((colimit F : _) : Type (max v u))) :
  is_open U ↔ ∀ j, is_open (colimit.ι F j ⁻¹' U) :=
begin
  conv_lhs { rw colimit_topology F },
  exact is_open_supr_iff
end

lemma coequalizer_is_open_iff (F : walking_parallel_pair ⥤ Top.{u})
  (U : set ((colimit F : _) : Type u)) :
  is_open U ↔ is_open (colimit.ι F walking_parallel_pair.one ⁻¹' U) :=
begin
  rw colimit_is_open_iff.{u},
  split,
  { intro H, exact H _ },
  { intros H j,
    cases j,
    { rw ←colimit.w F walking_parallel_pair_hom.left,
      exact (F.map walking_parallel_pair_hom.left).continuous_to_fun.is_open_preimage _ H },
    { exact H } }
end

end Top
