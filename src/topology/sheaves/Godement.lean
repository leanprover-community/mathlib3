/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import topology.sheaves.sheaf
import topology.sheaves.limits
import topology.sheaves.skyscraper
import topology.sheaves.stalks
import topology.sheaves.construction.prod

/-!
# Godement resolution

For a presheaf `𝓕 : (opens X)ᵒᵖ ⥤ C`, we can embedded `𝓕` into a sheaf `∏ₓ skyscraper(𝓕ₓ)` where
`x` ranges over `X` and `𝓕 ⟶ ∏ₓ skyscraper(𝓕ₓ)` is mono.

## Main definition
* `godement_presheaf`: for a presheaf `𝓕`, its Godement presheaf is `∏ₓ skyscraper(𝓕ₓ)`
* `to_godement_presheaf`: the canonical map `𝓕 ⟶ godement_presheaf 𝓕` sending `s : 𝓕(U)` to a
  bundle of stalks `x ↦ sₓ`.
-/

noncomputable theory

section presheaf

open Top
open topological_space
open category_theory
open category_theory.limits

universes u v

variables {X : Top.{u}} {C : Type u} [category.{u} C]
variables [has_limits C] [has_colimits C]
variables [Π (x : X) (U : opens X), decidable (x ∈ U)]
variables (𝓕 : presheaf C X) (𝓖 : sheaf C X)

/--
The `godement_presheaf` for a presheaf `𝓕` is defined as a product presheaf `∏ₓ skyscraper(𝓕ₓ)`
-/
def godement_presheaf : presheaf C X :=
∏ (λ x, skyscraper_presheaf x (𝓕.stalk x) : X → presheaf C X)

/--
There is a morphism `𝓕 ⟶ godement_presheaf(𝓕)` by lifting the unit of
skyscraper presheaf functor and stalk functor.
-/
def to_godement_presheaf : 𝓕 ⟶ godement_presheaf 𝓕 :=
pi.lift $ λ p₀, (skyscraper_presheaf_stalk_adjunction p₀).unit.app 𝓕

/--
sections of `𝓕` can be embedded into sections of product of skyscraper presheaves
-/
def to_godement_presheaf_sections (U : (opens X)ᵒᵖ) :
  𝓕.obj U ⟶ ∏ λ (x : X), (skyscraper_presheaf x (𝓕.stalk x)).obj U :=
(to_godement_presheaf 𝓕).app U ≫ (Top.presheaf.section_product_equiv_product_section _ _).hom

lemma to_godement_presheaf_comp_limit_obj_iso_limit_comp_evaluation (U : (opens X)ᵒᵖ) :
  (to_godement_presheaf 𝓕).app U ≫ (limit_obj_iso_limit_comp_evaluation
    (discrete.functor (λ x, skyscraper_presheaf x (𝓕.stalk x))) U).hom =
  to_godement_presheaf_sections 𝓕 U ≫ lim_map (discrete.nat_trans $ λ x, eq_to_hom rfl) :=
begin
  rw [to_godement_presheaf_sections, category.assoc],
  congr' 1,
  ext1 ⟨j⟩,
  simp only [Top.presheaf.section_product_equiv_product_section, iso.trans_hom, functor.map_iso_hom,
    lim_map_eq_lim_map, eq_to_hom_refl, category.assoc, lim_map_π, discrete.nat_trans_app,
    category.comp_id, discrete.nat_iso_hom_app, iso.refl_hom],
end

lemma germ_eq_to_godement_presheaf_sections_comp_pi {U : (opens X)ᵒᵖ} (p : U.unop) :
  presheaf.germ 𝓕 p = to_godement_presheaf_sections 𝓕 U ≫ pi.π _ p ≫ eq_to_hom (if_pos p.2) :=
begin
  dunfold to_godement_presheaf_sections to_godement_presheaf
    presheaf.section_product_equiv_product_section,
  simp only [iso.trans_hom, functor.map_iso_hom, lim_map_eq_lim_map, category.assoc],
  erw [←category.assoc (lim_map _), lim_map_π],
  simp only [skyscraper_presheaf_stalk_adjunction_unit, iso.refl_hom,
    stalk_skyscraper_presheaf_adjunction_auxs.unit_app, discrete.nat_iso_hom_app, category.comp_id,
    limit_obj_iso_limit_comp_evaluation_hom_π_assoc, limit.lift_π_app_assoc, fan.mk_π_app,
    stalk_skyscraper_presheaf_adjunction_auxs.to_skyscraper_presheaf_app],
  symmetry,
  erw [dif_pos, category.assoc, category.assoc, eq_to_hom_trans, category.id_comp, eq_to_hom_refl,
    category.comp_id],
  refl,
  exact p.2,
end

lemma godement_presheaf_is_sheaf : (godement_presheaf 𝓕).is_sheaf :=
limit_is_sheaf _ $ λ ⟨x⟩, (skyscraper_sheaf x _).2

/--
The `godement_presheaf` for any sheaf `𝓖` is a sheaf.
-/
def godement_sheaf : sheaf C X :=
⟨godement_presheaf 𝓖.1, godement_presheaf_is_sheaf _⟩

/--
There is a morphism `𝓖 ⟶ godement_sheaf(𝓖)` by lifting the unit of
skyscraper presheaf functor and stalk functor.
-/
def to_godement_sheaf : 𝓖 ⟶ godement_sheaf 𝓖 :=
⟨to_godement_presheaf 𝓖.1⟩


section concrete

variables [concrete_category.{u} C] [preserves_limits (forget C)]
variables [reflects_isomorphisms (forget C)]

local notation `sheaf_in_Type` := category_theory.presheaf.Sheaf_in_Type
  (opens.grothendieck_topology X) (forget C)

lemma stalk_bundles_eq0 (U : (opens X)ᵒᵖ) (x y : (sheaf_in_Type .obj 𝓖).1.obj U)
  (eq1 : (sheaf_in_Type .map (to_godement_sheaf 𝓖)).1.app U x =
      (sheaf_in_Type .map (to_godement_sheaf 𝓖)).1.app U y) :
  (forget C).map (to_godement_presheaf_sections 𝓖.presheaf U) x =
  (forget C).map (to_godement_presheaf_sections 𝓖.presheaf U) y :=
begin
  change (forget C).map ((to_godement_presheaf 𝓖.presheaf).app _) x =
    (forget C).map ((to_godement_presheaf 𝓖.presheaf).app _) y at eq1,
  dsimp only at eq1,
  have eq2 := congr_arg
    ((forget C).map (limit_obj_iso_limit_comp_evaluation (discrete.functor _) U).hom) eq1,
  dsimp only at eq2,
  change ((forget C).map _ ≫ (forget C).map _) x = ((forget C).map _ ≫ (forget C).map _) y at eq2,
  rw [←(forget C).map_comp, to_godement_presheaf_comp_limit_obj_iso_limit_comp_evaluation] at eq2,
  simp only [eq_to_hom_refl, comp_apply] at eq2,
  set α : discrete.functor (λ x, skyscraper_presheaf x (𝓖.presheaf.stalk x)) ⋙
    (evaluation (opens X)ᵒᵖ C).obj U ⟶
  discrete.functor (λ x, (skyscraper_presheaf x (𝓖.presheaf.stalk x)).obj U) :=
  discrete.nat_trans (λ x, eq_to_hom rfl),

  have eq3 := congr_arg ((forget C).map (lim_map α)) eq2,
  change ((forget C).map _ ≫ (forget C).map _) x = ((forget C).map _ ≫ (forget C).map _) y at eq3,
  rwa [←(forget C).map_comp, category.assoc, show lim_map _ ≫ lim_map α = lim_map (𝟙 _), from _,
    show lim_map (𝟙 _) = 𝟙 _, from _, category.comp_id] at eq3,
  { ext1, simp only [lim_map_π, nat_trans.id_app, category.comp_id, category.id_comp], },
  { ext1,
    simp only [category.assoc, lim_map_π, discrete.nat_trans_app, eq_to_hom_refl, category.comp_id,
    nat_trans.id_app], },
end

lemma stalk_bundles_eq (U : (opens X)ᵒᵖ) (x y : (sheaf_in_Type .obj 𝓖).1.obj U)
  (eq1 : (sheaf_in_Type .map (to_godement_sheaf 𝓖)).1.app U x =
      (sheaf_in_Type .map (to_godement_sheaf 𝓖)).1.app U y) (p : U.unop) :
  (forget C).map (𝓖.presheaf.germ p) x = (forget C).map (𝓖.presheaf.germ p) y :=
begin
  classical,
  have eq1' := stalk_bundles_eq0 𝓖 U x y eq1,
  rw germ_eq_to_godement_presheaf_sections_comp_pi,
  swap, apply_instance, swap, intros, apply_instance,
  simp only [forget_map_eq_coe, comp_apply] at eq1' ⊢,
  rw [eq1'],
end

instance mono_to_godement_sheaf [preserves_filtered_colimits (forget C)] :
  mono $ to_godement_sheaf 𝓖 :=
begin
  rw presheaf.mono_iff_stalk_mono,
  intros x,
  change mono ((presheaf.stalk_functor C x).map (to_godement_presheaf 𝓖.1)),
  rw concrete_category.mono_iff_injective_of_preserves_pullback,
  exact (presheaf.app_injective_iff_stalk_functor_map_injective (to_godement_presheaf 𝓖.1)).mpr
    (λ U x y H, presheaf.section_ext _ _ _ _ (λ p, stalk_bundles_eq 𝓖 (opposite.op U) x y H p)) x,
end

end concrete

end presheaf
