/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.basic
import category_theory.filtered
import category_theory.limits.types

/-!
# Preservation of filtered colimits.

Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits).
-/

open category_theory
open category_theory.functor

namespace category_theory.limits

universes v u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]

variables {J : Type v} [small_category J] {K : J ⥤ C}

class preserves_filtered_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_filtered_colimits : Π (J : Type v) [small_category J] [is_filtered J],
  preserves_colimits_of_shape J F)

attribute [instance, priority 100] preserves_filtered_colimits.preserves_filtered_colimits

namespace types

instance id_preserves_filtered_colimits : preserves_filtered_colimits (𝟭 (Type v)) :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K, by apply_instance } }

noncomputable
instance const_preserves_filtered_colimits (α : Type v) :
  preserves_filtered_colimits ((const (Type v)).obj α) :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K,
    preserves_colimit_of_is_iso (types.colimit_cocone_is_colimit _) (types.colimit_cocone_is_colimit _)
    begin
      apply (is_iso_equiv_bijective _).inv_fun,
      split,
      { -- injectivity
        rintros ⟨jx, px⟩ ⟨jy, py⟩ e,
        dsimp at e,
        subst e,
        exact quot.sound ⟨is_filtered.sup jx jy,
          is_filtered.left_to_sup _ _, is_filtered.right_to_sup _ _, rfl⟩, },
      { -- surjectivity
        intro p,
        exact ⟨quot.mk _ ⟨is_filtered.nonempty.some, p⟩, rfl⟩, },
    end } }

def star_iso : types.star ≅ (const (Type v)).obj punit.{v+1} :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

noncomputable
instance star_preserves_filtered_colimits : preserves_filtered_colimits types.star.{v} :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K, preserves_colimit_of_iso_right star_iso.symm, } }

def Prop_iso : types.Prop ≅ (const (Type v)).obj (ulift Prop) :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

noncomputable
instance Prop_preserves_filtered_colimits : preserves_filtered_colimits types.Prop.{v} :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K, preserves_colimit_of_iso_right Prop_iso.symm, } }

@[simps]
def prod (F G : C ⥤ Type v) : C ⥤ Type v :=
{ obj := λ X, F.obj X × G.obj X,
  map := λ X Y f p, (F.map f p.1, G.map f p.2) }

noncomputable
instance preserves_filtered_colimits_prod [has_colimits C] (F G : C ⥤ Type v)
  [preserves_filtered_colimits F] [preserves_filtered_colimits G] :
  preserves_filtered_colimits (prod F G) :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K,
    preserves_colimit_of_is_iso (colimit.is_colimit _) (types.colimit_cocone_is_colimit _)
    begin
      apply (is_iso_equiv_bijective _).inv_fun,
      split,
      { -- injectivity
        rintros ⟨jx, ⟨x₁,x₂⟩⟩ ⟨jy, ⟨y₁,y₂⟩⟩ h,
        injection h with h₁ h₂, clear h,
        dsimp at h₁ h₂,
        change (F.map_cocone (colimit.cocone K)).ι.app jx x₁ =
          ((F.map_cocone (colimit.cocone K)).ι.app jy y₁ : _) at h₁,
        change (G.map_cocone (colimit.cocone K)).ι.app jx x₂ =
          ((G.map_cocone (colimit.cocone K)).ι.app jy y₂ : _) at h₂,
        rw types.filtered_colimit.is_colimit_eq_iff _ (preserves_colimit.preserves (colimit.is_colimit K)) at h₁,
        swap, apply_instance,
        rw types.filtered_colimit.is_colimit_eq_iff _ (preserves_colimit.preserves (colimit.is_colimit K)) at h₂,
        swap, apply_instance,
        rcases h₁ with ⟨j₁, ix₁, iy₁, e₁⟩,
        rcases h₂ with ⟨j₂, ix₂, iy₂, e₂⟩,
        obtain ⟨j, i₁, i₂, h₁, h₂⟩ := is_filtered.bowtie ix₁ ix₂ iy₁ iy₂,
        refine quot.sound ⟨j, ix₁ ≫ i₁, iy₂ ≫ i₂, _⟩,
        ext; dsimp,
        { erw [K.map_comp, F.map_comp, types_comp_apply, e₁,
            ←h₂, K.map_comp, F.map_comp, types_comp_apply],
          refl, },
        { erw [h₁, K.map_comp, G.map_comp, types_comp_apply,
            K.map_comp, G.map_comp, types_comp_apply, ←e₂],
          refl, }, },
      { -- surjectivity
        rintro ⟨x₁, x₂⟩,
        change (F.map_cocone _).X at x₁,
        change (G.map_cocone _).X at x₂,
        let e₁ := preserves_colimit_iso (colimit.is_colimit K) (types.colimit_cocone_is_colimit (K ⋙ F)),
        let e₂ := preserves_colimit_iso (colimit.is_colimit K) (types.colimit_cocone_is_colimit (K ⋙ G)),
        rcases h₁ : e₁.hom x₁ with ⟨j₁, y₁⟩,
        rcases h₂ : e₂.hom x₂ with ⟨j₂, y₂⟩,
        fsplit,
        { exact quot.mk _ ⟨(is_filtered.sup j₁ j₂),
            ⟨(K ⋙ F).map (is_filtered.left_to_sup j₁ j₂) y₁,
             (K ⋙ G).map (is_filtered.right_to_sup j₁ j₂) y₂⟩⟩, },
        { simp only [functor.map_cocone_ι, functor.comp_map, prod.mk.inj_iff, prod_map,
            limits.types.colimit_cocone_is_colimit_desc, limits.colimit.cocone_ι],
          fsplit,
          { apply e₁.to_equiv.injective, simp [h₁, e₁],
            erw map_ι_comp_preserves_colimit_iso_hom_apply,
            exact quot.sound ⟨_, 𝟙 _, is_filtered.left_to_sup _ _, by simp⟩, },
          { apply e₂.to_equiv.injective, simp [h₂, e₂],
            erw map_ι_comp_preserves_colimit_iso_hom_apply,
            exact quot.sound ⟨_, 𝟙 _, is_filtered.right_to_sup _ _, by simp⟩, }, }, }
    end } }

def diagonal_iso_prod_id_id : types.diagonal ≅ prod (𝟭 _) (𝟭 _) :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

noncomputable
instance diagonal_preserves_filtered_colimits : preserves_filtered_colimits types.diagonal.{v} :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K, preserves_colimit_of_iso_right diagonal_iso_prod_id_id.symm, } }

def triple_diagonal_iso : types.triple_diagonal ≅ prod (𝟭 _) (prod (𝟭 _) (𝟭 _)) :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

noncomputable
instance triple_diagonal_preserves_filtered_colimits : preserves_filtered_colimits types.triple_diagonal.{v} :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K, preserves_colimit_of_iso_right triple_diagonal_iso.symm, } }

@[simps]
def equalizer {F G : C ⥤ Type v} (α β : F ⟶ G) : C ⥤ Type v :=
{ obj := λ X, { x : F.obj X // α.app X x = β.app X x },
  map := λ X Y f p, ⟨F.map f p.1, by rw [functor_to_types.naturality, p.2, functor_to_types.naturality] ⟩ }

noncomputable
instance preserves_filtered_colimits_equalizer [has_colimits C] {F G : C ⥤ Type v}
  [preserves_filtered_colimits F] [preserves_filtered_colimits G]
  (α β : F ⟶ G) :
  preserves_filtered_colimits (equalizer α β) :=
{ preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
  { preserves_colimit := λ K,
    preserves_colimit_of_is_iso (colimit.is_colimit _) (types.colimit_cocone_is_colimit _)
    begin
      apply (is_iso_equiv_bijective _).inv_fun,
      split,
      { -- injectivity
        rintros ⟨jx, ⟨x₁,x₂⟩⟩ ⟨jy, ⟨y₁,y₂⟩⟩ h,
        dsimp at h,
        injection h with h', clear h,
        dsimp at h',

        change (F.map_cocone (colimit.cocone K)).ι.app jx x₁ =
          ((F.map_cocone (colimit.cocone K)).ι.app jy y₁ : _) at h',
        rw types.filtered_colimit.is_colimit_eq_iff _ (preserves_colimit.preserves (colimit.is_colimit K)) at h',
        swap, apply_instance,

        obtain ⟨j, ix, iy, e⟩ := h',
        exact quot.sound ⟨j, ix, iy, subtype.eq e⟩, },
      { -- surjectivity
        rintro ⟨x, h⟩,
        change (F.map_cocone _).X at x,
        let eF := preserves_colimit_iso (colimit.is_colimit K) (types.colimit_cocone_is_colimit (K ⋙ F)),
        let eG := preserves_colimit_iso (colimit.is_colimit K) (types.colimit_cocone_is_colimit (K ⋙ G)),
        obtain ⟨j, y, w⟩ := jointly_surjective _ _ (eF.hom x),
        have w' := congr_arg eF.inv w,
        simp at w',
        rw [←w'] at h,
        simp [eF] at h,
        erw ι_comp_preserves_colimit_iso_inv_apply at h,
        erw functor_to_types.naturality at h,
        erw functor_to_types.naturality at h,
        erw ←ι_comp_preserves_colimit_iso_inv_apply (colimit.is_colimit K) (types.colimit_cocone_is_colimit (K ⋙ G)) at h,
        erw ←ι_comp_preserves_colimit_iso_inv_apply (colimit.is_colimit K) (types.colimit_cocone_is_colimit (K ⋙ G)) at h,

        fsplit,
        {
          apply quot.mk,
          use j,
          dsimp,
          fsplit, exact y,

          -- so close! perhaps we need to move `j` a bit further to the right to make
          -- `G.map ((limits.colimit.cocone K).ι.app j)` an iso?
          sorry,
           },
        { dsimp,
          apply subtype.eq,
          dsimp,
          apply eF.to_equiv.injective, simp [h],
          erw map_ι_comp_preserves_colimit_iso_hom_apply,
          exact w, },
        sorry, }
    end } }

-- noncomputable
-- instance diagonal_preserves_filtered_colimits' : preserves_filtered_colimits types.diagonal.{v} :=
-- { preserves_filtered_colimits := λ J 𝒥 ℱ, by exactI
--   { preserves_colimit := λ K,
--     preserves_colimit_of_is_iso (types.colimit_cocone_is_colimit _) (types.colimit_cocone_is_colimit _)
--     begin
--       apply (is_iso_equiv_bijective _).inv_fun,
--       split,
--       { -- injectivity
--         rintros ⟨jx, ⟨x₁,x₂⟩⟩ ⟨jy, ⟨y₁,y₂⟩⟩ h,
--         injection h with h₁ h₂, clear h,
--         rw types.filtered_colimit.is_colimit_eq_iff K (types.colimit_cocone_is_colimit _) at h₁ h₂,
--         rcases h₁ with ⟨j₁, ix₁, iy₁, e₁⟩,
--         rcases h₂ with ⟨j₂, ix₂, iy₂, e₂⟩,
--         obtain ⟨j, i₁, i₂, h₁, h₂⟩ := is_filtered.bowtie ix₁ ix₂ iy₁ iy₂,
--         refine quot.sound ⟨j, ix₁ ≫ i₁, iy₂ ≫ i₂, _⟩,
--         ext; dsimp,
--         { rw [K.map_comp, types_comp_apply, e₁, ←h₂, K.map_comp, types_comp_apply], },
--         { rw [h₁, K.map_comp, types_comp_apply, K.map_comp, types_comp_apply, ←e₂], }, },
--       { -- surjectivity
--         rintro ⟨⟨j₁, x₁⟩, ⟨j₂, x₂⟩⟩,
--         fsplit,
--         { exact quot.mk _ ⟨(is_filtered.sup j₁ j₂),
--             ⟨K.map (is_filtered.left_to_sup j₁ j₂) x₁,
--              K.map (is_filtered.right_to_sup j₁ j₂) x₂⟩⟩, },
--         { simp only [functor.map_cocone_ι, limits.types.colimit_cocone_is_colimit_desc,
--             limits.types.colimit_cocone_ι_app, id.def, prod.mk.inj_iff, types.diagonal_map],
--           fsplit,
--           { exact quot.sound ⟨_, 𝟙 _, is_filtered.left_to_sup _ _, by simp⟩, },
--           { exact quot.sound ⟨_, 𝟙 _, is_filtered.right_to_sup _ _, by simp⟩, }, }, },
--     end } }

end types

end category_theory.limits
