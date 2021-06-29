/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import category_theory.limits.preserves.basic
import category_theory.limits.types
import category_theory.limits.shapes.wide_pullbacks
import tactic.elementwise

/-!
# Facts about (co)limits of functors into concrete categories
-/

universes w v u

open category_theory

namespace category_theory.limits

attribute [elementwise] cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w

local attribute [instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

section limits

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]
  {J : Type v} [small_category J] (F : J ⥤ C) [preserves_limit F (forget C)]

lemma concrete.to_product_injective_of_is_limit {D : cone F} (hD : is_limit D) :
  function.injective (λ (x : D.X) (j : J), D.π.app j x) :=
begin
  let E := (forget C).map_cone D,
  let hE : is_limit E := is_limit_of_preserves _ hD,
  let G := types.limit_cone (F ⋙ forget C),
  let hG := types.limit_cone_is_limit (F ⋙ forget C),
  let T : E.X ≅ G.X := hE.cone_point_unique_up_to_iso hG,
  change function.injective (T.hom ≫ (λ x j, G.π.app j x)),
  have h : function.injective T.hom,
  { intros a b h,
    suffices : T.inv (T.hom a) = T.inv (T.hom b), by simpa,
    rw h },
  suffices : function.injective (λ (x : G.X) j, G.π.app j x),
    by exact function.injective.comp this h,
  intros a b hh,
  exact subtype.ext hh,
end

lemma concrete.is_limit_ext {D : cone F} (hD : is_limit D) (x y : D.X) :
  (∀ j, D.π.app j x = D.π.app j y) → x = y :=
λ h, concrete.to_product_injective_of_is_limit _ hD (funext h)

lemma concrete.limit_ext [has_limit F] (x y : limit F) :
  (∀ j, limit.π F j x = limit.π F j y) → x = y :=
concrete.is_limit_ext F (limit.is_limit _) _ _

open wide_pullback
open wide_pullback_shape

lemma concrete.wide_pullback_ext {B : C} {ι : Type*} {X : ι → C} (f : Π j : ι, X j ⟶ B)
  [has_wide_pullback B X f] [preserves_limit (wide_cospan B X f) (forget C)]
  (x y : wide_pullback B X f) (h₀ : base f x = base f y)
  (h : ∀ j, π f j x = π f j y) : x = y :=
begin
  apply concrete.limit_ext,
  rintro (_|j),
  { exact h₀ },
  { apply h }
end

lemma concrete.wide_pullback_ext' {B : C} {ι : Type*} [nonempty ι]
  {X : ι → C} (f : Π j : ι, X j ⟶ B) [has_wide_pullback B X f]
  [preserves_limit (wide_cospan B X f) (forget C)]
  (x y : wide_pullback B X f) (h : ∀ j, π f j x = π f j y) : x = y :=
begin
  apply concrete.wide_pullback_ext _ _ _ _ h,
  inhabit ι,
  simp only [← π_arrow f (arbitrary _), comp_apply, h],
end

end limits

end category_theory.limits
