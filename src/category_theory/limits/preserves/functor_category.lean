/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.functor_category
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.yoneda
import category_theory.limits.presheaf

/-!
# Preservation of (co)limits in the functor category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
for `F : C ⥤ D` preserves colimits.

The idea of the proof is simply that products and colimits in the functor category are computed
pointwise, so pointwise preservation implies general preservation.

* Show that `F ⋙ -` preserves limits if the target category has limits.
* Show that `F : C ⥤ D` preserves limits of a certain shape
  if `Lan F.op : Cᵒᵖ ⥤ Type*` preserves such limits.

# References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/

universes v₁ v₂ u u₂

noncomputable theory

namespace category_theory

open category limits

variables {C : Type u} [category.{v₁} C]
variables {D : Type u₂} [category.{u} D]
variables {E : Type u} [category.{v₂} E]

/--
If `X × -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -` for
`F : C ⥤ D` also preserves colimits.

Note this is (mathematically) a special case of the statement that
"if limits commute with colimits in `D`, then they do as well in `C ⥤ D`"
but the story in Lean is a bit more complex, and this statement isn't directly a special case.
That is, even with a formalised proof of the general statement, there would still need to be some
work to convert to this version: namely, the natural isomorphism
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅ prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
def functor_category.prod_preserves_colimits [has_binary_products D] [has_colimits D]
  [∀ (X : D), preserves_colimits (prod.functor.obj X)]
  (F : C ⥤ D) :
  preserves_colimits (prod.functor.obj F) :=
{ preserves_colimits_of_shape := λ J 𝒥, by exactI
  { preserves_colimit := λ K,
    { preserves := λ c t,
      begin
        apply evaluation_jointly_reflects_colimits _ (λ k, _),
        change is_colimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).map_cocone c),
        let := is_colimit_of_preserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t,
        apply is_colimit.map_cocone_equiv _ this,
        apply (nat_iso.of_components _ _).symm,
        { intro G,
          apply as_iso (prod_comparison ((evaluation C D).obj k) F G) },
        { intros G G',
          apply prod_comparison_natural ((evaluation C D).obj k) (𝟙 F) },
      end } } }

instance whiskering_left_preserves_limits [has_limits D] (F : C ⥤ E) :
  preserves_limits ((whiskering_left C E D).obj F) := ⟨λ J hJ, by exactI ⟨λ K, ⟨λ c hc,
begin
  apply evaluation_jointly_reflects_limits,
  intro Y,
  change is_limit (((evaluation E D).obj (F.obj Y)).map_cone c),
  exact preserves_limit.preserves hc,
end ⟩⟩⟩

instance whiskering_right_preserves_limits_of_shape {C : Type u} [category C]
  {D : Type*} [category.{u} D] {E : Type*} [category.{u} E]
  {J : Type u} [small_category J] [has_limits_of_shape J D]
    (F : D ⥤ E) [preserves_limits_of_shape J F] :
  preserves_limits_of_shape J ((whiskering_right C D E).obj F) := ⟨λ K, ⟨λ c hc,
begin
  apply evaluation_jointly_reflects_limits,
  intro k,
  change is_limit (((evaluation _ _).obj k ⋙ F).map_cone c),
  exact preserves_limit.preserves hc,
end ⟩⟩

instance whiskering_right_preserves_limits {C : Type u} [category C]
  {D : Type*} [category.{u} D] {E : Type*} [category.{u} E] (F : D ⥤ E)
  [has_limits D] [preserves_limits F] : preserves_limits ((whiskering_right C D E).obj F) := ⟨⟩

/-- If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so will `F`. -/
noncomputable
def preserves_limit_of_Lan_presesrves_limit {C D : Type u} [small_category C] [small_category D]
  (F : C ⥤ D) (J : Type u) [small_category J]
  [preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u))] :
  preserves_limits_of_shape J F :=
begin
  apply preserves_limits_of_shape_of_reflects_of_preserves F yoneda,
  exact preserves_limits_of_shape_of_nat_iso (comp_yoneda_iso_yoneda_comp_Lan F).symm,
  apply_instance
end

end category_theory
