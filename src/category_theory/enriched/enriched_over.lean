/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.concrete_category
import category_theory.eq_to_hom

/-- A helper tactic for discharging fields of `enriched_over`. -/
meta def try_refl : tactic unit := `[try {repeat { intro, }, refl}]

universes v u

open category_theory

namespace category_theory

variables (V : Type (v+1)) [large_category V] [concrete_category V]
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

-- Implementation note: if you create instances in which you prove `*_forget`
-- by anything other than `refl`, you're probably going to suffer later.
class enriched_over :=
(enriched_hom  [] : Π (X Y : C), V)
(notation X ` ⟶[] ` Y:10 := enriched_hom X Y)
(enriched_hom_forget' [] : ∀ (X Y : C), (forget V).obj (X ⟶[] Y) = (X ⟶ Y) . try_refl)
(comp_left [] : Π {X Y : C} (f : X ⟶ Y) (Z : C), (Y ⟶[] Z) ⟶ (X ⟶[] Z))
(comp_left_forget' [] : ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
  eq_to_hom ((enriched_hom_forget' Y Z).symm)
  ≫ (forget V).map (comp_left f Z)
  ≫ eq_to_hom (enriched_hom_forget' X Z) = (λ g : Y ⟶ Z, f ≫ g) . try_refl)
(comp_right [] : Π (X : C) {Y Z : C} (g : Y ⟶ Z), (X ⟶[] Y) ⟶ (X ⟶[] Z))
(comp_right_forget' [] : ∀ (X : C) {Y Z : C} (g : Y ⟶ Z),
  eq_to_hom ((enriched_hom_forget' X Y).symm)
  ≫ (forget V).map (comp_right X g)
  ≫ eq_to_hom (enriched_hom_forget' X Z) = (λ f : X ⟶ Y, f ≫ g) . try_refl)

open enriched_over

restate_axiom enriched_hom_forget'
restate_axiom comp_left_forget'
restate_axiom comp_right_forget'
attribute [simp] enriched_over.enriched_hom_forget
attribute [simp] enriched_over.comp_left_forget
attribute [simp] enriched_over.comp_right_forget'

variable [enriched_over V C]

notation X ` ⟶[`V`] ` Y:10 := (enriched_over.enriched_hom V X Y : V)
example [enriched_over V C] (X Y : C) : V := X ⟶[V] Y

section
omit 𝒞
variables (D : Type (v+1)) [large_category D] [concrete_category D]
variables [enriched_over V D]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

instance (X Y : D) : has_coe_to_fun ((X ⟶[V] Y) : V) :=
{ F := λ f, X → Y,
  coe := λ f,
  begin
    change (forget V).obj _ at f,
    simp only [enriched_over.enriched_hom_forget, forget_obj_eq_coe] at f,
    exact (f : X → Y),
  end }
end

omit 𝒞

/-- We check that we can construct the trivial enrichment of `Type` in `Type`. -/
instance : enriched_over (Type u) (Type u) :=
{ enriched_hom := λ X Y, X ⟶ Y,
  comp_left := λ X Y f Z, λ (g : Y ⟶ Z), f ≫ g,
  comp_right := λ X Y Z g, λ (f : X ⟶ Y), f ≫ g, }

open enriched_over

-- We check that this instance has good definitional properties:
example : comp_left Type (↾(λ n : ℕ, 2 * n)) ℕ = (λ f n, f (2 * n)) := rfl

end category_theory
