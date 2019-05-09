-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Michael Jendrusch, Scott Morrison
import category_theory.monoidal.category

open category_theory
open tactic

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory.monoidal

section

open monoidal_category

variables (C : Sort u₁) [𝒞 : monoidal_category.{v₁} C]
          (D : Sort u₂) [𝒟 : monoidal_category.{v₂} D]
include 𝒞 𝒟

structure lax_monoidal_functor extends C ⥤ D :=
-- unit morphism
(ε               : tensor_unit D ⟶ obj (tensor_unit C))
-- tensorator
(μ                : Π X Y : C, (obj X) ⊗ (obj Y) ⟶ obj (X ⊗ Y))
(μ_natural'       : ∀ (X Y X' Y' : C)
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  ((map f) ⊗ (map g)) ≫ μ Y Y' = μ X X' ≫ map (f ⊗ g)
  . obviously)
-- associativity of the tensorator
(associativity'   : ∀ (X Y Z : C),
    (μ X Y ⊗ 𝟙 (obj Z)) ≫ μ (X ⊗ Y) Z ≫ map (associator X Y Z).hom
  = (associator (obj X) (obj Y) (obj Z)).hom ≫ (𝟙 (obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z)
  . obviously)
-- unitality
(left_unitality'  : ∀ X : C,
    (left_unitor (obj X)).hom
  = (ε ⊗ 𝟙 (obj X)) ≫ μ (tensor_unit C) X ≫ map (left_unitor X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (right_unitor (obj X)).hom
  = (𝟙 (obj X) ⊗ ε) ≫ μ X (tensor_unit C) ≫ map (right_unitor X).hom
  . obviously)

restate_axiom lax_monoidal_functor.μ_natural'
attribute [simp] lax_monoidal_functor.μ_natural
restate_axiom lax_monoidal_functor.left_unitality'
attribute [simp] lax_monoidal_functor.left_unitality
restate_axiom lax_monoidal_functor.right_unitality'
attribute [simp] lax_monoidal_functor.right_unitality
restate_axiom lax_monoidal_functor.associativity'
attribute [simp] lax_monoidal_functor.associativity

-- When `rewrite_search` lands, add @[search] attributes to
-- lax_monoidal_functor.μ_natural lax_monoidal_functor.left_unitality
-- lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

structure monoidal_functor
extends lax_monoidal_functor.{v₁ v₂} C D :=
(ε_is_iso            : is_iso ε . obviously)
(μ_is_iso            : Π X Y : C, is_iso (μ X Y) . obviously)

attribute [instance] monoidal_functor.ε_is_iso monoidal_functor.μ_is_iso

variables {C D}

def monoidal_functor.ε_iso (F : monoidal_functor.{v₁ v₂} C D) :
  tensor_unit D ≅ F.obj (tensor_unit C) :=
as_iso F.ε
def monoidal_functor.μ_iso (F : monoidal_functor.{v₁ v₂} C D) (X Y : C) :
  (F.obj X) ⊗ (F.obj Y) ≅ F.obj (X ⊗ Y) :=
as_iso (F.μ X Y)

end

namespace monoidal_functor

open monoidal_category

-- In order to express the tensorator as a natural isomorphism,
-- we need to be in at least `Type 0`, so we have products.
variables {C : Type u₁} [𝒞 : monoidal_category.{v₁+1} C]
variables {D : Type u₂} [𝒟 : monoidal_category.{v₂+1} D]
include 𝒞 𝒟

def μ_nat_iso (F : monoidal_functor.{v₁+1 v₂+1} C D) :
  (functor.prod F.to_functor F.to_functor) ⋙ (tensor D) ≅ (tensor C) ⋙ F.to_functor :=
nat_iso.of_components
  (by intros; dsimp; apply F.μ_iso)
  (by intros; dsimp; apply F.to_lax_monoidal_functor.μ_natural)

end monoidal_functor

section

variables (C : Sort u₁) [𝒞 : monoidal_category.{v₁} C]
include 𝒞

def monoidal_functor.id : monoidal_functor.{v₁ v₁} C C :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  .. functor.id C }

@[simp] lemma id_obj (X : C) : (monoidal_functor.id C).obj X = X := rfl
@[simp] lemma id_map {X X' : C} (f : X ⟶ X') : (monoidal_functor.id C).map f = f := rfl
@[simp] lemma id_ε : (monoidal_functor.id C).ε = 𝟙 _ := rfl
@[simp] lemma id_μ (X Y) : (monoidal_functor.id C).μ X Y = 𝟙 _ := rfl

variables {C}
variables {D : Sort u₂} [𝒟 : monoidal_category.{v₂} D]
variables {E : Sort u₃} [ℰ : monoidal_category.{v₃} E]

include 𝒟 ℰ

section
variables (F : lax_monoidal_functor.{v₁ v₂} C D) (G : lax_monoidal_functor.{v₂ v₃} D E)

-- The proofs here are horrendous; rewrite_search helps a lot.
def lax_monoidal_functor.comp : lax_monoidal_functor.{v₁ v₃} C E :=
{ ε                := G.ε ≫ (G.map F.ε),
  μ                := λ X Y, G.μ (F.obj X) (F.obj Y) ≫ G.map (F.μ X Y),
  μ_natural'       := λ _ _ _ _ f g,
  begin
    simp only [functor.comp_map, assoc],
    conv_lhs { rw [←category.assoc], congr, rw [lax_monoidal_functor.μ_natural] },
    conv_lhs { rw [category.assoc], congr, skip, rw [←map_comp] },
    conv_rhs { congr, skip, rw [←map_comp, ←lax_monoidal_functor.μ_natural] }
  end,
  associativity'   := λ X Y Z,
  begin
    dsimp,
    rw interchange_right_identity,
    slice_rhs 3 4 { rw [← G.to_functor.map_id, G.μ_natural], },
    slice_rhs 1 3 { rw ←G.associativity, },
    rw interchange_left_identity,
    slice_lhs 2 3 { rw [← G.to_functor.map_id, G.μ_natural], },
    rw [category.assoc, category.assoc, category.assoc, category.assoc, category.assoc,
        ←G.to_functor.map_comp, ←G.to_functor.map_comp, ←G.to_functor.map_comp, ←G.to_functor.map_comp,
        F.associativity],
  end,
  left_unitality'  := λ X,
  begin
    dsimp,
    rw [G.left_unitality, interchange_left_identity, category.assoc, category.assoc],
    apply congr_arg,
    rw F.left_unitality,
    conv_lhs { congr, skip, rw [map_comp] },
    conv_lhs { rw [←category.id_app, ←category.assoc] },
    conv_lhs { congr, rw [←lax_monoidal_functor.μ_natural] },
    conv_lhs { congr, congr, congr, skip, rw [functor.category.id_app, map_id] },
    conv_rhs { rw [←category.assoc] },
    rw map_comp,
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    rw [G.right_unitality, interchange_right_identity, category.assoc, category.assoc],
    apply congr_arg,
    rw F.right_unitality,
    conv_lhs { congr, skip, rw [map_comp] },
    conv_lhs { rw [←category.id_app, ←category.assoc] },
    conv_lhs { congr, rw [←lax_monoidal_functor.μ_natural] },
    conv_lhs { congr, congr, congr, rw [functor.category.id_app, map_id] },
    conv_rhs { rw [←category.assoc] },
    rw map_comp,
  end,
  .. (F.to_functor) ⋙ (G.to_functor) }.

@[simp] lemma lax_monoidal_functor.comp_obj (X : C) : (F.comp G).obj X = G.obj (F.obj X) := rfl
@[simp] lemma lax_monoidal_functor.comp_map {X X' : C} (f : X ⟶ X') :
  (F.comp G).map f = (G.map (F.map f) : G.obj (F.obj X) ⟶ G.obj (F.obj X')) := rfl
@[simp] lemma lax_monoidal_functor.comp_ε : (F.comp G).ε = G.ε ≫ (G.map F.ε) := rfl
@[simp] lemma lax_monoidal_functor.comp_μ (X Y : C) : (F.comp G).μ X Y = G.μ (F.obj X) (F.obj Y) ≫ G.map (F.μ X Y) := rfl
end

section
variables (F : monoidal_functor.{v₁ v₂} C D) (G : monoidal_functor.{v₂ v₃} D E)

def monoidal_functor.comp : monoidal_functor.{v₁ v₃} C E :=
{ ε_is_iso := by { dsimp, apply_instance }, -- TODO tidy should get this
  μ_is_iso := by { dsimp, apply_instance }, -- TODO tidy should get this
  .. (F.to_lax_monoidal_functor).comp (G.to_lax_monoidal_functor) }.

end
end

end category_theory.monoidal
