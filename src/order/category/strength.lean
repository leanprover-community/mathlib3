/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import category_theory.monad
import category_theory.monoidal.category
import category_theory.monoidal.braided

/-!
# Tensorial Strength

In a monoidal category `C`, the tensorial strength for functor
`F : C ⥤ C` is a natural transformation `σ_ X Y : X⊗FY ⟶ F(X⊗Y)`
which commutes with tensorial unitor and associator.

From a programming perspective, it can be seen as bringing a
piece of data of type `X` inside an existing monadic value.

## Main definitions

 * `has_strength` a class for strong functors
 * `has_costrength` a class for co-strong functors
 * `strong_monad` a class for strong monads

## References
 * https://ncatlab.org/nlab/show/tensorial+strength
 * https://ncatlab.org/nlab/show/strong+monad
 * [Anders Kock, *Strong functors and monoidal monads*, Arch. Math. (Basel) 23 (1972), 113–120.][kock]
-/

universes u v
namespace category_theory

variables {C : Type u} [category.{v} C] [monoidal_category C]
variables (F : C ⥤ C)

/-- In a monoidal category `C`, the tensorial strength for functor
`F : C ⥤ C` is a natural transformation `σ_ X Y : X⊗FY ⟶ F(X⊗Y)`
which commutes with tensorial unitor and associator.
-/
class has_strength :=
(strength' [] : Π X Y : C, X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
(notation `σ_` := strength')
(naturality : Π {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
  σ_ X Y ≫ F.map (f ⊗ g) = (f ⊗ F.map g) ≫ σ_ X' Y')
(unit_strength (X : C) : (λ_ _).inv ≫ σ_ (𝟙_ _) X = F.map (λ_ _).inv)
(assoc_strength (X Y Z : C) :
  (α_ X Y (F.obj Z)).hom ≫ (𝟙 _ ⊗ σ_ _ _) ≫ σ_ _ _ =
  σ_ _ _ ≫ F.map ((α_ X Y Z).hom))

notation `σ_` := has_strength.strength'
open monoidal_category has_strength
attribute [simp, reassoc] has_strength.naturality has_strength.unit_strength has_strength.assoc_strength

namespace has_strength
variables [has_strength F]

@[simp] lemma strength_nat_left {X Y X' : C} (f : X ⟶ X') :
  σ_ F X Y ≫ F.map (f ⊗ 𝟙 _) = (f ⊗ 𝟙 _) ≫ σ_ F X' Y :=
by simp [naturality]
.
@[simp] lemma strength_nat_right {X Y Y' : C} (g : Y ⟶ Y') :
  σ_ F X Y ≫ F.map (𝟙 _ ⊗ g) = (𝟙 _ ⊗ F.map g) ≫ σ_ F X Y' :=
naturality _ _

end has_strength

section nat_trans

variables F

/-- Tensorial strength, as a natural transformation. -/
@[simps] def strength [has_strength F] :
  functor.prod (𝟭 C) F ⋙ tensor C ⟶ tensor C ⋙ F :=
{ app := λ X, has_strength.strength' F _ _,
  naturality' := by intros; dsimp; simp only [has_strength.naturality] }

end nat_trans

/-- In a monoidal category `C`, the tensorial costrength (co- does not
refer to opposite the category) for functor `F : C ⥤ C` is a natural
transformation `σ_ X Y : FX⊗Y ⟶ F(X⊗Y)` which commutes with tensorial
unitor and associator.-/
class has_costrength :=
(costrength' [] : Π X Y : C, F.obj X ⊗ Y ⟶ F.obj (X ⊗ Y))
(notation `τ_` := costrength')
(naturality : Π {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
  τ_ X Y ≫ F.map (f ⊗ g) = (F.map f ⊗ g) ≫ τ_ X' Y')
(unit_costrength (X : C) : (ρ_ _).inv ≫ τ_ X (𝟙_ _) = F.map (ρ_ _).inv)
(assoc_costrength (X Y Z : C) :
  (α_ (F.obj X) Y Z).inv ≫ (τ_ _ _ ⊗ 𝟙 _) ≫ τ_ _ _ =
  τ_ _ _ ≫ F.map ((α_ X Y Z).inv))

notation `τ_` := has_costrength.costrength'
open has_costrength
attribute [simp, reassoc] has_costrength.naturality
attribute [simp, reassoc] has_costrength.unit_costrength has_costrength.assoc_costrength

section prio

set_option default_priority 100
variables [braided_category.{v} C]

#check monoidal_category.associator_naturality

instance has_strength.to_has_costrength [has_strength F] : has_costrength F :=
{ costrength' := λ X Y, (β_ _ _).hom ≫ σ_ _ _ _ ≫ F.map ((β_ _ _).inv),
  naturality := by intros; simp only [← functor.map_comp, category.assoc, braided_category.braiding_naturality_assoc, braided_category.braiding_naturality_inv, ← has_strength.naturality_assoc],
  unit_costrength := by intros; simp [← functor.map_comp],
  assoc_costrength := sorry
    -- by intros; simp only [← tensor_comp, monoidal_category.associator_naturality, category.assoc, ← functor.map_comp]
  -- sorry -- by intros; dsimp; simp [← tensor_comp, category.assoc],
 }

/-- The strength derived from co-strength -/
def has_costrength.to_has_strength [has_costrength F] : has_strength F :=
{ strength' := λ X Y, (β_ _ _).hom ≫ τ_ _ _ _ ≫ F.map ((β_ _ _).inv),
  naturality := by intros; simp only [← functor.map_comp, category.assoc, braided_category.braiding_naturality_assoc, braided_category.braiding_naturality_inv, ← has_costrength.naturality_assoc],
  unit_strength := by intros; simp [← functor.map_comp],
  assoc_strength := sorry -- by intros; dsimp; simp [← functor.map_comp, ← tensor_comp, ← tensor_comp_assoc, category.assoc],
  }

end prio

namespace has_costrength

variables [has_costrength F]

@[simp] lemma costrength_nat_left {X Y X' : C} (f : X ⟶ X') :
  τ_ F X Y ≫ F.map (f ⊗ 𝟙 _) = (F.map f ⊗ 𝟙 _) ≫ τ_ F X' Y :=
naturality _ _
.
@[simp] lemma costrength_nat_right {X Y Y' : C} (g : Y ⟶ Y') :
  τ_ F X Y ≫ F.map (𝟙 _ ⊗ g) = (𝟙 _ ⊗ g) ≫ τ_ F X Y' :=
by rw [naturality, F.map_id]

end has_costrength

section nat_trans

variables F

/-- Tensorial strength, as a natural transformation. -/
@[simps] def costrength [has_costrength F] :
  functor.prod F (𝟭 C) ⋙ tensor C ⟶ tensor C ⋙ F :=
{ app := λ X, has_costrength.costrength' F _ _,
  naturality' := by intros; dsimp; simp only [has_costrength.naturality] }

end nat_trans

/--
A strong monad is a monad with tensorial strength and where
the tensorial strength commutes with the monad's unit and
product.
-/
class strong_monad extends monad F, has_strength F :=
(pure_strength {X Y : C} : (𝟙 X ⊗ (η_ F).app Y) ≫ σ_ F X Y = (η_ F).app _)
(bind_strength {X Y : C} :
  (𝟙 X ⊗ (μ_ F).app Y) ≫ σ_ F X Y =
  (σ_ F X (F.obj Y) ≫ F.map (σ_ F X Y) ≫ (μ_ F).app _ : X ⊗ F.obj _ ⟶ _))

def strong_monad.to_lax_functor [strong_monad F] [has_costrength F] : lax_monoidal_functor C C :=
{ ε := (η_ F).app _,
  μ := λ X Y, (σ_ F _ _ ≫ F.map (τ_ F _ _) ≫ (μ_ F).app _ : F.obj _ ⊗ F.obj _ ⟶ F.obj _ ),
  μ_natural' := by intros; simp [← (μ_ F).naturality]; rw [← functor.map_comp_assoc, ← has_strength.naturality_assoc, ← functor.map_comp_assoc, has_costrength.naturality]; dsimp,
  associativity' := sorry, -- by intros; dsimp; simp [← (μ_ F).naturality]; rw [← functor.map_comp_assoc, ← tensor_comp_assoc, ← tensor_comp_assoc, ← tensor_comp_assoc, ← tensor_comp_assoc, ← (μ_ F).naturality, has_strength.naturality_assoc],
  left_unitality' := sorry,  -- by obviously,
  right_unitality' := sorry, -- by obviously,
  .. F
 }

end category_theory
