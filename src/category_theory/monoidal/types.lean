/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.of_has_finite_products
import category_theory.limits.shapes.finite_products
import category_theory.limits.types

open category_theory
open category_theory.limits
open tactic

universes u v

namespace category_theory.monoidal

local attribute [instance] monoidal_of_has_finite_products

instance types : monoidal_category.{u} (Type u) := by apply_instance

-- TODO Once we add braided/symmetric categories, include the braiding/symmetry.

instance : unique (𝟙_ (Type u)) := by tidy

def as_term {X : Type u} (f : 𝟙_ (Type u) ⟶ X) : X :=
f (default _)

@[simp] lemma apply_pt {X : Type u} (f : 𝟙_ (Type u) ⟶ X) : f (default _) = as_term f := rfl

def of_term {X : Type u} (x : X) : 𝟙_ (Type u) ⟶ X := λ _, x

@[simp] lemma of_term_as_term {X : Type u} (f : 𝟙_ (Type u) ⟶ X) : of_term (as_term f) = f :=
begin
  funext x,
  dsimp [as_term, of_term],
  congr,
end

@[simp] lemma as_term_of_term {X : Type u} (x : X) : as_term (of_term x) = x := rfl

def tmul {X Y : Type u} (x : X) (y : Y) : (X ⊗ Y : Type u) :=
as_term ((λ_ (𝟙_ (Type u))).inv ≫ (of_term x ⊗ of_term y))

lemma ρ_inv {X : Type u} (x : X) : ((ρ_ X).inv : X → X ⊗ (𝟙_ (Type u))) x = tmul x (default _) :=
begin
  dsimp only [tmul],
  -- TODO
  -- 1. there are too many simp lemmas about the monoidal structure for type!
  -- 2. we need `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`.
  sorry
end

end category_theory.monoidal
