/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.linear.linear_functor
import category_theory.monoidal.preadditive

/-!
# Linear monoidal categories

A monoidal category is `monoidal_linear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/

namespace category_theory

open category_theory.limits
open category_theory.monoidal_category

variables (R : Type*) [semiring R]
variables (C : Type*) [category C] [preadditive C] [linear R C]
variables [monoidal_category C] [monoidal_preadditive C]

/--
A category is `monoidal_linear R` if tensoring is `R`-linear in both factors.
-/
class monoidal_linear :=
(tensor_smul' : ∀ {W X Y Z : C} (f : W ⟶ X) (r : R) (g : Y ⟶ Z),
  f ⊗ (r • g) = r • (f ⊗ g) . obviously)
(smul_tensor' : ∀ {W X Y Z : C} (r : R) (f : W ⟶ X) (g : Y ⟶ Z),
  (r • f) ⊗ g = r • (f ⊗ g) . obviously)

restate_axiom monoidal_linear.tensor_smul'
restate_axiom monoidal_linear.smul_tensor'
attribute [simp] monoidal_linear.tensor_smul monoidal_linear.smul_tensor

variables [monoidal_linear R C]

instance tensor_left_linear (X : C) : (tensor_left X).linear R := {}
instance tensor_right_linear (X : C) : (tensor_right X).linear R := {}
instance tensoring_left_linear (X : C) : ((tensoring_left C).obj X).linear R := {}
instance tensoring_right_linear (X : C) : ((tensoring_right C).obj X).linear R := {}

end category_theory
