/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic

/-!
The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.

TODO:
either use this equivalence to transport the monoidal structure from `Module ℤ` to `Ab`,
or, having constructing it directly, show this functor is monoidal.
-/

open category_theory
open category_theory.equivalence

instance : full (forget₂ (Module ℤ) AddCommGroup) :=
{ preimage := λ A B f,
  { to_fun := f,
    add := λ x y, add_monoid_hom.map_add f x y,
    smul := λ n x, add_monoid_hom.map_int_module_smul f n x, } }

instance : ess_surj (forget₂ (Module ℤ) AddCommGroup) :=
{ obj_preimage := λ A, Module.of ℤ A,
  iso' := by tidy }

instance : is_equivalence (forget₂ (Module ℤ) AddCommGroup) :=
equivalence_of_fully_faithfully_ess_surj (forget₂ (Module ℤ) AddCommGroup)
