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
or, having constructed that monoidal structure directly, show this functor is monoidal.
-/

open category_theory
open category_theory.equivalence

/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is full. -/
instance : full (forget₂ (Module ℤ) AddCommGroup) :=
{ preimage := λ A B f,
  -- TODO: why `add_monoid_hom.to_int_linear_map` doesn't work here?
  { to_fun := f,
    map_add' := add_monoid_hom.map_add f,
    map_smul' := λ n x, by convert add_monoid_hom.map_int_module_smul f n x } }

/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is essentially surjective. -/
instance : ess_surj (forget₂ (Module ℤ) AddCommGroup) :=
{ obj_preimage := λ A, Module.of ℤ A,
  iso' := λ A, { hom := 𝟙 A, inv := 𝟙 A, } }

instance : is_equivalence (forget₂ (Module ℤ) AddCommGroup) :=
equivalence_of_fully_faithfully_ess_surj (forget₂ (Module ℤ) AddCommGroup)
