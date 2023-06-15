/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.

TODO:
either use this equivalence to transport the monoidal structure from `Module ℤ` to `Ab`,
or, having constructed that monoidal structure directly, show this functor is monoidal.
-/

open category_theory
open category_theory.equivalence

universes u

namespace Module

/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is full. -/
instance forget₂_AddCommGroup_full : full (forget₂ (Module ℤ) AddCommGroup.{u}) :=
{ preimage := λ A B f,
  -- `add_monoid_hom.to_int_linear_map` doesn't work here because `A` and `B` are not definitionally
  -- equal to the canonical `add_comm_group.int_module` module instances it expects.
  { to_fun := f,
    map_add' := add_monoid_hom.map_add f,
    map_smul' := λ n x, by rw [int_smul_eq_zsmul, int_smul_eq_zsmul, map_zsmul,
                               ring_hom.id_apply] } }

/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is essentially surjective. -/
instance forget₂_AddCommGroup_ess_surj : ess_surj (forget₂ (Module ℤ) AddCommGroup.{u}) :=
{ mem_ess_image := λ A, ⟨Module.of ℤ A, ⟨{ hom := 𝟙 A, inv := 𝟙 A }⟩⟩}

noncomputable instance forget₂_AddCommGroup_is_equivalence :
  is_equivalence (forget₂ (Module ℤ) AddCommGroup.{u}) :=
equivalence.of_fully_faithfully_ess_surj (forget₂ (Module ℤ) AddCommGroup)

end Module
