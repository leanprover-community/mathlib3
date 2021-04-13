/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.enriched.enriched_over
import algebra.category.Group.basic
import data.equiv.transfer_instance

universes v u

namespace category_theory

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

abbreviation preadditive' := enriched_over.{v} AddCommGroup.{v} C

instance (X Y : C) [preadditive' C] : add_comm_group (X ⟶ Y) :=
equiv.add_comm_group (equiv.cast (by simp) : (X ⟶ Y) ≃ (X ⟶[AddCommGroup.{v}] Y : Type v))

end category_theory
