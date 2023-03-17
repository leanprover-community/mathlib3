/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.units

/-!
# Some facts about finite rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open_locale classical

lemma card_units_lt (M₀ : Type*) [monoid_with_zero M₀] [nontrivial M₀] [fintype M₀] :
  fintype.card M₀ˣ < fintype.card M₀ :=
fintype.card_lt_of_injective_of_not_mem (coe : M₀ˣ → M₀) units.ext not_is_unit_zero
