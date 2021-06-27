/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.associated
import data.fintype.basic

/-!
# Some facts about finite rings
-/

open_locale classical

lemma card_units_lt (M₀ : Type*) [monoid_with_zero M₀] [nontrivial M₀] [fintype M₀] :
  fintype.card (units M₀) < fintype.card M₀ :=
fintype.card_lt_of_injective_of_not_mem (coe : units M₀ → M₀) units.ext not_is_unit_zero
