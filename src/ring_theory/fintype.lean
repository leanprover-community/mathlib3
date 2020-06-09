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

lemma card_units_lt (R : Type*) [semiring R] [nonzero R] [fintype R] :
  fintype.card (units R) < fintype.card R :=
card_lt_card_of_injective_of_not_mem (coe : units R → R) units.ext not_is_unit_zero
