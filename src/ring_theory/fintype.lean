/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.ring
import data.fintype.basic

/-!
Some facts about finite rings.

(There may be a better home for these elsewhere?)
-/

lemma zero_not_mem_range_coe_units (R : Type*) [nonzero_semiring R] :
  (0 : R) ∉ set.range (coe : units R → R) :=
begin
  rintro ⟨⟨v,w',h,h'⟩, a⟩,
  dsimp at a,
  subst a,
  simpa using h,
end

open_locale classical

lemma card_units_lt (R : Type*) [nonzero_semiring R] [fintype R] :
  fintype.card (units R) < fintype.card R :=
card_lt_card_of_injective_of_not_mem (coe : units R → R) units.ext (zero_not_mem_range_coe_units R)
