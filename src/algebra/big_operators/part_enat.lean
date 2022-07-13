/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.big_operators.basic
import data.nat.part_enat

/-!
# Big operators in `part_enat`

A simple lemma about sums in `part_enat`.
-/
open_locale big_operators
variables {α : Type*}

namespace finset
lemma sum_nat_coe_enat (s : finset α) (f : α → ℕ) :
  (∑ x in s, (f x : part_enat)) = (∑ x  in s, f x : ℕ) :=
(part_enat.coe_hom.map_sum _ _).symm

end finset
