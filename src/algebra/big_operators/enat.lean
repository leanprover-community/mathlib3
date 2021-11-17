/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.big_operators.basic
import data.nat.enat

/-!
# Big operators in `enat`

A simple lemma about sums in `enat`.
-/
open_locale big_operators
variables {α : Type*}

namespace finset
lemma sum_nat_coe_enat (s : finset α) (f : α → ℕ) :
  (∑ x in s, (f x : enat)) = (∑ x  in s, f x : ℕ) :=
(enat.coe_hom.map_sum _ _).symm

end finset
