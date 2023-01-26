/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.cast
import algebra.big_operators.basic

/-! # Casting lemmas for rational numbers involving sums and products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open_locale big_operators

variables {ι α : Type*}

namespace rat

section with_div_ring
variables [division_ring α] [char_zero α]

@[simp, norm_cast] lemma cast_list_sum (s : list ℚ) : (↑(s.sum) : α) = (s.map coe).sum :=
map_list_sum (rat.cast_hom α) _

@[simp, norm_cast] lemma cast_multiset_sum (s : multiset ℚ) : (↑(s.sum) : α) = (s.map coe).sum :=
map_multiset_sum (rat.cast_hom α) _

@[simp, norm_cast] lemma cast_sum (s : finset ι) (f : ι → ℚ) :
  (↑(∑ i in s, f i) : α) = ∑ i in s, f i :=
map_sum (rat.cast_hom α) _ _

@[simp, norm_cast] lemma cast_list_prod (s : list ℚ) : (↑(s.prod) : α) = (s.map coe).prod :=
map_list_prod (rat.cast_hom α) _

end with_div_ring

section field
variables [field α] [char_zero α]

@[simp, norm_cast] lemma cast_multiset_prod (s : multiset ℚ) : (↑(s.prod) : α) = (s.map coe).prod :=
map_multiset_prod (rat.cast_hom α) _

@[simp, norm_cast] lemma cast_prod (s : finset ι) (f : ι → ℚ) :
  (↑(∏ i in s, f i) : α) = ∏ i in s, f i :=
map_prod (rat.cast_hom α) _ _

end field

end rat
