/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.defs

namespace list

/-- The alternating sum of a list. -/
def alternating_sum {G : Type*} [has_zero G] [has_add G] [has_neg G] : list G → G
| [] := 0
| (g :: []) := g
| (g :: h :: t) := g + -h + alternating_sum t

/-- The alternating product of a list. -/
@[to_additive] def alternating_prod {G : Type*} [has_one G] [has_mul G] [has_inv G] : list G → G
| [] := 1
| (g :: []) := g
| (g :: h :: t) := g * h⁻¹ * alternating_prod t

variables {G : Type*} [comm_group G]

@[simp, to_additive] lemma alternating_prod_nil :
  alternating_prod ([] : list G) = 1 := rfl

@[simp, to_additive] lemma alternating_prod_singleton (g : G) :
  alternating_prod [g] = g := rfl

@[simp, to_additive alternating_sum_cons_cons']
lemma alternating_prod_cons_cons (g h : G) (l : list G) :
  alternating_prod (g :: h :: l) = g * h⁻¹ * alternating_prod l := rfl

lemma alternating_sum_cons_cons {G : Type*} [add_comm_group G] (g h : G) (l : list G) :
  alternating_sum (g :: h :: l) = g - h + alternating_sum l := rfl

end list
