/-
Copyright (c) 2021 Nicholas Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Tan
-/

import set_theory.fincard
import group_theory.group_action
import data.setoid.partition
import data.setoid.count_partition
import data.fintype.basic
import algebra.big_operators


/-!
# Class Equation

The Class Equation for a finite group G is the following identity, where `Z(G)` is the center
of a group and `[G : H]` is the index of `H` in `G`

* | G | = | Z(G) | + ∑ [ G : C_i ]

## Main statements


## TODO

* prove/find/import that orbits are partition of a set
      because they define an equivalence relation `orbit_rel`
* conclude that summing size of each orbit will give size of set

* prove that orbit is either fixed point or not fixed
* fixed points have orbit of size 1
* sum of all orbits is number of fixed points + sum of card of nonfixed orbits

* use group action of conjugation on group

-/

open equiv fintype finset mul_action function
open equiv.perm subgroup list quotient_group
open_locale classical big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G] [fintype α] (S : setoid α)

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

variables [mul_action G α]

def orbits [fintype α] [fintype G] : setoid α := orbit_rel G α

namespace mul_action

lemma card_set_is_sum_card_orbits
  [fintype α] [fintype G] :
  card α = ∑ orb in (orbit_rel G α).classes.to_finset, (orb : set α).to_finset.card :=
begin
  exact card_set_is_sum_card_classes (orbit_rel G α),
end

/-- **Class Equation for a Group Action** -/
theorem card_set_is_card_fixed_add_card_orbits
  [fintype α] [fintype G] [fintype (fixed_points G α)] :
  card α = card (fixed_points G α) :=
begin
  sorry,
end

/-- **Class equation for a Group** -/
theorem card_group_is_card_center_add_card_conj [fintype G] :
  card G = card (center G) :=
begin
  sorry,
end

end mul_action
