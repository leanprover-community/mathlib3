/-
Copyright (c) 2021 Nicholas Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Tan
-/
import group_theory.group_action
import group_theory.quotient_group
import group_theory.order_of_element
import data.zmod.basic
import data.fintype.card
import data.list.rotate

/-!
# Class Equation

The Class Equation for a finite group G is the following identity, where `Z(G)` is the center
of a group and `[G : H]` is the index of `H` in `G`

* | G | = | Z(G) | + ∑ [ G : C_i ]

## Main statements


## TODO

* prove/find/import that orbits are partition of a set
      because they define an equivalence relation `orbit_rel`
* prove that orbit is either fixed point or not

* use group action of conjugation on group

-/

open equiv fintype finset mul_action function
open equiv.perm subgroup list quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

namespace mul_action
variables [mul_action G α]

-- lemma orbits_partition
--   [fintype α] [fintype G] :

-- begin
--   sorry,
-- end

-- lemma card_set_is_card_orbits
--   [fintype α] [fintype G] :
--   card α = ∑ :=
-- begin
--   sorry,
-- end

/-- **Class Equation for a Group Action** -/
theorem card_set_is_card_fixed_add_card_orbits
  [fintype α] [fintype G] [fintype (fixed_points G α)] :
  card α = card (fixed_points G α) :=
begin
  sorry,
end

/-- **Class equation for a Group** -/
theorem card_group_is_card_center_add_conj [fintype G] :
  card G = card (center G) :=
begin
  sorry,
end

end mul_action
