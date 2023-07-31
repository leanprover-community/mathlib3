/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.instances
import algebra.order.monoid.with_top

/-!
# Adjoining a top element to a `linear_ordered_add_comm_group_with_top`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variable {α : Type*}

section linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group α] {a b c d : α}

instance with_top.linear_ordered_add_comm_group_with_top :
  linear_ordered_add_comm_group_with_top (with_top α) :=
{ neg            := option.map (λ a : α, -a),
  neg_top        := @option.map_none _ _ (λ a : α, -a),
  add_neg_cancel := begin
    rintro (a | a) ha,
    { exact (ha rfl).elim },
    { exact with_top.coe_add.symm.trans (with_top.coe_eq_coe.2 (add_neg_self a)) }
  end,
  .. with_top.linear_ordered_add_comm_monoid_with_top,
  .. option.nontrivial }

@[simp, norm_cast]
lemma with_top.coe_neg (a : α) : ((-a : α) : with_top α) = -a := rfl

end linear_ordered_add_comm_group
