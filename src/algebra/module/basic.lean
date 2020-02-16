/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import tactic.cache group_theory.group_action.basic algebra.ring

/-!
# Modules over a ring.

This file contains definitions of `semimodule`, `module`, and some basic lemmas that do not
rely on `finset`s and/or `group_power`.
-/

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `α` and an additive monoid of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class semimodule (α : Type u) (β : Type v) [semiring α]
  [add_comm_monoid β] extends distrib_mul_action α β :=
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : β, (0 : α) • x = 0)

/-- A module is a generalization of vector spaces to a scalar ring.
  It consists of a scalar ring `α` and an additive group of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class module (α : Type u) (β : Type v) [ring α] [add_comm_group β] extends semimodule α β

end prio

structure module.core (α β) [ring α] [add_comm_group β] extends has_scalar α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀(r s : α) (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)

def module.of_core {α β} [ring α] [add_comm_group β] (M : module.core α β) : module α β :=
by letI := M.to_has_scalar; exact
{ zero_smul := λ x,
    have (0 : α) • x + (0 : α) • x = (0 : α) • x + 0, by rw ← M.add_smul; simp,
    add_left_cancel this,
  smul_zero := λ r,
    have r • (0:β) + r • 0 = r • 0 + 0, by rw ← M.smul_add; simp,
    add_left_cancel this,
  ..M }

section semimodule

variables [semiring α] [add_comm_monoid β] [semimodule α β] (r s : α) (x y : β)

theorem add_smul : (r + s) • x = r • x + s • x := semimodule.add_smul r s x

variables (α)
@[simp] theorem zero_smul : (0 : α) • x = 0 := semimodule.zero_smul α x

end semimodule

section module
variables [ring α] [add_comm_group β] [module α β] (r s : α) (x y : β)

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

variables (α)
theorem neg_one_smul (x : β) : (-1 : α) • x = -x := by simp
variables {α}

@[simp] theorem smul_neg : r • (-x) = -(r • x) :=
by rw [← neg_one_smul α, ← mul_smul, mul_neg_one, neg_smul]

theorem smul_sub (r : α) (x y : β) : r • (x - y) = r • x - r • y :=
by simp [smul_add]; rw smul_neg

theorem sub_smul (r s : α) (y : β) : (r - s) • y = r • y - s • y :=
by simp [add_smul]

end module

