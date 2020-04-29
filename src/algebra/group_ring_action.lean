/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Group action on rings.
-/

import group_theory.group_action data.equiv.ring

universes u v

variables (α : Type u) (β : Type v)

section prio
set_option default_priority 100 -- see Note [default priority]

/-- Typeclass for multiplicative actions by monoids on monoids. -/
class mul_mul_action [monoid α] [monoid β] extends mul_action α β :=
(smul_one : ∀ (g : α), (g • 1 : β) = 1)
(smul_mul : ∀ (g : α) (x y : β), g • (x * y) = (g • x) * (g • y))

/-- Typeclass for multiplicative actions by monoids on additive monoids. -/
class mul_add_action [monoid α] [add_monoid β] extends mul_action α β :=
(smul_zero : ∀ (g : α), (g • 0 : β) = 0)
(smul_add : ∀ (g : α) (x y : β), g • (x + y) = (g • x) + (g • y))

attribute [to_additive mul_add_action] mul_mul_action

set_option old_structure_cmd true
/-- Typeclass for multiplicative actions by monoids on semirings. -/
class mul_semiring_action [monoid α] [semiring β] extends mul_mul_action α β, mul_add_action α β.
end prio

export mul_mul_action (smul_one smul_mul)
export mul_add_action (smul_zero smul_add)

/-- Each element of the monoid defines a monoid homomorphism. -/
def mul_mul_action.to_mul_hom [monoid α] [monoid β] [mul_mul_action α β] (x : α) : β →* β :=
{ to_fun   := (•) x,
  map_one' := smul_one x,
  map_mul' := smul_mul x }

/-- Each element of the monoid defines a additive monoid homomorphism. -/
def mul_add_action.to_add_hom [monoid α] [add_monoid β] [mul_add_action α β] (x : α) : β →+ β :=
{ to_fun   := (•) x,
  map_zero' := smul_zero x,
  map_add' := smul_add x }

attribute [to_additive mul_add_action.to_add_hom] mul_mul_action.to_mul_hom

/-- Each element of the group defines a monoid isomorphism. -/
def mul_mul_action.to_mul_equiv [group α] [monoid β] [mul_mul_action α β] (x : α) : β ≃* β :=
{ .. mul_mul_action.to_mul_hom α β x,
  .. mul_action.to_perm α β x }

/-- Each element of the group defines an additive monoid isomorphism. -/
def mul_add_action.to_add_equiv [group α] [add_monoid β] [mul_add_action α β] (x : α) : β ≃+ β :=
{ .. mul_add_action.to_add_hom α β x,
  .. mul_action.to_perm α β x }

attribute [to_additive mul_add_action.to_add_equiv] mul_mul_action.to_mul_equiv

/-- Each element of the monoid defines a semiring homomorphism. -/
def mul_semiring_action.to_semiring_hom [monoid α] [semiring β] [mul_semiring_action α β] (x : α) :
  β →+* β :=
{ .. mul_mul_action.to_mul_hom α β x,
  .. mul_add_action.to_add_hom α β x }

/-- Each element of the group defines a semiring isomorphism. -/
def mul_semiring_action.to_semiring_equiv [group α] [semiring β] [mul_semiring_action α β] (x : α) :
  β ≃+* β :=
{ .. mul_mul_action.to_mul_equiv α β x,
  .. mul_add_action.to_add_equiv α β x }

section simp_lemmas

variables {α β}

attribute [simp] smul_one smul_mul smul_zero smul_add

@[simp] lemma smul_inv [monoid α] [group β] [mul_mul_action α β] (x : α) (m : β) :
  x • m⁻¹ = (x • m)⁻¹ :=
(mul_mul_action.to_mul_hom α β x).map_inv m

@[simp] lemma smul_neg [monoid α] [add_group β] [mul_add_action α β] (x : α) (m : β) :
  x • (-m) = -(x • m) :=
(mul_add_action.to_add_hom α β x).map_neg m

@[simp] lemma smul_inv' [monoid α] [field β] [mul_semiring_action α β] (x : α) (m : β) :
  x • m⁻¹ = (x • m)⁻¹ :=
(mul_semiring_action.to_semiring_hom α β x).map_inv

end simp_lemmas
