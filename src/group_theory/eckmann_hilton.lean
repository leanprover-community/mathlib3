/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis
-/
import algebra.group.basic

/-!
# Eckmann-Hilton argument

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `eckmann_hilton.comm_monoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `eckmann_hilton.comm_group`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/


universe u

namespace eckmann_hilton
variables {X : Type u}

local notation a `<`m`>` b := m a b

/-- `is_unital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
structure is_unital (m : X → X → X) (e : X) extends is_left_id _ m e, is_right_id _ m e : Prop.

@[to_additive eckmann_hilton.add_zero_class.is_unital]
lemma mul_one_class.is_unital [G : mul_one_class X] : is_unital (*) (1 : X) :=
is_unital.mk (by apply_instance) (by apply_instance)

variables {m₁ m₂ : X → X → X} {e₁ e₂ : X}
variables (h₁ : is_unital m₁ e₁) (h₂ : is_unital m₂ e₂)
variables (distrib : ∀ a b c d, ((a <m₂> b) <m₁> (c <m₂> d)) = ((a <m₁> c) <m₂> (b <m₁> d)))
include h₁ h₂ distrib

/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.comm_monoid`. -/
lemma one : e₁ = e₂ :=
by simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using distrib e₂ e₁ e₁ e₂

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
lemma mul : m₁ = m₂ :=
begin
  funext a b,
  calc m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) :
    by simp only [one h₁ h₂ distrib, h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id]
          ... = m₂ a b :
    by simp only [distrib, h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id]
end

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
lemma mul_comm : is_commutative _ m₂ :=
⟨λ a b, by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib e₂ a b e₂⟩

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
lemma mul_assoc : is_associative _ m₂ :=
⟨λ a b c, by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib a b e₂ c⟩

omit h₁ h₂ distrib

/-- If a type carries a unital magma structure that distributes over a unital binary
operations, then the magma structure is a commutative monoid. -/
@[to_additive "If a type carries a unital additive magma structure that distributes over a
unital binary operations, then the additive magma structure is a commutative additive monoid."]
def comm_monoid [h : mul_one_class X]
  (distrib : ∀ a b c d, ((a * b) <m₁> (c * d)) = ((a <m₁> c) * (b <m₁> d))) : comm_monoid X :=
{ mul := (*),
  one := 1,
  mul_comm := (mul_comm h₁ mul_one_class.is_unital distrib).comm,
  mul_assoc := (mul_assoc h₁ mul_one_class.is_unital distrib).assoc,
  ..h }

/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
@[to_additive "If a type carries an additive group structure that distributes
over a unital binary operation, then the additive group is commutative."]
def comm_group [G : group X]
  (distrib : ∀ a b c d, ((a * b) <m₁> (c * d)) = ((a <m₁> c) * (b <m₁> d))) : comm_group X :=
{ ..(eckmann_hilton.comm_monoid h₁ distrib),
  ..G }

end eckmann_hilton
