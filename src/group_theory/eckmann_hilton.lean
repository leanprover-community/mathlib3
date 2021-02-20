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

* `eckmann_hilton.comm_monoid`: If a type carries two unital binary operations that distribute
  over each other, then these operations are equal, and form a commutative monoid structure.
* `eckmann_hilton.comm_group`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/


universe u

namespace eckmann_hilton
variables {X : Type u}

local notation a `<`m`>` b := m a b

/-- `is_unital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
class is_unital (m : X → X → X) (e : X) : Prop :=
(one_mul : ∀ x : X, (e <m> x) = x)
(mul_one : ∀ x : X, (x <m> e) = x)

@[to_additive add_group.is_unital]
lemma group.is_unital [G : group X] : is_unital (*) (1 : X) := { ..G }

variables {m₁ m₂ : X → X → X} {e₁ e₂ : X}
variables (h₁ : is_unital m₁ e₁) (h₂ : is_unital m₂ e₂)
variables (distrib : ∀ a b c d, ((a <m₂> b) <m₁> (c <m₂> d)) = ((a <m₁> c) <m₂> (b <m₁> d)))
include h₁ h₂ distrib

/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.comm_monoid`. -/
lemma one : e₁ = e₂ :=
by simpa only [h₁.one_mul, h₁.mul_one, h₂.one_mul, h₂.mul_one] using distrib e₂ e₁ e₁ e₂

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
lemma mul : (m₁ = m₂) :=
begin
  funext a b,
  calc m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) :
    by simp only [one h₁ h₂ distrib, h₁.one_mul, h₁.mul_one, h₂.one_mul, h₂.mul_one]
          ... = m₂ a b :
    by simp only [distrib, h₁.one_mul, h₁.mul_one, h₂.one_mul, h₂.mul_one]
end

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
lemma mul_comm : is_commutative _ m₂ :=
⟨λ a b, by simpa [mul h₁ h₂ distrib, h₂.one_mul, h₂.mul_one] using distrib e₂ a b e₂⟩

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
lemma mul_assoc : is_associative _ m₂ :=
⟨λ a b c, by simpa [mul h₁ h₂ distrib, h₂.one_mul, h₂.mul_one] using distrib a b e₂ c⟩

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal, and form a commutative monoid structure. -/
@[to_additive "If a type carries two unital binary operations that distribute over each other,
then these operations are equal, and form a additive commutative monoid structure."]
def comm_monoid : comm_monoid X :=
{ mul := m₂,
  one := e₂,
  mul_comm := (mul_comm h₁ h₂ distrib).comm,
  mul_assoc := (mul_assoc h₁ h₂ distrib).assoc,
  ..h₂ }

omit h₁ h₂ distrib

/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
@[to_additive "If a type carries an additive group structure that distributes
over a unital binary operation, then the additive group is commutative."]
def comm_group [G : group X]
  (distrib : ∀ a b c d, ((a * b) <m₁> (c * d)) = ((a <m₁> c) * (b <m₁> d))) : comm_group X :=
{ mul_comm := (eckmann_hilton.comm_monoid h₁ group.is_unital distrib).mul_comm,
  ..G }

end eckmann_hilton
