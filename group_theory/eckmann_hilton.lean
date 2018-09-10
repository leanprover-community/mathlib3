/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import tactic.interactive

universe u

namespace eckmann_hilton
variables (X : Type u)

local notation a `<`m`>` b := @has_mul.mul X m a b

class is_unital [m : has_mul X] [e : has_one X] : Prop :=
(one_mul : ∀ x : X, (e.one <m> x) = x)
(mul_one : ∀ x : X, (x <m> e.one) = x)

attribute [simp] is_unital.one_mul is_unital.mul_one

variables {X} {m₁ : has_mul X} {e₁ : has_one X} {m₂ : has_mul X} {e₂ : has_one X}
variables (h₁ : @is_unital X m₁ e₁) (h₂ : @is_unital X m₂ e₂)
variables (distrib : ∀ a b c d, ((a <m₂> b) <m₁> (c <m₂> d)) = ((a <m₁> c) <m₂> (b <m₁> d)))
include h₁ h₂ distrib

lemma one : (e₁.one = e₂.one) :=
by simpa using distrib e₂.one e₁.one e₁.one e₂.one

lemma mul : (m₁.mul = m₂.mul) :=
by funext a b; have := distrib a e₁.one e₁.one b;
simp at this; simpa [one h₁ h₂ distrib] using this

lemma mul_comm : is_commutative _ m₂.mul :=
⟨λ a b, by simpa [mul h₁ h₂ distrib] using distrib e₂.one a b e₂.one⟩

lemma mul_assoc : is_associative _ m₂.mul :=
⟨λ a b c, by simpa [mul h₁ h₂ distrib] using distrib a b e₂.one c⟩

instance : comm_monoid X :=
{ mul_comm := (mul_comm h₁ h₂ distrib).comm,
  mul_assoc := (mul_assoc h₁ h₂ distrib).assoc,
  ..m₂, ..e₂, ..h₂ }

end eckmann_hilton

