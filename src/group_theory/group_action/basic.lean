/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import tactic.split_ifs

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Typeclass for multiplictive actions by monoids. This generalizes group actions. -/
class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
end prio

section
variables [monoid α] [mul_action α β]

theorem mul_smul (a₁ a₂ : α) (b : β) : (a₁ * a₂) • b = a₁ • a₂ • b := mul_action.mul_smul _ _ _

lemma smul_smul (a₁ a₂ : α) (b : β) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

variable (α)
@[simp] theorem one_smul (b : β) : (1 : α) • b = b := mul_action.one_smul α _

variables {α} (p : Prop) [decidable p]

lemma ite_smul (a₁ a₂ : α) (b : β) : (ite p a₁ a₂) • b = ite p (a₁ • b) (a₂ • b) :=
by split_ifs; refl

lemma smul_ite (a : α) (b₁ b₂ : β) : a • (ite p b₁ b₂) = ite p (a • b₁) (a • b₂) :=
by split_ifs; refl

end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β] extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero {} : ∀(r : α), r • (0 : β) = 0)
end prio

variables [monoid α] [add_monoid β] [distrib_mul_action α β]

theorem smul_add (a : α) (b₁ b₂ : β) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : α) : a • (0 : β) = 0 :=
distrib_mul_action.smul_zero _
