/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad

Modules over a ring.
-/
import .field

universes u v

class has_scalar (α : inout Type u) (γ : Type v) := (smul : α → γ → γ)

infixl ` • `:73 := has_scalar.smul

class module (α : inout Type u) (β : Type v) [ring α] extends has_scalar α β, add_comm_group β :=
(smul_left_distrib  : ∀r (x y : β), r • (x + y) = r • x + r • y)
(smul_right_distrib : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul           : ∀r s (x : β), (r * s) • x = r • (s • x))
(one_smul           : ∀x : β, (1 : α) • x = x)

section module
variables {α : Type u} {β : Type v} [ring α] [module α β]
variables {a b c : α} {u v w : β}

theorem smul_left_distrib : a • (u + v) = a • u + a • v := module.smul_left_distrib a u v
theorem smul_right_distrib : (a + b) • u = a • u + b • u := module.smul_right_distrib a b u
theorem mul_smul : (a * b) • u = a • (b • u) :=  module.mul_smul a b u
@[simp] theorem one_smul : (1 : α) • u = u := module.one_smul _ u

@[simp] theorem zero_smul : (0 : α) • u = 0 :=
have (0 : α) • u + 0 • u = 0 • u + 0, by rewrite [←smul_right_distrib]; simp,
add_left_cancel this

@[simp] theorem smul_zero : a • (0 : β) = 0 :=
have a • (0:β) + a • 0 = a • 0 + 0, by rewrite [←smul_left_distrib]; simp,
add_left_cancel this

@[simp] theorem neg_smul : (-a) • u = - (a • u) :=
eq_neg_of_add_eq_zero (by rewrite [←smul_right_distrib, add_left_neg, zero_smul])

@[simp] theorem smul_neg : a • (-u) = -(a • u) :=
calc a • (-u) = a • (-(1 • u)) : by simp
  ... = (a * -1) • u : by rw [←neg_smul, mul_smul]; simp
  ... = -(a • u) : by rw [mul_neg_eq_neg_mul_symm]; simp

theorem smul_sub_left_distrib (a : α) (u v : β) : a • (u - v) = a • u - a • v :=
by simp [smul_left_distrib]

theorem sub_smul_right_distrib (a b : α) (v : β) : (a - b) • v = a • v - b • v :=
by simp [smul_right_distrib]

lemma smul_smul : a • (b • u) = (a * b) • u := mul_smul.symm

end module

def ring.to_module {α : Type u} [r : ring α] : module α α :=
{ r with
  smul := λa b, a * b,
  smul_left_distrib := assume a b c, mul_add _ _ _,
  smul_right_distrib := assume a b c, add_mul _ _ _,
  mul_smul := assume a b c, mul_assoc _ _ _,
  one_smul := assume a, one_mul _ }
