/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/

import tactic.ring
import tactic.abel

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`: a typeclass for rings where multiplication is idempotent.
* `boolean_ring.to_boolean_algebra`: every Boolean ring is a Boolean algebra; this definition and
  the `sup` and `inf` notations for `boolean_ring` are localized as instances in the
  `boolean_algebra_of_boolean_ring` locale.

## Tags

boolean ring, boolean algebra

-/

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class boolean_ring α extends ring α :=
(mul_idem : ∀ a : α, a * a = a)

open boolean_ring
variables {α : Type*} [boolean_ring α]

instance : is_idempotent α (*) := ⟨mul_idem⟩

@[simp] lemma add_self (a : α) : a + a = 0 :=
have a + a = a + a + (a + a) :=
  calc a + a = (a+a) * (a+a)           : by rw mul_idem
         ... = a*a + a*a + (a*a + a*a) : by rw [add_mul, mul_add]
         ... = a + a + (a + a)         : by rw mul_idem,
by rwa self_eq_add_left at this

@[simp] lemma neg_eq (a : α) : -a = a :=
calc -a = -a + 0      : by rw add_zero
    ... = -a + -a + a : by rw [←neg_add_self, add_assoc]
    ... = a           : by rw [add_self, zero_add]

lemma add_eq_zero (a b : α) : a + b = 0 ↔ a = b :=
calc a + b = 0 ↔ a = -b : add_eq_zero_iff_eq_neg
           ... ↔ a = b  : by rw neg_eq

lemma mul_add_mul (a b : α) : a*b + b*a = 0 :=
have a + b = a + b + (a*b + b*a) :=
  calc a + b = (a + b) * (a + b)       : by rw mul_idem
         ... = a*a + a*b + (b*a + b*b) : by rw [add_mul, mul_add, mul_add]
         ... = a + a*b + (b*a + b)     : by simp only [mul_idem]
         ... = a + b + (a*b + b*a)     : by abel,
by rwa self_eq_add_right at this

namespace boolean_ring

@[priority 100] -- Note [lower instance priority]
instance : comm_ring α :=
{ mul_comm := λ a b, by rw [←add_eq_zero, mul_add_mul],
  .. (infer_instance : boolean_ring α) }

/-- The join operation in a Boolean ring is `x + y + x*y`. -/
def has_sup : has_sup α := ⟨λ x y, x + y + x*y⟩
/-- The meet operation in a Boolean ring is `x * y`. -/
def has_inf : has_inf α := ⟨(*)⟩

-- Note [lower instance priority]
localized "attribute [instance, priority 100] boolean_ring.has_sup" in
  boolean_algebra_of_boolean_ring
localized "attribute [instance, priority 100] boolean_ring.has_inf" in
  boolean_algebra_of_boolean_ring

lemma sup_comm (a b : α) : a ⊔ b = b ⊔ a := by { dsimp only [(⊔)], ring }
lemma inf_comm (a b : α) : a ⊓ b = b ⊓ a := by { dsimp only [(⊓)], ring }

lemma sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by { dsimp only [(⊔)], ring }
lemma inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by { dsimp only [(⊓)], ring }

lemma sup_inf_self (a b : α) : a ⊔ a ⊓ b = a :=
by { dsimp only [(⊔), (⊓)], assoc_rw [mul_idem, add_self, add_zero] }
lemma inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a :=
by { dsimp only [(⊔), (⊓)], assoc_rw [mul_add, mul_add, mul_idem, mul_idem, add_self, add_zero] }

lemma le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
calc (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) +
          (a * b + (a * a) * b) +
          (a * c + (a * a) * c) +
          (a * b * c + (a * a) * b * c) : by ring
... = a + b * c + a * (b * c)           : by simp only [mul_idem, add_self, add_zero]

lemma le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c :=
by { dsimp only [(⊔), (⊓)], rw [le_sup_inf_aux, add_self, mul_idem, zero_add] }

/--
The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + a)`
-/
def to_boolean_algebra : boolean_algebra α :=
{ le_sup_inf := le_sup_inf,
  top := 1,
  le_top := λ a, show a + 1 + a * 1 = 1, by assoc_rw [mul_one, add_comm, add_self, add_zero],
  bot := 0,
  bot_le := λ a, show 0 + a + 0 * a = a, by rw [zero_mul, zero_add, add_zero],
  compl := λ a, 1 + a,
  sdiff := λ a b, a * (1 + b),
  inf_compl_le_bot := λ a,
    show a*(1+a) + 0 + a*(1+a)*0 = 0,
    by norm_num [mul_add, mul_idem, add_self],
  top_le_sup_compl := λ a,
    begin
      change 1 + (a + (1+a) + a*(1+a)) + 1*(a + (1+a) + a*(1+a)) = a + (1+a) + a*(1+a),
      norm_num [mul_add, mul_idem],
      rw [←add_assoc, add_self],
    end,
  sdiff_eq := λ a b, rfl,
  .. lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self }

localized "attribute [instance, priority 100] boolean_ring.to_boolean_algebra" in
  boolean_algebra_of_boolean_ring

end boolean_ring
