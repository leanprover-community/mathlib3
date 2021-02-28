/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/

import algebra.ring.basic
import order.symm_diff
import tactic.ring
import tactic.abel

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`
* `boolean_ring.to_boolean_algebra`: every Boolean ring is a Boolean algebra

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

@[priority 100] -- Note [lower instance priority]
instance : has_sup α := ⟨λ x y, x + y + x*y⟩

@[priority 100] -- Note [lower instance priority]
instance : has_inf α := ⟨(*)⟩

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

end boolean_ring

namespace boolean_algebra

/-- Every Boolean algebra has the structure of a Boolean ring, with `inf` as multiplication
and symmetric difference as addition. -/
def to_boolean_ring (α : Type*) [boolean_algebra α] : boolean_ring α :=
{ add := (Δ),
  add_assoc := symm_diff_assoc,
  zero := ⊥,
  zero_add := λ b, by simp [(+), symm_diff_eq],
  add_zero := λ b, by simp [(+), symm_diff_eq],
  neg := λ a, a,
  add_left_neg := λ b,
    begin
      simp only [has_neg.neg, (+), add_semigroup.add, add_monoid.add, symm_diff_eq, sup_bot_eq,
        inf_compl_eq_bot],
      refl,
    end,
  add_comm := symm_diff_comm,
  mul := (⊓),
  mul_assoc := λ a b c, by simp only [(*), inf_assoc],
  one := ⊤,
  one_mul := λ b, by simp [(*)],
  mul_one := λ b, by simp [(*)],
  left_distrib := λ a b c,
    begin
      simp only [symm_diff_eq, compl_inf, inf_sup_left, inf_assoc],
      rw [@inf_comm _ _ b aᶜ, ←@inf_assoc _ _ a aᶜ, inf_compl_eq_bot, bot_inf_eq,
        bot_sup_eq, @inf_comm _ _ c aᶜ, ←@inf_assoc _ _ a aᶜ,
        inf_compl_eq_bot, bot_inf_eq, bot_sup_eq],
    end,
  right_distrib := λ a b c,
    begin
      simp only [symm_diff_eq, compl_inf, inf_sup_right, inf_assoc, inf_sup_left],
      rw [@inf_comm _ _ c, @inf_comm _ _ c aᶜ, inf_compl_eq_bot, inf_bot_eq, inf_bot_eq,
        sup_bot_eq, sup_bot_eq],
    end,
  mul_idem := λ b, inf_idem }

-------------------------------

/-
@[class]
structure boolean_algebra : Type u_1 → Type u_1
fields:
boolean_algebra.sup : Π {α : Type u_1} [c : boolean_algebra α], α → α → α
boolean_algebra.le : Π {α : Type u_1} [c : boolean_algebra α], α → α → Prop
boolean_algebra.lt : Π {α : Type u_1} [c : boolean_algebra α], α → α → Prop
boolean_algebra.inf : Π {α : Type u_1} [c : boolean_algebra α], α → α → α
boolean_algebra.top : Π {α : Type u_1} [c : boolean_algebra α], α
boolean_algebra.bot : Π {α : Type u_1} [c : boolean_algebra α], α
boolean_algebra.compl : Π {α : Type u_1} [c : boolean_algebra α], α → α
boolean_algebra.sdiff : Π {α : Type u_1} [c : boolean_algebra α], α → α → α
-/

lemma to_boolean_ring.sup_eq (α : Type*) (BA : boolean_algebra α) :
  (@boolean_ring.to_boolean_algebra α (@boolean_algebra.to_boolean_ring α BA)).sup = BA.sup :=
symm_diff_symm_diff_sup _ _

lemma to_boolean_ring.le_iff (α : Type*) (BA : boolean_algebra α) :
  (@boolean_ring.to_boolean_algebra α (@boolean_algebra.to_boolean_ring α BA)).le = BA.le :=
begin
  ext a b,
  change a Δ b Δ (a ⊓ b) = b ↔ a ≤ b,
  simp [symm_diff_symm_diff_sup],
end

lemma to_boolean_ring.lt_iff (α : Type*) (BA : boolean_algebra α) :
  (@boolean_ring.to_boolean_algebra α (@boolean_algebra.to_boolean_ring α BA)).lt = BA.lt :=
begin
  ext a b,
  change a Δ b Δ (a ⊓ b) = b ∧ b Δ a Δ (b ⊓ a) ≠ a ↔ a < b,
  simp [symm_diff_symm_diff_sup, lt_iff_le_not_le],
  refl,
end

-- lemma foo2 (α : Type*) [boolean_algebra α] (a b : α) :
--   a ⊓ b = a Δ b Δ (a ⊓ b) :=
-- by rw [symm_diff_assoc, symm_diff_eq, compl_symm_diff, symm_diff_eq, @inf_comm _ _ a b, ←inf_assoc,
--   inf_idem, @inf_comm _ _ b a, inf_assoc, inf_compl_eq_bot, inf_bot_eq, sup_bot_eq,
--   compl_inf, @sup_comm _ _ aᶜ, inf_sup_self, inf_assoc, @inf_comm _ _ _ aᶜ, @sup_comm _ _ bᶜ,
--   inf_sup_self, inf_sup_left, ←inf_assoc, inf_idem, blah]

lemma to_boolean_ring.inf_eq (α : Type*) (BA : boolean_algebra α) :
  BA.inf = (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).inf :=
rfl

lemma to_boolean_ring.top_eq (α : Type*) (BA : boolean_algebra α) :
  BA.top = (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).top :=
rfl

lemma to_boolean_ring.bot_eq (α : Type*) (BA : boolean_algebra α) :
  BA.bot = (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).bot :=
rfl

lemma to_boolean_ring.compl_eq (α : Type*) (BA : boolean_algebra α) :
  (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).compl = BA.compl :=
top_symm_diff _

lemma to_boolean_ring.sdiff_eq (α : Type*) (BA : boolean_algebra α) :
  BA.sdiff = (@boolean_ring.to_boolean_algebra α (@to_boolean_ring α BA)).sdiff :=
begin
  ext a b,
  change a \ b = a ⊓ (⊤ Δ b),
  rw [top_symm_diff, sdiff_eq],
  refl,
end

end boolean_algebra


namespace boolean_ring
/-
ring.add : Π {α : Type u} [c : ring α], α → α → α
ring.zero : Π {α : Type u} [c : ring α], α
ring.neg : Π {α : Type u} [c : ring α], α → α
ring.sub : Π {α : Type u} [c : ring α], α → α → α
ring.mul : Π {α : Type u} [c : ring α], α → α → α
ring.one : Π {α : Type u} [c : ring α], α
-/

lemma blah (α : Type*) (BR : boolean_ring α) (a b : α) :
  (a * (1 + b)) + (b * (1 + a)) + (a * (1 + b)) * (b * (1 + a)) = a + b :=
calc (a * (1 + b)) + (b * (1 + a)) + (a * (1 + b)) * (b * (1 + a)) =
    a + b + (a * b + a * b) + (a * b + (a * a)*b) + (a * (b * b) + (a*a)*(b*b)) : by ring
  ... = a+b : by simp only [mul_idem, add_self, add_zero]

lemma to_boolean_algebra.add_eq (α : Type*) (BR : boolean_ring α) :
  BR.add = (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).add :=
begin
  ext a b,
  exact (boolean_ring.blah _ _ _ _).symm
end

lemma to_boolean_algebra.zero_eq (α : Type*) (BR : boolean_ring α) :
  BR.zero = (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).zero :=
rfl

lemma to_boolean_algebra.neg_eq (α : Type*) (BR : boolean_ring α) :
  BR.neg = (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).neg :=
funext $ neg_eq

lemma blah2 (α : Type*) (BR : boolean_ring α) (a b : α) :
  a - b = a + b :=
by rw [sub_eq_add_neg, add_right_inj, neg_eq]

lemma to_boolean_algebra.sub_eq (α : Type*) (BR : boolean_ring α) :
  BR.sub = (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).sub :=
begin
  ext a b,
  change a - b = (a * (1 + b)) + (b * (1 + a)) + (a * (1 + b)) * (b * (1 + a)),
  rw [blah, boolean_ring.blah2],
end

lemma to_boolean_algebra.mul_eq (α : Type*) (BR : boolean_ring α) :
  BR.mul = (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).mul :=
rfl

lemma to_boolean_algebra.one_eq (α : Type*) (BR : boolean_ring α) :
  BR.one = (@boolean_algebra.to_boolean_ring α (@to_boolean_algebra α BR)).one :=
rfl

end boolean_ring
