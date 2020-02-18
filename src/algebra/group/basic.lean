/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon, Mario Carneiro
-/
import algebra.group.to_additive logic.function

/-!
# Extra identities for semigroups, monoids, and groups
-/

universes u v w
variables {M : Type u} {A : Type v} {G : Type w}

@[to_additive add_monoid_to_is_left_id]
instance monoid_to_is_left_id [monoid M] : is_left_id M (*) 1 :=
⟨ monoid.one_mul ⟩

@[to_additive add_monoid_to_is_right_id]
instance monoid_to_is_right_id [monoid M] : is_right_id M (*) 1 :=
⟨ monoid.mul_one ⟩

@[to_additive]
theorem mul_left_injective [left_cancel_semigroup M] (a : M) : function.injective ((*) a) :=
λ b c, mul_left_cancel

@[to_additive]
theorem mul_right_injective [right_cancel_semigroup M] (a : M) : function.injective (λ x, x * a) :=
λ b c, mul_right_cancel

@[simp, to_additive]
theorem mul_left_inj [left_cancel_semigroup M] (a : M) {b c : M} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[simp, to_additive]
theorem mul_right_inj [right_cancel_semigroup M] (a : M) {b c : M} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

@[to_additive]
theorem mul_mul_mul_comm [comm_semigroup M] {a b c d : M} :
  (a * b) * (c * d) = (a * c) * (b * d) :=
by simp only [mul_left_comm, mul_assoc]

section group
variables [group G] {a b c : G}

@[simp, to_additive]
theorem inv_inj' : a⁻¹ = b⁻¹ ↔ a = b :=
⟨λ h, by rw [← inv_inv a, h, inv_inv], congr_arg _⟩

@[to_additive]
theorem mul_left_surjective (a : G) : function.surjective ((*) a) :=
λ x, ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
theorem mul_right_surjective (a : G) : function.surjective (λ x, x * a) :=
λ x, ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[to_additive]
theorem eq_of_inv_eq_inv : a⁻¹ = b⁻¹ → a = b :=
inv_inj'.1

@[simp, to_additive]
theorem mul_self_iff_eq_one : a * a = a ↔ a = 1 :=
by have := @mul_left_inj _ _ a a 1; rwa mul_one at this

@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
by rw [← @inv_inj' _ _ a 1, one_inv]

@[simp, to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
not_congr inv_eq_one

@[to_additive]
theorem left_inverse_inv (G) [group G] :
function.left_inverse (λ a : G, a⁻¹) (λ a, a⁻¹) :=
inv_inv

attribute [simp] mul_inv_cancel_left add_neg_cancel_left mul_inv_cancel_right add_neg_cancel_right

@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
eq_comm.trans $ eq_inv_iff_eq_inv.trans eq_comm

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
by simpa [mul_left_inv, -mul_right_inj] using @mul_right_inj _ _ b a (b⁻¹)

@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
mul_eq_one_iff_eq_inv.symm

@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
mul_eq_one_iff_inv_eq.symm

@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
⟨λ h, by rw [h, inv_mul_cancel_right], λ h, by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
⟨λ h, by rw [h, mul_inv_cancel_left], λ h, by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
⟨λ h, by rw [← h, mul_inv_cancel_left], λ h, by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
⟨λ h, by rw [← h, inv_mul_cancel_right], λ h, by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b :=
by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
theorem inv_comm_of_comm (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
begin
  have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
    congr_arg (λ x:G, a⁻¹ * x * a⁻¹) H.symm,
  rwa [inv_mul_cancel_left, mul_assoc, mul_inv_cancel_right] at this
end

@[simp, to_additive]
lemma mul_left_eq_self : a * b = b ↔ a = 1 :=
⟨λ h, @mul_right_cancel _ _ a b 1 (by simp [h]), λ h, by simp [h]⟩

@[simp, to_additive]
lemma mul_right_eq_self : a * b = a ↔ b = 1 :=
⟨λ h, @mul_left_cancel _ _ a b 1 (by simp [h]), λ h, by simp [h]⟩

end group

section add_group
variables [add_group A] {a b c d : A}

local attribute [simp] sub_eq_add_neg

@[simp] lemma sub_left_inj : a - b = a - c ↔ b = c :=
(add_left_inj _).trans neg_inj'

@[simp] lemma sub_right_inj : b - a = c - a ↔ b = c :=
add_right_inj _

lemma sub_add_sub_cancel (a b c : A) : (a - b) + (b - c) = a - c :=
by rw [← add_sub_assoc, sub_add_cancel]

lemma sub_sub_sub_cancel_right (a b c : A) : (a - c) - (b - c) = a - b :=
by rw [← neg_sub c b, sub_neg_eq_add, sub_add_sub_cancel]

theorem sub_sub_assoc_swap : a - (b - c) = a + c - b :=
by simp

theorem sub_eq_zero : a - b = 0 ↔ a = b :=
⟨eq_of_sub_eq_zero, λ h, by rw [h, sub_self]⟩

theorem sub_ne_zero : a - b ≠ 0 ↔ a ≠ b :=
not_congr sub_eq_zero

theorem eq_sub_iff_add_eq : a = b - c ↔ a + c = b :=
eq_add_neg_iff_add_eq

theorem sub_eq_iff_eq_add : a - b = c ↔ a = c + b :=
add_neg_eq_iff_eq_add

theorem eq_iff_eq_of_sub_eq_sub (H : a - b = c - d) : a = b ↔ c = d :=
by rw [← sub_eq_zero, H, sub_eq_zero]

theorem left_inverse_sub_add_left (c : A) : function.left_inverse (λ x, x - c) (λ x, x + c) :=
assume x, add_sub_cancel x c

theorem left_inverse_add_left_sub (c : A) : function.left_inverse (λ x, x + c) (λ x, x - c) :=
assume x, sub_add_cancel x c

theorem left_inverse_add_right_neg_add (c : A) :
  function.left_inverse (λ x, c + x) (λ x, - c + x) :=
assume x, add_neg_cancel_left c x

theorem left_inverse_neg_add_add_right (c : A) :
  function.left_inverse (λ x, - c + x) (λ x, c + x) :=
assume x, neg_add_cancel_left c x

end add_group

section add_comm_group
variables [add_comm_group A] {a b c : A}

lemma sub_sub_cancel (a b : A) : a - (a - b) = b := sub_sub_self a b

lemma sub_eq_neg_add (a b : A) : a - b = -b + a :=
add_comm _ _

theorem neg_add' (a b : A) : -(a + b) = -a - b := neg_add a b

lemma neg_sub_neg (a b : A) : -a - -b = b - a := by simp

lemma eq_sub_iff_add_eq' : a = b - c ↔ c + a = b :=
by rw [eq_sub_iff_add_eq, add_comm]

lemma sub_eq_iff_eq_add' : a - b = c ↔ a = b + c :=
by rw [sub_eq_iff_eq_add, add_comm]

lemma add_sub_cancel' (a b : A) : a + b - a = b :=
by rw [sub_eq_neg_add, neg_add_cancel_left]

lemma add_sub_cancel'_right (a b : A) : a + (b - a) = b :=
by rw [← add_sub_assoc, add_sub_cancel']

@[simp] lemma add_add_neg_cancel'_right (a b : A) : a + (b + -a) = b :=
add_sub_cancel'_right a b

lemma sub_right_comm (a b c : A) : a - b - c = a - c - b :=
add_right_comm _ _ _

lemma add_add_sub_cancel (a b c : A) : (a + c) + (b - c) = a + b :=
by rw [add_assoc, add_sub_cancel'_right]

lemma sub_add_add_cancel (a b c : A) : (a - c) + (b + c) = a + b :=
by rw [add_left_comm, sub_add_cancel, add_comm]

lemma sub_add_sub_cancel' (a b c : A) : (a - b) + (c - a) = c - b :=
by rw add_comm; apply sub_add_sub_cancel

lemma add_sub_sub_cancel (a b c : A) : (a + b) - (a - c) = b + c :=
by rw [← sub_add, add_sub_cancel']

lemma sub_sub_sub_cancel_left (a b c : A) : (c - a) - (c - b) = b - a :=
by rw [← neg_sub b c, sub_neg_eq_add, add_comm, sub_add_sub_cancel]

lemma sub_eq_sub_iff_sub_eq_sub {d : A} :
  a - b = c - d ↔ a - c = b - d :=
⟨λ h, by rw eq_add_of_sub_eq h; simp, λ h, by rw eq_add_of_sub_eq h; simp⟩

end add_comm_group

section add_monoid
variables [add_monoid A] {a b c : A}

@[simp] lemma bit0_zero : bit0 (0 : A) = 0 := add_zero _
@[simp] lemma bit1_zero [has_one A] : bit1 (0 : A) = 1 :=
by rw [bit1, bit0_zero, zero_add]

end add_monoid

@[to_additive]
lemma inv_involutive {α} [group α] : function.involutive (has_inv.inv : α → α) := inv_inv
