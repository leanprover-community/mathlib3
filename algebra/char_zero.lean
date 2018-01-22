/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Natural homomorphism from the natural numbers into a monoid with one.
-/
import data.nat.cast algebra.group algebra.field

/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.) -/
class char_zero (α : Type*) [add_monoid α] [has_one α] : Prop :=
(cast_inj : ∀ {m n : ℕ}, (m : α) = n ↔ m = n)

theorem char_zero_of_inj_zero {α : Type*} [add_monoid α] [has_one α]
  (add_left_cancel : ∀ a b c : α, a + b = a + c → b = c)
  (H : ∀ n:ℕ, (n:α) = 0 → n = 0) : char_zero α :=
⟨λ m n, ⟨suffices ∀ {m n : ℕ}, (m:α) = n → m ≤ n,
  from λ h, le_antisymm (this h) (this h.symm),
  λ m n h, (le_total m n).elim id $ λ h2, le_of_eq $ begin
    cases nat.le.dest h2 with k e,
    suffices : k = 0, {simp [this] at e, rw e},
    apply H, apply add_left_cancel n,
    rw [← nat.cast_add, e, add_zero, h]
  end,
congr_arg _⟩⟩

theorem add_group.char_zero_of_inj_zero {α : Type*} [add_group α] [has_one α]
  (H : ∀ n:ℕ, (n:α) = 0 → n = 0) : char_zero α :=
char_zero_of_inj_zero (@add_left_cancel _ _) H

theorem ordered_cancel_comm_monoid.char_zero_of_inj_zero {α : Type*}
  [ordered_cancel_comm_monoid α] [has_one α]
  (H : ∀ n:ℕ, (n:α) = 0 → n = 0) : char_zero α :=
char_zero_of_inj_zero (@add_left_cancel _ _) H

instance linear_ordered_semiring.to_char_zero {α : Type*}
  [linear_ordered_semiring α] : char_zero α :=
ordered_cancel_comm_monoid.char_zero_of_inj_zero $
λ n h, nat.eq_zero_of_le_zero $
  (@nat.cast_le α _ _ _).1 (by simp [h])

namespace nat
variables {α : Type*} [add_monoid α] [has_one α] [char_zero α]

@[simp] theorem cast_inj {m n : ℕ} : (m : α) = n ↔ m = n :=
char_zero.cast_inj _

theorem cast_injective : function.injective (coe : ℕ → α)
| m n := cast_inj.1

@[simp] theorem cast_eq_zero {n : ℕ} : (n : α) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

@[simp] theorem cast_ne_zero {n : ℕ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

end nat

lemma two_ne_zero' {α : Type*} [add_monoid α] [has_one α] [char_zero α] : (2:α) ≠ 0 :=
by simpa using (@nat.cast_ne_zero α _ _ _ 2).2 dec_trivial

section
variables {α : Type*} [domain α] [char_zero α]

lemma add_self_eq_zero {a : α} : a + a = 0 ↔ a = 0 :=
by rw [← two_mul, mul_eq_zero]; simp [two_ne_zero']

lemma bit0_eq_zero {a : α} : bit0 a = 0 ↔ a = 0 := add_self_eq_zero
end

section
variables {α : Type*} [division_ring α] [char_zero α]

@[simp] lemma half_add_self (a : α) : (a + a) / 2 = a :=
by rw [← mul_two, mul_div_cancel a two_ne_zero']

@[simp] lemma add_halves' (a : α) : a / 2 + a / 2 = a :=
by rw [← add_div, half_add_self]

lemma sub_half (a : α) : a - a / 2 = a / 2 :=
by rw [sub_eq_iff_eq_add, add_halves']

lemma half_sub (a : α) : a / 2 - a = - (a / 2) :=
by rw [← neg_sub, sub_half]

end