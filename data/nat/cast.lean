/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Natural homomorphism from the natural numbers into a monoid with one.
-/
import data.nat.basic algebra.ordered_group

namespace nat
variables {α : Type*}

section
variables [has_zero α] [has_one α] [has_add α]

/-- Canonical homomorphism from `ℕ` to a type `α` with `0`, `1` and `+`. -/
protected def cast : ℕ → α
| 0     := 0
| (n+1) := cast n + 1

@[priority 0] instance cast_coe : has_coe ℕ α := ⟨nat.cast⟩

@[simp] theorem cast_zero : ((0 : ℕ) : α) = 0 := rfl

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : α) = n + 1 := rfl
@[simp] theorem cast_succ (n : ℕ) : ((succ n : ℕ) : α) = n + 1 := rfl
end

@[simp] theorem cast_one [add_monoid α] [has_one α] : ((1 : ℕ) : α) = 1 := zero_add _

@[simp] theorem cast_add [add_monoid α] [has_one α] (m) : ∀ n, ((m + n : ℕ) : α) = m + n
| 0     := (add_zero _).symm
| (n+1) := show ((m + n : ℕ) : α) + 1 = m + (n + 1), by rw [cast_add n, add_assoc]

@[simp] theorem cast_bit0 [add_monoid α] [has_one α] (n : ℕ) : ((bit0 n : ℕ) : α) = bit0 n := cast_add _ _

@[simp] theorem cast_bit1 [add_monoid α] [has_one α] (n : ℕ) : ((bit1 n : ℕ) : α) = bit1 n :=
by rw [bit1, cast_add_one, cast_bit0]; refl

@[simp] theorem cast_pred [add_group α] [has_one α] : ∀ {n}, n > 0 → ((n - 1 : ℕ) : α) = n - 1
| (n+1) h := (add_sub_cancel (n:α) 1).symm

@[simp] theorem cast_sub [add_group α] [has_one α] {m n} (h : m ≤ n) : ((n - m : ℕ) : α) = n - m :=
eq_sub_of_add_eq $ by rw [← cast_add, nat.sub_add_cancel h]

@[simp] theorem cast_mul [semiring α] (m) : ∀ n, ((m * n : ℕ) : α) = m * n
| 0     := (mul_zero _).symm
| (n+1) := (cast_add _ _).trans $
show ((m * n : ℕ) : α) + m = m * (n + 1), by rw [cast_mul n, left_distrib, mul_one]

theorem mul_cast_comm [semiring α] (a : α) (n : ℕ) : a * n = n * a :=
by induction n; simp [left_distrib, right_distrib, *]

@[simp] theorem cast_nonneg [linear_ordered_semiring α] : ∀ n : ℕ, 0 ≤ (n : α)
| 0     := le_refl _
| (n+1) := add_nonneg (cast_nonneg n) zero_le_one

@[simp] theorem cast_le [linear_ordered_semiring α] : ∀ {m n : ℕ}, (m : α) ≤ n ↔ m ≤ n
| 0     n     := by simp [zero_le]
| (m+1) 0     := by simpa [not_succ_le_zero] using
  lt_add_of_lt_of_nonneg zero_lt_one (@cast_nonneg α _ m)
| (m+1) (n+1) := (add_le_add_iff_right 1).trans $
  (@cast_le m n).trans $ (add_le_add_iff_right 1).symm

@[simp] theorem cast_lt [linear_ordered_semiring α] {m n : ℕ} : (m : α) < n ↔ m < n :=
by simpa [-cast_le] using not_congr (@cast_le α _ n m)

@[simp] theorem cast_pos [linear_ordered_ring α] {n : ℕ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_id : ∀ n : ℕ, ↑n = n
| 0     := rfl
| (n+1) := congr_arg (+1) (cast_id n)

@[simp] theorem cast_min [decidable_linear_ordered_semiring α] {a b : ℕ} : (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [h, min]

@[simp] theorem cast_max [decidable_linear_ordered_semiring α] {a b : ℕ} : (↑(max a b) : α) = max a b :=
by by_cases a ≤ b; simp [h, max]

end nat

/-- Typeclass for monoids with characteristic zero. (This is usually stated on fields
  but it makes sense for any additive monoid with 1.) -/
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

@[simp] theorem cast_eq_zero {n : ℕ} : (n : α) = 0 ↔ n = 0 :=
by rw [← cast_zero, cast_inj]

@[simp] theorem cast_ne_zero {n : ℕ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

end nat