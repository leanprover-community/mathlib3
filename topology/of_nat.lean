/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Morphism from `nat` into a semiring with 1.

TODO: move to `data.nat` and split into the different parts for `int`, `rat`, and `real`.
-/
import data.rat topology.real

section of_nat
variables {α : Type*} [semiring α] {n : ℕ}

@[simp] def of_nat : ℕ → α
| 0            := 0
| (nat.succ n) := of_nat n + 1

@[simp] lemma of_nat_add : ∀{m}, of_nat (n + m) = (of_nat n + of_nat m : α)
| 0       := by simp
| (m + 1) := calc of_nat (n + (m + 1)) = of_nat (nat.succ (n + m)) :
    by rw [nat.succ_eq_add_one]; simp
  ... = (of_nat n + of_nat (nat.succ m) : α) :
    by simp [of_nat_add]

@[simp] lemma of_nat_one : of_nat 1 = (1 : α) :=
calc of_nat 1 = 0 + 1 : rfl
 ... = (1:α) : by simp

@[simp] lemma of_nat_mul : ∀{m}, of_nat (n * m) = (of_nat n * of_nat m : α)
| 0       := by simp
| (m + 1) := by simp [mul_add, of_nat_mul]

@[simp] lemma of_nat_bit0 : of_nat (bit0 n) = (bit0 (of_nat n) : α) := of_nat_add

@[simp] lemma of_nat_bit1 : of_nat (bit0 n) = (bit0 (of_nat n) : α) := of_nat_add

lemma of_nat_sub {α : Type*} [ring α] {n m : ℕ} (h : m ≤ n) :
  of_nat (n - m) = (of_nat n - of_nat m : α) :=
calc of_nat (n - m) = (of_nat ((n - m) + m) - of_nat m : α) : by simp
  ... = (of_nat n - of_nat m : α) : by rw [nat.sub_add_cancel h]

end of_nat

lemma int_of_nat_eq_of_nat : ∀{n : ℕ}, int.of_nat n = of_nat n
| 0       := rfl
| (n + 1) := by simp [int.of_nat_add, int.of_nat_one, @int_of_nat_eq_of_nat n]

lemma rat_of_nat_eq_of_nat : ∀{n : ℕ}, (↑(of_nat n : ℤ) : ℚ) = of_nat n
| 0       := rfl
| (n + 1) :=
  by rw [of_nat_add, rat.coe_int_add, of_nat_one, rat.coe_int_one, rat_of_nat_eq_of_nat]; simp

lemma rat_coe_eq_of_nat {n : ℕ} : (↑n : ℚ) = of_nat n :=
show ↑(int.of_nat n) = (of_nat n : ℚ), by rw [int_of_nat_eq_of_nat, rat_of_nat_eq_of_nat]

lemma real_of_rat_of_nat_eq_of_nat : ∀{n : ℕ}, of_rat (of_nat n) = of_nat n
| 0     := rfl
| (n+1) := by simp [of_rat_add.symm, of_rat_one.symm, real_of_rat_of_nat_eq_of_nat]

section of_nat_order
variables {α : Type*} [linear_ordered_semiring α]

lemma zero_le_of_nat : ∀{n}, 0 ≤ (of_nat n : α)
| 0       := le_refl 0
| (n + 1) := le_add_of_le_of_nonneg zero_le_of_nat (zero_le_one)

lemma of_nat_pos : ∀{n}, 0 < n → 0 < (of_nat n : α)
| 0       h := (lt_irrefl 0 h).elim
| (n + 1) h := by simp; exact lt_add_of_le_of_pos zero_le_of_nat zero_lt_one

lemma of_nat_le_of_nat {n m : ℕ} (h : n ≤ m) : of_nat n ≤ (of_nat m : α) :=
let ⟨k, hk⟩ := nat.le.dest h in
by simp [zero_le_of_nat, hk.symm]

lemma of_nat_le_of_nat_iff {n m : ℕ} : of_nat n ≤ (of_nat m : α) ↔ n ≤ m :=
suffices of_nat n ≤ (of_nat m : α) → n ≤ m,
  from iff.intro this of_nat_le_of_nat,
begin
  induction n generalizing m,
  case nat.zero { simp [nat.zero_le] },
  case nat.succ n ih {
    cases m,
    case nat.zero {
      exact assume h,
        have of_nat (n + 1) = (0:α), from le_antisymm h zero_le_of_nat,
        have 1 ≤ (0:α),
          from calc (1:α) ≤ of_nat n + 1 : le_add_of_nonneg_left zero_le_of_nat
            ... = (0:α) : this,
        absurd this $ not_le_of_gt zero_lt_one },
    case nat.succ m {
      exact assume h,
        have 1 + of_nat n ≤ (1 + of_nat m : α), by simp * at *,
        have of_nat n ≤ (of_nat m : α), from le_of_add_le_add_left this,
        show nat.succ n ≤ nat.succ m,
          from nat.succ_le_succ $ ih this } }
end

end of_nat_order

lemma exists_lt_of_nat {r : ℝ} : ∃n, r < of_nat n :=
let ⟨q, hq⟩ := exists_lt_of_rat r in
⟨rat.nat_ceil q, calc r < of_rat q : hq
  ... ≤ of_rat (↑(int.of_nat $ rat.nat_ceil q)) : of_rat_le_of_rat.mpr $ rat.le_nat_ceil q
  ... = of_nat (rat.nat_ceil q) :
    by simp [int_of_nat_eq_of_nat, rat_of_nat_eq_of_nat, real_of_rat_of_nat_eq_of_nat]⟩

