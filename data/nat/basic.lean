/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro

Basic operations on the natural numbers.
-/
import logic.basic

universe u

namespace nat

protected theorem eq_mul_of_div_eq_right {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : 
  a = b * c := 
by rw [← H2, nat.mul_div_cancel' H1] 
 
protected theorem div_eq_iff_eq_mul_right {a b c : ℕ} (H : b > 0) (H' : b ∣ a) : 
  a / b = c ↔ a = b * c := 
⟨nat.eq_mul_of_div_eq_right H', nat.div_eq_of_eq_mul_right H⟩ 
 
protected theorem div_eq_iff_eq_mul_left {a b c : ℕ} (H : b > 0) (H' : b ∣ a) : 
  a / b = c ↔ a = c * b := 
by rw mul_comm; exact nat.div_eq_iff_eq_mul_right H H' 
 
protected theorem eq_mul_of_div_eq_left {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : 
  a = c * b := 
by rw [mul_comm, nat.eq_mul_of_div_eq_right H1 H2]

theorem add_pos_left {m : ℕ} (h : m > 0) (n : ℕ) : m + n > 0 :=
calc
  m + n > 0 + n : nat.add_lt_add_right h n
    ... = n     : nat.zero_add n
    ... ≥ 0     : zero_le n

theorem add_pos_right (m : ℕ) {n : ℕ} (h : n > 0) : m + n > 0 :=
begin rw add_comm, exact add_pos_left h m end

theorem add_pos_iff_pos_or_pos (m n : ℕ) : m + n > 0 ↔ m > 0 ∨ n > 0 :=
iff.intro
  begin
    intro h,
    cases m with m,
    {simp [zero_add] at h, exact or.inr h},
    exact or.inl (succ_pos _)
  end
  begin
    intro h, cases h with mpos npos,
    { apply add_pos_left mpos },
    apply add_pos_right _ npos
  end

theorem succ_le_succ_iff (m n : ℕ) : succ m ≤ succ n ↔ m ≤ n :=
⟨le_of_succ_le_succ, succ_le_succ⟩

theorem lt_succ_iff_le (m n : ℕ) : m < succ n ↔ m ≤ n :=
succ_le_succ_iff m n

lemma le_zero_iff {i : ℕ} : i ≤ 0 ↔ i = 0 :=
⟨nat.eq_zero_of_le_zero, assume h, h ▸ le_refl i⟩

lemma le_add_one_iff {i j : ℕ} : i ≤ j + 1 ↔ (i ≤ j ∨ i = j + 1) :=
⟨assume h,
  match nat.eq_or_lt_of_le h with
  | or.inl h := or.inr h
  | or.inr h := or.inl $ nat.le_of_succ_le_succ h
  end,
  or.rec (assume h, le_trans h $ nat.le_add_right _ _) le_of_eq⟩

end nat
