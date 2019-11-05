/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The `even` predicate on the integers.
-/
import .modeq data.nat.parity algebra.group_power

namespace int

@[simp] theorem mod_two_ne_one {n : int} : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

@[simp] theorem mod_two_ne_zero {n : int} : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

def even (n : int) : Prop := 2 ∣ n

@[simp] theorem even_coe_nat (n : nat) : even n ↔ nat.even n :=
have ∀ m, 2 * to_nat m = to_nat (2 * m),
 from λ m, by cases m; refl,
⟨λ ⟨m, hm⟩, ⟨to_nat m, by rw [this, ←to_nat_coe_nat n, hm]⟩,
 λ ⟨m, hm⟩, ⟨m, by simp [hm]⟩⟩

theorem even_iff {n : int} : even n ↔ n % 2 = 0 :=
⟨λ ⟨m, hm⟩, by simp [hm], λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [h])⟩⟩

instance : decidable_pred even :=
λ n, decidable_of_decidable_of_iff (by apply_instance) even_iff.symm

@[simp] theorem even_zero : even (0 : int) := ⟨0, dec_trivial⟩

@[simp] theorem not_even_one : ¬ even (1 : int) :=
by rw even_iff; apply one_ne_zero

@[simp] theorem even_bit0 (n : int) : even (bit0 n) :=
⟨n, by rw [bit0, two_mul]⟩

@[parity_simps] theorem even_add {m n : int} : even (m + n) ↔ (even m ↔ even n) :=
begin
  cases mod_two_eq_zero_or_one m with h₁ h₁; cases mod_two_eq_zero_or_one n with h₂ h₂;
    simp [even_iff, h₁, h₂],
  { exact @modeq.modeq_add _ _ 0 _ 0 h₁ h₂ },
  { exact @modeq.modeq_add _ _ 0 _ 1 h₁ h₂ },
  { exact @modeq.modeq_add _ _ 1 _ 0 h₁ h₂ },
  exact @modeq.modeq_add _ _ 1 _ 1 h₁ h₂
end

@[parity_simps] theorem even_neg {n : ℤ} : even (-n) ↔ even n := by simp [even]

@[simp] theorem not_even_bit1 (n : int) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

@[parity_simps] theorem even_sub {m n : int} : even (m - n) ↔ (even m ↔ even n) :=
by simp with parity_simps

@[parity_simps] theorem even_mul {m n : int} : even (m * n) ↔ even m ∨ even n :=
begin
  cases mod_two_eq_zero_or_one m with h₁ h₁; cases mod_two_eq_zero_or_one n with h₂ h₂;
    simp [even_iff, h₁, h₂],
  { exact @modeq.modeq_mul _ _ 0 _ 0 h₁ h₂ },
  { exact @modeq.modeq_mul _ _ 0 _ 1 h₁ h₂ },
  { exact @modeq.modeq_mul _ _ 1 _ 0 h₁ h₂ },
  exact @modeq.modeq_mul _ _ 1 _ 1 h₁ h₂
end

@[parity_simps] theorem even_pow {m : int} {n : nat} : even (m^n) ↔ even m ∧ n ≠ 0 :=
by { induction n with n ih; simp [*, even_mul, pow_succ], tauto }

-- Here are examples of how `parity_simps` can be used with `int`.

example (m n : int) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even (25394535 : int) :=
by simp

end int
