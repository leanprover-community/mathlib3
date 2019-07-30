/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The `even` predicate on the natural numbers.
-/
import .modeq

namespace nat

@[simp] theorem mod_two_ne_one {n : nat} : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

@[simp] theorem mod_two_ne_zero {n : nat} : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

def even (n : nat) : Prop := 2 ∣ n

theorem even_iff {n : nat} : even n ↔ n % 2 = 0 :=
⟨λ ⟨m, hm⟩, by simp [hm], λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [h])⟩⟩

instance : decidable_pred even :=
λ n, decidable_of_decidable_of_iff (by apply_instance) even_iff.symm

run_cmd mk_simp_attr `parity_simps

@[simp] theorem even_zero : even 0 := ⟨0, dec_trivial⟩

@[simp] theorem not_even_one : ¬ even 1 :=
by rw even_iff; apply one_ne_zero

@[simp] theorem even_bit0 (n : nat) : even (bit0 n) :=
⟨n, by rw [bit0, two_mul]⟩

@[parity_simps] theorem even_add {m n : nat} : even (m + n) ↔ (even m ↔ even n) :=
begin
  cases mod_two_eq_zero_or_one m with h₁ h₁; cases mod_two_eq_zero_or_one n with h₂ h₂;
    simp [even_iff, h₁, h₂],
  { exact @modeq.modeq_add _ _ 0 _ 0 h₁ h₂ },
  { exact @modeq.modeq_add _ _ 0 _ 1 h₁ h₂ },
  { exact @modeq.modeq_add _ _ 1 _ 0 h₁ h₂ },
  exact @modeq.modeq_add _ _ 1 _ 1 h₁ h₂
end

@[simp] theorem not_even_bit1 (n : nat) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

@[parity_simps] theorem even_sub {m n : nat} (h : m ≥ n) : even (m - n) ↔ (even m ↔ even n) :=
begin
  conv { to_rhs, rw [←nat.sub_add_cancel h, even_add] },
  by_cases h : even n; simp [h]
end

@[parity_simps] theorem even_succ {n : nat} : even (succ n) ↔ ¬ even n :=
by rw [succ_eq_add_one, even_add]; simp [not_even_one]

@[parity_simps] theorem even_mul {m n : nat} : even (m * n) ↔ even m ∨ even n :=
begin
  cases mod_two_eq_zero_or_one m with h₁ h₁; cases mod_two_eq_zero_or_one n with h₂ h₂;
    simp [even_iff, h₁, h₂],
  { exact @modeq.modeq_mul _ _ 0 _ 0 h₁ h₂ },
  { exact @modeq.modeq_mul _ _ 0 _ 1 h₁ h₂ },
  { exact @modeq.modeq_mul _ _ 1 _ 0 h₁ h₂ },
  exact @modeq.modeq_mul _ _ 1 _ 1 h₁ h₂
end

@[parity_simps] theorem even_pow {m n : nat} : even (m^n) ↔ even m ∧ n ≠ 0 :=
by { induction n with n ih; simp [*, pow_succ, even_mul], tauto }

-- Here are examples of how `parity_simps` can be used with `nat`.

example (m n : nat) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even 25394535 :=
by simp

end nat
