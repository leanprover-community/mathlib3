/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The `even` and `odd` predicates on the natural numbers.
-/
import data.nat.modeq

namespace nat

@[simp] theorem mod_two_ne_one {n : nat} : ¬ n % 2 = 1 ↔ n % 2 = 0 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

@[simp] theorem mod_two_ne_zero {n : nat} : ¬ n % 2 = 0 ↔ n % 2 = 1 :=
by cases mod_two_eq_zero_or_one n with h h; simp [h]

/-- A natural number `n` is `even` if `2 | n`. -/
def even (n : nat) : Prop := 2 ∣ n

theorem even_iff {n : nat} : even n ↔ n % 2 = 0 :=
⟨λ ⟨m, hm⟩, by simp [hm], λ h, ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [h])⟩⟩

lemma not_even_iff {n : ℕ} : ¬ even n ↔ n % 2 = 1 :=
by rw [even_iff, mod_two_ne_zero]

/-- A natural number `n` is `odd` if it is not even.  The mathlib API
for parity is developed in terms of `even`; to avoid duplication,
results should not be stated in terms of `odd`.  The purpose of this
definition is for code outside mathlib that wishes to have a formal
statement that is as literal a translation as possible of the
corresponding informal statement, where that informal statement refers
to odd numbers. -/
def odd (n : ℕ) : Prop := ¬ even n

@[simp] lemma odd_def (n : ℕ) : odd n ↔ ¬ even n := iff.rfl

instance : decidable_pred even :=
λ n, decidable_of_decidable_of_iff (by apply_instance) even_iff.symm

instance decidable_pred_odd : decidable_pred odd :=
λ n, decidable_of_decidable_of_iff (by apply_instance) not_even_iff.symm

mk_simp_attribute parity_simps "Simp attribute for lemmas about `even`"

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

theorem even.add {m n : ℕ} (hm : m.even) (hn : n.even) : (m + n).even :=
even_add.2 $ by simp only [*]

@[simp] theorem not_even_bit1 (n : nat) : ¬ even (bit1 n) :=
by simp [bit1] with parity_simps

lemma two_not_dvd_two_mul_add_one (a : ℕ) : ¬(2 ∣ 2 * a + 1) :=
begin
  convert not_even_bit1 a,
  exact two_mul a,
end

lemma two_not_dvd_two_mul_sub_one : Π {a : ℕ} (w : 0 < a), ¬(2 ∣ 2 * a - 1)
| (a+1) _ := two_not_dvd_two_mul_add_one a

@[parity_simps] theorem even_sub {m n : nat} (h : n ≤ m) : even (m - n) ↔ (even m ↔ even n) :=
begin
  conv { to_rhs, rw [←nat.sub_add_cancel h, even_add] },
  by_cases h : even n; simp [h]
end

theorem even.sub {m n : ℕ} (hm : m.even) (hn : n.even) : (m - n).even :=
(le_total n m).elim
  (λ h, by simp only [even_sub h, *])
  (λ h, by simp only [sub_eq_zero_of_le h, even_zero])

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

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even 
if and only if `m` is even and `n` is positive. -/
@[parity_simps] theorem even_pow {m n : nat} : even (m^n) ↔ even m ∧ n ≠ 0 :=
by { induction n with n ih; simp [*, pow_succ', even_mul], tauto }

lemma even_div {a b : ℕ} : even (a / b) ↔ a % (2 * b) / b = 0 :=
by rw [even, dvd_iff_mod_eq_zero, nat.div_mod_eq_mod_mul_div, mul_comm]

theorem neg_one_pow_eq_one_iff_even {α : Type*} [ring α] {n : ℕ} (h1 : (-1 : α) ≠ 1):
  (-1 : α) ^ n = 1 ↔ even n :=
⟨λ h, n.mod_two_eq_zero_or_one.elim (dvd_iff_mod_eq_zero _ _).2
  (λ hn, by rw [neg_one_pow_eq_pow_mod_two, hn, pow_one] at h; exact (h1 h).elim),
  λ ⟨m, hm⟩, by rw [neg_one_pow_eq_pow_mod_two, hm]; simp⟩

-- Here are examples of how `parity_simps` can be used with `nat`.

example (m n : nat) (h : even m) : ¬ even (n + 3) ↔ even (m^2 + m + n) :=
by simp [*, (dec_trivial : ¬ 2 = 0)] with parity_simps

example : ¬ even 25394535 :=
by simp

end nat
