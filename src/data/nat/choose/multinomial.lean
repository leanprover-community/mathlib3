/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
Heavily inspired by code from Kyle Miller and Kevin Buzzard
-/
import data.nat.choose.basic
import data.list.perm
import data.finset.basic
import algebra.big_operators.basic
import tactic.linarith

/-!
# Multinomial

This file defines the multinomial coefficient and several small lemma's for manipulating it.

## Main declarations

- `nat.multinomial`: the multinomial coefficient

-/

open_locale nat

namespace nat

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(s.sum f)! / s.prod (factorial ∘ f)`
-/
def multinomial {α} (s : finset α) (f : α → ℕ) : ℕ := (s.sum f)! / s.prod (factorial ∘ f)


lemma prod_factorial_dvd_factorial_sum {α} (s : finset α) (f : α → ℕ) :
  s.prod (factorial ∘ f) ∣ (s.sum f)! :=
begin
  classical,
  induction s using finset.induction with α' s' has ih,
  { simp only [finset.sum_empty, finset.prod_empty, factorial], },
  { simp [finset.prod_insert has, finset.sum_insert has],
    refine dvd_trans (mul_dvd_mul_left ((f α')!) ih) _,
    convert factorial_mul_factorial_dvd_factorial (le.intro rfl),
    rw nat.add_sub_cancel_left, },
end

lemma mul_factorial_dvd_factorial_add (a b : ℕ) : a! * b! ∣ (a + b)! :=
begin
  convert @factorial_mul_factorial_dvd_factorial (a + b) a (le.intro rfl),
  rw nat.add_sub_cancel_left,
end

lemma prod_factorial_pos {α} (s : finset α) (f : α → ℕ) :
  0 < s.prod (factorial ∘ f) :=
begin
  classical,
  induction s using finset.induction with α' s' has ih,
  { simp only [succ_pos', finset.prod_empty], },
  { rw finset.prod_insert has,
    exact nat.mul_pos (nat.factorial_pos (f α')) ih, },
end

lemma multinomial_pos {α} (s : finset α) (f : α → ℕ): 0 < multinomial s f :=
nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
  (prod_factorial_pos s f)

lemma multinomial_spec {α} (s : finset α) (f : α → ℕ):
  s.prod (factorial ∘ f) * multinomial s f = (s.sum f)! :=
begin
  exact nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f),
end


@[simp] lemma multinomial_nil {α} (f: α → ℕ): multinomial ∅ f = 1 := rfl

@[simp] lemma multinomial_singleton {α} (f: α → ℕ) (a : α): multinomial {a} f = 1 :=
by simp [multinomial, nat.div_self (factorial_pos (f a))]

@[simp] lemma multinomial_one {α} [decidable_eq α]
  (s : finset α) (f : α → ℕ) (a : α) (h: a ∉ s) (h₁: f a = 1):
  multinomial (insert a s) f = (s.sum f).succ * multinomial s f :=
begin
  simp only [multinomial, one_mul, factorial],
  rw [finset.sum_insert h, finset.prod_insert h, h₁, add_comm, ←succ_eq_add_one, factorial_succ],
  simp only [factorial_one, one_mul, function.comp_app, factorial],
  rw nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _),
end

lemma multinomial_add_n {α} [decidable_eq α]
  (s : finset α) (f : α → ℕ) (a : α) (h: a ∉ s) {n : ℕ} (h₁: f a = n) :
  multinomial (insert a s) f = (n + (s.sum f)).choose n * multinomial s f :=
begin
  rw choose_eq_factorial_div_factorial (le.intro rfl),
  simp [multinomial, nat.add_sub_cancel_left, finset.sum_insert h, finset.prod_insert h, h₁],
  rw div_mul_div_comm (mul_factorial_dvd_factorial_add n (s.sum f))
    (prod_factorial_dvd_factorial_sum _ _),
  rw mul_comm n! (s.sum f)!,
  rw mul_assoc,
  rw mul_comm _ (s.sum f)!,
  rw nat.mul_div_mul _ _ (factorial_pos (s.sum f)),
end

/-! ### Connection to binomial coefficients -/

lemma binomial_eq {α} [decidable_eq α] (f: α → ℕ) (a b: α) (h: a ≠ b) :
  multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) :=
  by simp [multinomial, finset.sum_pair h, finset.prod_pair h]


lemma binomial_eq_choose {α} [decidable_eq α] (f: α → ℕ) (a b: α) (h: a ≠ b) :
  multinomial {a, b} f = (f a + f b).choose (f a) :=
begin
  have fact : f a ≤ f a + f b, by linarith,
  simp [binomial_eq _ _ _ h, choose_eq_factorial_div_factorial fact],
end

lemma binomial_spec {α} [decidable_eq α] (f: α → ℕ) (a b: α) (hab: a ≠ b) :
  (f a)! * (f b)! * multinomial {a, b} f  = (f a + f b)! :=
begin
  have h := multinomial_spec {a, b} f ,
  simpa [finset.sum_pair hab, finset.prod_pair hab] using h,
end

@[simp] lemma binomial_one {α} [decidable_eq α] (f: α → ℕ) (a b: α) (h: a ≠ b) (h₁: f a = 1) :
  multinomial {a, b} f = (f b).succ :=
begin
  rw multinomial_one {b} f a (finset.not_mem_singleton.mpr h) h₁,
  simp,
end

lemma binomial_succ_succ {α} [decidable_eq α] (f: α → ℕ) (a b: α) (h: a ≠ b) :
  multinomial {a, b} (function.update (function.update f a (f a).succ) b (f b).succ) =
  multinomial {a, b} (function.update f a (f a).succ)
  + multinomial {a, b} (function.update f b (f b).succ) :=
begin
  simp only [binomial_eq_choose, function.update_apply, function.update_noteq,
    succ_add, add_succ, choose_succ_succ, h, ne.def, not_false_iff, function.update_same],
  rw if_neg (ne_comm.mp h),
  ring,
end

lemma succ_mul_binomial {α} [decidable_eq α] (f: α → ℕ) (a b: α) (h: a ≠ b) :
  (f a + f b).succ * multinomial {a, b} f =
  (f a).succ * multinomial {a, b} (function.update f a (f a).succ) :=
begin
  rw [binomial_eq_choose _ _ _ h, binomial_eq_choose _ _ _ h, mul_comm (f a).succ,
    function.update_same, function.update_noteq (ne_comm.mp h)],
  convert succ_mul_choose_eq (f a + f b) (f a),
  exact succ_add (f a) (f b),
end

end nat
