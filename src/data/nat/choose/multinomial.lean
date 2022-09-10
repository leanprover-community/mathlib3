/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/

import algebra.big_operators.fin
import algebra.big_operators.order
import data.nat.choose.basic
import data.nat.factorial.big_operators
import data.fin.vec_notation

import tactic.linarith

/-!
# Multinomial

This file defines the multinomial coefficient and several small lemma's for manipulating it.

## Main declarations

- `nat.multinomial`: the multinomial coefficient

-/

open_locale big_operators nat

namespace nat

variables {α : Type*} (s : finset α) (f : α → ℕ)
variables {a b : α}

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i in s, f i)! / ∏ i in s, (f i)!`.
-/
def multinomial : ℕ := (∑ i in s, f i)! / ∏ i in s, (f i)!

lemma multinomial_pos : 0 < multinomial s f := nat.div_pos
  (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f)) (prod_factorial_pos s f)

lemma multinomial_spec : (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)! :=
nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

@[simp] lemma multinomial_nil : multinomial ∅ f = 1 := rfl

@[simp] lemma multinomial_singleton : multinomial {a} f = 1 :=
by simp [multinomial, nat.div_self (factorial_pos (f a))]

@[simp] lemma multinomial_insert_one [decidable_eq α] (h : a ∉ s) (h₁ : f a = 1) :
  multinomial (insert a s) f = (s.sum f).succ * multinomial s f :=
begin
  simp only [multinomial, one_mul, factorial],
  rw [finset.sum_insert h, finset.prod_insert h, h₁, add_comm, ←succ_eq_add_one, factorial_succ],
  simp only [factorial_one, one_mul, function.comp_app, factorial],
  rw nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _),
end

lemma multinomial_insert [decidable_eq α] (h : a ∉ s) :
  multinomial (insert a s) f = (f a + s.sum f).choose (f a) * multinomial s f :=
begin
  rw choose_eq_factorial_div_factorial (le.intro rfl),
  simp only [multinomial, nat.add_sub_cancel_left, finset.sum_insert h, finset.prod_insert h,
    function.comp_app],
  rw [div_mul_div_comm ((f a).factorial_mul_factorial_dvd_factorial_add (s.sum f))
    (prod_factorial_dvd_factorial_sum _ _), mul_comm (f a)! (s.sum f)!, mul_assoc,
    mul_comm _ (s.sum f)!, nat.mul_div_mul _ _ (factorial_pos _)],
end

/-! ### Connection to binomial coefficients -/

lemma binomial_eq [decidable_eq α] (h : a ≠ b) :
  multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) :=
by simp [multinomial, finset.sum_pair h, finset.prod_pair h]

lemma binomial_eq_choose [decidable_eq α] (h : a ≠ b) :
  multinomial {a, b} f = (f a + f b).choose (f a) :=
by simp [binomial_eq _ h, choose_eq_factorial_div_factorial (nat.le_add_right _ _)]

lemma binomial_spec [decidable_eq α] (hab : a ≠ b) :
  (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! :=
by simpa [finset.sum_pair hab, finset.prod_pair hab] using multinomial_spec {a, b} f

@[simp] lemma binomial_one [decidable_eq α] (h : a ≠ b) (h₁ : f a = 1) :
  multinomial {a, b} f = (f b).succ :=
by simp [multinomial_insert_one {b} f (finset.not_mem_singleton.mpr h) h₁]

lemma binomial_succ_succ [decidable_eq α] (h : a ≠ b) :
  multinomial {a, b} (function.update (function.update f a (f a).succ) b (f b).succ) =
  multinomial {a, b} (function.update f a (f a).succ) +
  multinomial {a, b} (function.update f b (f b).succ) :=
begin
  simp only [binomial_eq_choose, function.update_apply, function.update_noteq,
    succ_add, add_succ, choose_succ_succ, h, ne.def, not_false_iff, function.update_same],
  rw if_neg h.symm,
  ring,
end

lemma succ_mul_binomial [decidable_eq α] (h : a ≠ b) :
  (f a + f b).succ * multinomial {a, b} f =
  (f a).succ * multinomial {a, b} (function.update f a (f a).succ) :=
begin
  rw [binomial_eq_choose _ h, binomial_eq_choose _ h, mul_comm (f a).succ,
    function.update_same, function.update_noteq (ne_comm.mp h)],
  convert succ_mul_choose_eq (f a + f b) (f a),
  exact succ_add (f a) (f b),
end

/-! ### Simple cases -/

lemma multinomial_univ_two (a b : ℕ) : multinomial finset.univ ![a, b] = (a + b)! / (a! * b!) :=
by simp [multinomial, fin.sum_univ_two, fin.prod_univ_two]

lemma multinomial_univ_three (a b c : ℕ) : multinomial finset.univ ![a, b, c] =
  (a + b + c)! / (a! * b! * c!) :=
by simp [multinomial, fin.sum_univ_three, fin.prod_univ_three]

end nat
