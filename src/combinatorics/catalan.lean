/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import data.nat.choose.central
import algebra.big_operators.fin
import tactic.field_simp
import tactic.linear_combination

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
               `catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)`.

## Main results

* `catalan_eq_central_binom_div `: The explicit formula for the Catalan number using the central
  binomial coefficient, `catalan n = nat.central_binom n / (n + 1)`.

## Implementation details

The proof of the equality of the two definitions follows
https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Generalise to Catalan numbers associated to arbitrary Coxeter groups.

-/

open_locale big_operators
open finset

/-- The recursive definition of the sequence of Catalan numbers:
`catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)` -/
def catalan : ℕ → ℕ
| 0       := 1
| (n + 1) := ∑ i : fin n.succ, have _ := i.2, have _ := nat.lt_succ_iff.mpr (n.sub_le i),
             catalan i * catalan (n - i)

@[simp] lemma catalan_zero : catalan 0 = 1 := by rw catalan

lemma catalan_succ (n : ℕ) : catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i) :=
by rw catalan

/-- A helper sequence that can be used to prove the equality of the recursive and the explicit
definition using a telescoping sum argument. -/
private def gosper_catalan (n j : ℕ) : ℚ :=
nat.central_binom j * nat.central_binom (n - j) * (2 * j - n) / (2 * n * (n + 1))

private lemma gosper_trick {n i : ℕ} (h : i ≤ n) :
gosper_catalan (n+1) (i+1) - gosper_catalan (n+1) i =
nat.central_binom i / (i + 1) * nat.central_binom (n - i) / (n - i + 1) :=
begin
  have : (n:ℚ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero,
  have : (n:ℚ) + 1 + 1 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero,
  have : (i:ℚ) + 1 ≠ 0 := by exact_mod_cast i.succ_ne_zero,
  have : (n:ℚ) - i + 1 ≠ 0 := by exact_mod_cast (n - i).succ_ne_zero,
  have h₁ : ((i:ℚ) + 1) * (i + 1).central_binom = 2 * (2 * i + 1) * i.central_binom,
  { exact_mod_cast nat.succ_mul_central_binom_succ i },
  have h₂ : ((n:ℚ) - i + 1) * (n - i + 1).central_binom
    = 2 * (2 * (n - i) + 1) * (n - i).central_binom,
  { exact_mod_cast nat.succ_mul_central_binom_succ (n - i) },
  simp only [gosper_catalan],
  push_cast,
  field_simp,
  rw (nat.succ_sub h),
  linear_combination
    (2:ℚ) * (n - i).central_binom * (i + 1 - (n - i)) * (n + 1) * (n + 2) * ((n - i) + 1) * h₁
    - 2 * i.central_binom * (n + 1) * (n + 2) * (i - (n - i) - 1) * (i + 1) * h₂,
end

lemma gosper_catalan_sub_eq_catalan' (n : ℕ) :
  gosper_catalan (n + 1) (n + 1) - gosper_catalan (n + 1) 0 = nat.central_binom (n + 1) / (n + 2) :=
begin
simp only [gosper_catalan, tsub_self, nat.central_binom_zero, nat.cast_one, mul_one, nat.cast_add,
  tsub_zero, one_mul, nat.cast_zero, mul_zero, zero_sub, neg_add_rev, div_sub_div_same, ← mul_sub,
  ← mul_div],
congr,
rw [← neg_add, sub_neg_eq_add, add_comm (1 : ℚ) _, sub_add_cancel, ← div_div, div_self,
    inv_eq_one_div, add_assoc],
{ refl },
{ apply mul_ne_zero,
  { exact two_ne_zero },
  { exact_mod_cast n.succ_ne_zero } },
end

lemma s (a b c : ℕ) (h : (a / b : ℚ) = c) : a / b = c :=
begin
have h' : b ∣ a,
{ use c,
  rw ← h, sorry },
exact_mod_cast h,
end

theorem catalan_eq_central_binom_div (n : ℕ) :
  (catalan n : ℚ) = nat.central_binom n / (n + 1) :=
begin
  induction n using nat.case_strong_induction_on with d hd,
  { simp, },
  { simp_rw [catalan_succ, nat.cast_sum, nat.cast_mul],
    transitivity (∑ i : fin d.succ, (nat.central_binom i / (i + 1)) * (nat.central_binom (d - i) / (d - i + 1)) : ℚ),
    refine sum_congr rfl (λ i _, _),
    push_cast,
    rw [←hd _ i.is_le],
    rw [←hd _ tsub_le_self],
    { transitivity ∑ i : fin d.succ, (gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i),
      { rw [← sum_range (λi, gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i),
            sum_range_sub, nat.succ_eq_add_one],
        exact (gosper_catalan_sub_eq_catalan' d).symm, },
      refine sum_congr rfl (λ i _, _),
      exact gosper_trick d i (i.is_le), },
     },
end
