/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import data.nat.choose.central
import algebra.big_operators.fin
import tactic.field_simp

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
               `catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)`.
* `catalan' n`: the `n`th Catalan number, defined explicitly as
               `catalan' n = 1 / (n + 1) * nat.central_binom n`.

## Main results

* `catalan_defs_agree`: The fact that the two definitions both give the same sequence.

## Implementation details

The proof of the equality of the two definitions follows
https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Generalise to Catalan numbers associated to arbitrary Coxeter groups.

-/

open_locale big_operators
open finset

def catalan : ℕ → ℕ
| 0       := 1
| (n + 1) := ∑ i : fin n.succ, have _ := i.2, have _ := nat.lt_succ_iff.mpr (n.sub_le i),
             catalan i * catalan (n - i)

@[simp] lemma catalan_zero : catalan 0 = 1 := by rw catalan

lemma catalan_succ (n : ℕ) : catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i) :=
by rw catalan

def catalan' (n : ℕ) :  ℚ :=
1 / (n + 1) * nat.central_binom n

@[simp] lemma catalan'_zero : catalan' 0 = 1 :=
begin rw catalan', simp, end

private def gosper_catalan (n j : ℕ) : ℚ :=
nat.central_binom j * nat.central_binom (n - j) * (2 * j - n) / (2 * n * (n + 1))

lemma trick {a b c : ℕ} (h : b ≤ a) : a + c - (b + c) = a - b :=
begin exact nat.add_sub_add_right a c b end

lemma gosper_trick (n i : ℕ) (h : i ≤ n) :
gosper_catalan (n+1) (i+1) - gosper_catalan (n+1) i = catalan' i * catalan' (n - i) :=
begin
rw ← @mul_right_inj' _ _ (i + 1 : ℚ) _ _ (nat.cast_add_one_ne_zero i),
rw ← @mul_right_inj' _ _ (n - i + 1 : ℚ) _ _ (by exact_mod_cast (n - i).succ_ne_zero),
{ simp only [gosper_catalan, catalan'],
  rw [mul_sub, mul_sub],
  rw mul_div,
  rw ← mul_assoc,
  rw ← mul_assoc,
  rw_mod_cast nat.succ_mul_central_binom_succ i,
  rw mul_comm i.central_binom,
  simp only [← mul_assoc],
  rw_mod_cast mul_comm (n - i + 1),
  nth_rewrite 1 mul_div,
  push_cast,
  simp only [← mul_assoc],
  rw mul_assoc (i + 1 : ℚ),
  simp_rw nat.sub_add_comm h,
  rw_mod_cast nat.succ_mul_central_binom_succ,
  simp_rw nat.add_sub_add_right,
  rw mul_comm _ (n-i).central_binom,
  rw mul_comm _ (n-i).central_binom,
  rw ← mul_assoc (i+1),
  rw mul_comm (i+1),
  push_cast,
  simp only [mul_div, ← mul_assoc],
  rw_mod_cast mul_comm _ (n-i).central_binom,
  simp only [← mul_div, ← mul_assoc],
  push_cast,
  simp only [mul_assoc],
  rw ← mul_sub,
  simp only [← mul_assoc],
  rw mul_comm _ ((n-i).central_binom : ℚ),
  congr,
  rw mul_comm _ (i.central_binom : ℚ),
  rw mul_comm _ (i.central_binom : ℚ),
  rw mul_comm _ (i.central_binom : ℚ),
  simp only [mul_assoc],
  rw ← mul_sub,
  congr,
  ring_nf,
  field_simp,
  rw div_self,
  { have h : ((n : ℚ) + (-(i : ℚ) + 1)) * (i + 1) = (i + 1) * n + (-i ^ 2 + 1),
    { ring },
    { rw [← h, div_self],
      apply mul_ne_zero,
      { rw ← add_assoc,
        rw ← sub_eq_add_neg,
        exact_mod_cast (n-i).succ_ne_zero, },
      { exact_mod_cast i.succ_ne_zero } }, },
  { exact_mod_cast nat.succ_ne_zero _ } },
end

lemma gosper_catalan_sub_eq_catalan' (n : ℕ) :
  gosper_catalan (n + 1) (n + 1) - gosper_catalan (n + 1) 0 = catalan' (n + 1) :=
begin
simp only [gosper_catalan, catalan', nat.cast_succ, one_div, tsub_self, nat.central_binom_zero,
  nat.cast_one, mul_one, tsub_zero, one_mul, nat.cast_zero, mul_zero, zero_sub, neg_add_rev,
  div_eq_mul_inv],
rw [mul_assoc, mul_assoc, mul_assoc, ← mul_sub, mul_comm],
congr,
nth_rewrite 1 ← one_mul (n + 1 : ℚ),
rw [← neg_add_rev, neg_mul, sub_neg_eq_add, ← sub_mul],
norm_num,
rw [← mul_add, ← add_mul, ← two_mul, mul_comm _ (1/2 : ℚ), ← mul_assoc, mul_comm (n + 1 + 1 : ℚ)⁻¹],
simp only [← mul_assoc],
nth_rewrite 1 ← one_mul (n + 1 + 1 : ℚ)⁻¹,
congr,
simp only [one_div, inv_mul_cancel_right₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
apply mul_inv_cancel,
exact_mod_cast n.succ_ne_zero,
end

theorem catalan_defs_agree (n : ℕ) :
catalan' n = catalan n :=
begin
  induction n using nat.case_strong_induction_on with d hd,
  { simp, },
  { simp_rw [catalan_succ, nat.cast_sum, nat.cast_mul],
    transitivity ∑ i : fin d.succ, catalan' i * catalan' (d - i),
    { transitivity ∑ i : fin d.succ, (gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i),
      { rw [← sum_range (λi, gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i),
            sum_range_sub, nat.succ_eq_add_one],
        exact (gosper_catalan_sub_eq_catalan' d).symm, },
      refine sum_congr rfl (λ i _, _),
      exact gosper_trick d i (i.is_le), },
    refine sum_congr rfl (λ i _, _),
    rw [←hd _ i.is_le, ←hd _ tsub_le_self], },
end
