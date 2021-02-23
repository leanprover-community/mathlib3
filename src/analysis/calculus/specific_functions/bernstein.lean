/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.polynomial.derivative
import data.nat.choose
import linear_algebra.basis
import data.nat.pochhammer
import tactic.omega
import tactic.slim_check

noncomputable theory

meta def tactic.interactive.ls := tactic.interactive.library_search

@[simp]
lemma fin.succ_coe (n : ℕ) (i : fin n) : (i.cast_succ : ℕ) = (i : ℕ) :=
rfl

@[simp, norm_cast] theorem polynomial.coe_nat_inj' {m n : ℕ} : (↑m : polynomial ℤ) = ↑n ↔ m = n :=
sorry

open nat (choose)
open polynomial (X)

def bernstein_polynomial (n ν : ℕ) : polynomial ℤ := (choose n ν) * X^ν * (1 - X)^(n - ν)

-- Sanity check
example : bernstein_polynomial 3 2 = 3 * X^2 - 3 * X^3 :=
begin
  norm_num [bernstein_polynomial, choose],
  ring,
end

namespace bernstein_polynomial

lemma eval_at_0 (n ν : ℕ) : (bernstein_polynomial n ν).eval 0 = if ν = 0 then 1 else 0 :=
begin
  dsimp [bernstein_polynomial],
  split_ifs,
  { subst h, simp, },
  { simp [zero_pow (nat.pos_of_ne_zero h)], },
end
lemma eval_at_1 (n ν : ℕ) : (bernstein_polynomial n ν).eval 1 = if ν = n then 1 else 0 :=
begin
  dsimp [bernstein_polynomial],
  split_ifs,
  { subst h, simp, },
  { by_cases w : 0 < n - ν,
    { simp [zero_pow w], },
    { simp [(show n < ν, by omega), nat.choose_eq_zero_of_lt], }, },
end.

lemma derivative' (n ν : ℕ) :
  (bernstein_polynomial (n+1) (ν+1)).derivative =
    (n+1) * (bernstein_polynomial n ν - bernstein_polynomial n (ν + 1)) :=
begin
  dsimp [bernstein_polynomial],
  suffices :
    ↑((n + 1).choose (ν + 1)) * ((↑ν + 1) * X ^ ν) * (1 - X) ^ (n - ν)
      -(↑((n + 1).choose (ν + 1)) * X ^ (ν + 1) * (↑(n - ν) * (1 - X) ^ (n - ν - 1))) =
    (↑n + 1) * (↑(n.choose ν) * X ^ ν * (1 - X) ^ (n - ν) -
         ↑(n.choose (ν + 1)) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))),
  { simpa [polynomial.derivative_pow, ←sub_eq_add_neg], }, -- make this a simp lemma?
  conv_rhs { rw mul_sub, },
  -- -- We'll prove the two terms match up separately.
  refine congr (congr_arg has_sub.sub _) _,
  { simp only [←mul_assoc],
    refine congr (congr_arg (*) (congr (congr_arg (*) _) rfl)) rfl,
    -- Now it's just about binomial coefficients
    norm_cast,
    convert (nat.succ_mul_choose_eq _ _).symm, },
  { rw nat.sub_sub, rw [←mul_assoc,←mul_assoc], congr' 1,
    rw mul_comm , rw [←mul_assoc,←mul_assoc],  congr' 1,
    norm_cast,
    convert (nat.choose_mul_succ_eq n (ν + 1)).symm using 1,
    { convert mul_comm _ _ using 2,
      simp, },
    { apply mul_comm, }, },
end

lemma derivative (n ν : ℕ) :
  (bernstein_polynomial n (ν+1)).derivative =
    n * (bernstein_polynomial (n-1) ν - bernstein_polynomial (n-1) (ν+1)) :=
begin
  cases n,
  { simp [bernstein_polynomial], },
  { apply derivative', }
end

lemma iterate_derivative_at_zero_eq_zero_of_le (n : ℕ) {ν k : ℕ} :
  k ≤ ν → (polynomial.derivative^[k] (bernstein_polynomial n (ν+1))).eval 0 = 0 :=
begin
  induction k with k ih generalizing n ν,
  { simp [eval_at_0], },
  { simp only [derivative, int.coe_nat_eq_zero, int.nat_cast_eq_coe_nat, mul_eq_zero,
      function.comp_app, function.iterate_succ,
      polynomial.iterate_derivative_sub, polynomial.iterate_derivative_coe_nat_mul,
      polynomial.eval_mul, polynomial.eval_nat_cast, polynomial.eval_sub],
    intro h,
    right,
    rw ih,
    simp only [sub_zero],
    convert @ih (n-1) (ν-1) _; omega, }
end

@[simp]
lemma iterate_derivative_succ_at_zero_eq_zero (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial n (ν+1))).eval 0 = 0 :=
iterate_derivative_at_zero_eq_zero_of_le n (le_refl _)

lemma iterate_derivative_self_at_0 (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial n ν)).eval 0 = n.falling_factorial ν :=
begin
  induction ν with ν ih generalizing n,
  { simp [eval_at_0], },
  { simp [derivative, ih],
    rw [nat.falling_factorial_eq_mul_left],
    push_cast, }
end

/-
lemma linear_independent.fin_succ (n : ℕ) (ι : fin (n+1) → V)
  (hι : linear_independent K (ι ∘ fin.cast_succ))
  (hx : ι (fin.last n) ∉ span K (set.range (ι ∘ @fin.cast_succ n))) :
  linear_independent K ι :=
sorry
-/

lemma linear_independent_aux (n k : ℕ) (h : k ≤ n + 1):
  linear_independent ℚ (λ ν : fin k, (bernstein_polynomial n ν).map (algebra_map ℤ ℚ)) :=
begin
  induction k with k ih,
  { apply linear_independent_empty_type,
    sorry, },
  { apply linear_independent.fin_succ, -- use linear_independent_fin_succ instead?
    { exact ih (le_of_lt h) },
    { -- The actual work!
      -- We show that the k-th derivate at 1 doesn't vanish,
      -- but vanishes for everything in the span.

      } }
  -- library_search,
end

lemma linear_independent (n : ℕ) :
  linear_independent ℚ (λ ν : fin (n+1), (bernstein_polynomial n ν).map (algebra_map ℤ ℚ)) :=
linear_independent_aux n (n+1) (le_refl _)

end bernstein_polynomial
