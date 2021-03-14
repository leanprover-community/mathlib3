/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.abel
import data.polynomial.eval

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`pochhammer S n : polynomial S = X * (X+1) * ... * (X + n - 1)`
which is also known as the rising factorial.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ`,
we define the polynomial with coefficients in any `[semiring S]`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
* Defining Bernstein polynomials (e.g. as one way to prove Weierstrass' theorem).
-/

universes u v

open polynomial

section
variables (S : Type u) [semiring S]

/--
`pochhammer S n` is the polynomial `X * (X+1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def pochhammer : ℕ → polynomial S
| 0 := 1
| (n+1) := X * (pochhammer n).comp (X + 1)

@[simp] lemma pochhammer_zero : pochhammer S 0 = 1 := rfl
@[simp] lemma pochhammer_one : pochhammer S 1 = X := by simp [pochhammer]
lemma pochhammer_succ_left (n : ℕ) : pochhammer S (n+1) = X * (pochhammer S n).comp (X+1) :=
by { dsimp [pochhammer], refl, }

section
variables {S} {T : Type v} [semiring T]
@[simp] lemma pochhammer_map (f : S →+* T) (n : ℕ) : (pochhammer S n).map f = pochhammer T n :=
begin
  induction n with n ih,
  { simp, },
  { simp [ih, pochhammer_succ_left, map_comp], },
end

end

@[simp, norm_cast] lemma pochhammer_eval_cast (n k : ℕ) :
  ((pochhammer ℕ n).eval k : S) = (pochhammer S n).eval k :=
begin
  rw [←pochhammer_map (algebra_map ℕ S), eval_map, ←(algebra_map ℕ S).eq_nat_cast,
    eval₂_at_nat_cast, nat.cast_id, ring_hom.eq_nat_cast],
end

lemma pochhammer_eval_zero {n : ℕ} : (pochhammer S n).eval 0 = if n = 0 then 1 else 0 :=
begin
  cases n,
  { simp, },
  { simp [X_mul, nat.succ_ne_zero, pochhammer_succ_left], }
end

@[simp] lemma pochhammer_zero_eval_zero : (pochhammer S 0).eval 0 = 1 :=
by simp [pochhammer_eval_zero]

@[simp] lemma pochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (pochhammer S n).eval 0 = 0 :=
by simp [pochhammer_eval_zero, h]

lemma pochhammer_succ_right (n : ℕ) : pochhammer S (n+1) = pochhammer S n * (X + n) :=
begin
  suffices h : pochhammer ℕ (n+1) = pochhammer ℕ n * (X + n),
  { apply_fun polynomial.map (algebra_map ℕ S) at h,
    simpa only [pochhammer_map, map_mul, map_add, map_X, map_nat_cast] using h, },
  induction n with n ih,
  { simp, },
  { conv_lhs {
    rw [pochhammer_succ_left, ih, mul_comp, ←mul_assoc, ←pochhammer_succ_left, add_comp, X_comp,
      nat_cast_comp, add_assoc, add_comm (1 : polynomial ℕ)], },
    refl, },
end

lemma polynomial.mul_X_add_nat_cast_comp {p q : polynomial S} {n : ℕ} :
  (p * (X + n)).comp q = (p.comp q) * (q + n) :=
by rw [mul_add, add_comp, mul_X_comp, ←nat.cast_comm, nat_cast_mul_comp, nat.cast_comm, mul_add]

lemma pochhammer_mul (n m : ℕ) :
  pochhammer S n * (pochhammer S m).comp (X + n) = pochhammer S (n + m) :=
begin
  induction m with m ih,
  { simp, },
  { rw [pochhammer_succ_right, polynomial.mul_X_add_nat_cast_comp, ←mul_assoc, ih,
      nat.succ_eq_add_one, ←add_assoc, pochhammer_succ_right, nat.cast_add, add_assoc], }
end

end

section
variables {S : Type*} [ordered_semiring S] [nontrivial S]

lemma pochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (pochhammer S n).eval s :=
begin
  induction n with n ih,
  { simp only [nat.nat_zero_eq_zero, pochhammer_zero, eval_one], exact zero_lt_one, },
  { rw [pochhammer_succ_right, mul_add, eval_add, ←nat.cast_comm, eval_nat_cast_mul, eval_mul_X,
      nat.cast_comm, ←mul_add],
    exact mul_pos ih
      (lt_of_lt_of_le h ((le_add_iff_nonneg_right _).mpr (nat.cast_nonneg n))), }
end

end

section factorial

open_locale nat

/-- Preliminary version of `pochhammer_eval_one` specialized to `S = ℕ`. -/
lemma pochhammer_eval_one' (n : ℕ) : (pochhammer ℕ n).eval 1 = n! :=
begin
  induction n with n ih,
  { simp, },
  { simp [ih, mul_comm, nat.succ_eq_add_one, add_comm, pochhammer_succ_right], },
end

@[simp]
lemma pochhammer_eval_one (S : Type*) [semiring S] (n : ℕ) :
  (pochhammer S n).eval (1 : S) = (n! : S) :=
by simpa using congr_arg (algebra_map ℕ S) (pochhammer_eval_one' n)

/-- Preliminary version of `factorial_mul_pochhammer` specialized to `S = ℕ`. -/
lemma factorial_mul_pochhammer' (r n : ℕ) :
  r! * (pochhammer ℕ n).eval (r+1) = (r + n)! :=
by simpa [add_comm 1 r, pochhammer_eval_one'] using congr_arg (eval 1) (pochhammer_mul ℕ r n)

lemma factorial_mul_pochhammer (S : Type*) [semiring S] (r n : ℕ) :
  (r! : S) * (pochhammer S n).eval (r+1) = (r + n)! :=
by simpa using congr_arg (algebra_map ℕ S) (factorial_mul_pochhammer' r n)

lemma pochhammer_eval_eq_factorial_div_factorial {r n : ℕ} :
  (pochhammer ℕ n).eval (r+1) = (r + n)! / r! :=
(nat.div_eq_of_eq_mul_right (nat.factorial_pos _) (factorial_mul_pochhammer' r n).symm).symm

lemma pochhammer_eval_eq_choose_mul_factorial {r n : ℕ} :
  (pochhammer ℕ n).eval (r+1) = (r + n).choose n * n! :=
begin
  rw pochhammer_eval_eq_factorial_div_factorial,
  -- TODO we need a `clear_denominators` tactic!
  apply nat.div_eq_of_eq_mul_right (nat.factorial_pos _),
  rw [mul_comm],
  convert (nat.choose_mul_factorial_mul_factorial (nat.le_add_left n r)).symm,
  simp,
end

lemma choose_eq_pochhammer_eval_div_factorial {r n : ℕ} :
  (r + n).choose n = (pochhammer ℕ n).eval (r+1) / n! :=
begin
  symmetry,
  apply nat.div_eq_of_eq_mul_right (nat.factorial_pos _),
  rw [mul_comm, pochhammer_eval_eq_choose_mul_factorial],
end

end factorial
