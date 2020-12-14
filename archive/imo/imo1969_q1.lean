/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import tactic.linarith
import tactic.norm_cast
import tactic.ring

open int
open nat

/-!
# IMO 1969 Q1

Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.

The key to the solution is that you can factor z into the product of two polynomials,
if a = 4*m^4.
-/

lemma factorization (m n : ℤ) : ((m - n)^2 + m^2) * ((m + n)^2 + m^2) = n^4 + 4*m^4 := by ring

/-!
To show that the product is not prime, we need to show each of the factors is at least 2,
which nlinarith can solve since they are expressed as a sum of squares.
-/
lemma left_factor_large (m n : ℤ) (h: 1 < m) : 1 < ((m - n)^2 + m^2) := by nlinarith
lemma right_factor_large (m n : ℤ) (h: 1 < m) : 1 < ((m + n)^2 + m^2) := by nlinarith

/-!
The factorization is over the integers, but we need the nonprimality over the natural numbers.
-/

lemma int_large (a : ℤ) (h : 1 < a) : 1 < a.nat_abs :=
by exact_mod_cast lt_of_lt_of_le h le_nat_abs

lemma int_not_prime (a b : ℤ) (c : ℕ) (h1 : 1 < a) (h2 : 1 < b) (h3 : a*b = ↑c) : ¬ prime c :=
have h4 : (a*b).nat_abs = a.nat_abs * b.nat_abs, from nat_abs_mul a b,
have h5 : a.nat_abs * b.nat_abs = c, by finish,
norm_num.not_prime_helper a.nat_abs b.nat_abs c h5 (int_large a h1) (int_large b h2)

lemma polynomial_not_prime (m n : ℕ) (h1 : 1 < m) : ¬ prime (n^4 + 4*m^4) :=
have h2 : 1 < of_nat m, from coe_nat_lt.mpr h1,
begin
  refine int_not_prime _ _ _ (left_factor_large ↑m ↑n h2) (right_factor_large ↑m ↑n h2) _,
  rw factorization,
  norm_cast
end

/-!
Now we just need to show this works for an arbitrarily large $a$, to prove there are
infinitely many of them.
$a = 4*(2+b)^4$ should do. So $m = 2+b$.
-/

theorem imo1969_q1 : ∀ b : ℕ, ∃ a : ℕ, a ≥ b ∧ ∀ n : ℕ, ¬ prime (n^4 + a) :=
assume b,
have h1 : 1 < 2+b, by linarith,
have b^2 ≥ b, by nlinarith,
have h2 : 4*(2+b)^4 ≥ b, by nlinarith,
begin
  use [4*(2+b)^4, h2],
  assume n,
  exact polynomial_not_prime (2+b) n h1
end


