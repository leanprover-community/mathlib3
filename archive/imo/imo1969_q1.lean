import tactic
import tactic.basic
import tactic.linarith
import tactic.norm_cast
import tactic.ring

open int
open nat

/-
The 1969 IMO, problem 1:
Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.

The key to the solution is that you can factor this into the product of two polynomials, if a = 4*m^4.
-/

lemma factorization (m n: ℤ): (n^2 + 2*m^2 - 2*n*m) * (n^2 + 2*m^2 + 2*n*m) = n^4 + 4*m^4
:= by ring

/-
To show that the product is not prime, we need to show each of the factors is at least 2, which we can
do with a sum-of-squares expression.
-/
lemma left_factor_large (m n: ℤ) (h: m > 1): (n^2 + 2*m^2 - 2*n*m) > 1 :=
have h: (n^2 + 2*m^2 - 2*n*m) = (m-n)^2 + m^2, by ring,
begin
  rw h,
  nlinarith,
end

lemma right_factor_large (m n: ℤ) (h: m > 1): (n^2 + 2*m^2 + 2*n*m) > 1 :=
have h: (n^2 + 2*m^2 + 2*n*m) = (m+n)^2 + m^2, by ring,
begin
  rw h,
  nlinarith,
end

/-
The factorization is over the integers, but we need the nonprimality over the natural numbers.
-/

lemma int_large (a: ℤ) (h: a > 1) : a.nat_abs > 1 :=
have a = ↑(a.nat_abs) ∨ a = -↑(a.nat_abs), from nat_abs_eq a,
or.elim this
  (assume: a = ↑(a.nat_abs), by linarith)
  (assume: a = -↑(a.nat_abs), by linarith)

lemma int_not_prime (a b: ℤ) (c: ℕ) (h1: a > 1) (h2: b > 1) (h3: a*b = ↑c) : ¬ prime c :=
have h4: (a*b).nat_abs = a.nat_abs * b.nat_abs, from nat_abs_mul a b,
have h5: a.nat_abs * b.nat_abs = c, by finish,
norm_num.not_prime_helper a.nat_abs b.nat_abs c h5 (int_large a h1) (int_large b h2)

lemma polynomial_not_prime (m n: ℕ) (h1: m > 1) : ¬ prime (n^4 + 4*m^4) :=
have h2: of_nat m > 1, from coe_nat_lt.mpr h1,
begin
  refine int_not_prime _ _ _ (left_factor_large ↑m ↑n h2) (right_factor_large ↑m ↑n h2) _,
  rw factorization,
  norm_cast
end


/-
Now we just need to show this works for an arbitrarily large a, to prove there are infinitely many of them.
a = 4*(2+b)^4 should do. So m = 2+b.
-/

theorem imo1969_q1: ∀ b: ℕ, ∃ a: ℕ, a ≥ b ∧ ∀ n: ℕ, ¬ prime (n^4 + a) :=
assume b,
have h1: 2+b > 1, by linarith,
have b^2 ≥ b, by nlinarith,
have h2: 4*(2+b)^4 ≥ b, by nlinarith,
begin
  fapply exists.intro,
  exact 4*(2+b)^4,
  apply and.intro h2,
  assume n,
  exact polynomial_not_prime (2+b) n h1
end


