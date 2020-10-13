/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import algebra.group_power.identities
import tactic.linarith
import tactic.norm_cast
import data.set.finite

open int
open nat

/-!
# IMO 1969 Q1

Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.

The key to the solution is that you can factor $z$ into the product of two polynomials,
if $a = 4*m^4$. This is Sophie Germain's identity, called `pow_four_add_four_mul_pow_four`
in mathlib.
-/
lemma factorization {m n : ℤ} : ((n - m)^2 + m^2) * ((n + m)^2 + m^2) = n^4 + 4*m^4 :=
pow_four_add_four_mul_pow_four.symm

/-!
To show that the product is not prime, we need to show each of the factors is at least 2,
which `nlinarith` can solve since they are expressed as a sum of squares.
-/
lemma left_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < ((n - m)^2 + m^2) := by nlinarith
lemma right_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < ((n + m)^2 + m^2) := by nlinarith

/-!
The factorization is over the integers, but we need the nonprimality over the natural numbers.
-/

lemma int_large {a : ℤ} (h : 1 < a) : 1 < a.nat_abs :=
by exact_mod_cast lt_of_lt_of_le h le_nat_abs

/-
Should this be in src? Probably, with assumptions 1 < a.nat_abs and 1 < b.nat_abs.
-/

lemma int_not_prime {a b : ℤ} {c : ℕ} (h1 : 1 < a) (h2 : 1 < b) (h3 : a*b = (c : ℤ)) : ¬ prime c :=
have h4 : a.nat_abs * b.nat_abs = c, by rw [←nat_abs_mul, h3, nat_abs_of_nat],
norm_num.not_prime_helper a.nat_abs b.nat_abs c h4 (int_large h1) (int_large h2)

lemma polynomial_not_prime {m : ℕ} (h1 : 1 < m) (n : ℕ) : ¬ prime (n^4 + 4*m^4) :=
have h2 : 1 < (m : ℤ), from coe_nat_lt.mpr h1,
begin
  refine int_not_prime (left_factor_large (n : ℤ) h2) (right_factor_large (n : ℤ) h2) _,
  exact_mod_cast factorization
end

/-!
Now we just need to show this works for an arbitrarily large $a$, to prove there are
infinitely many of them.
$a = 4*(2+b)^4$ should do. So $m = 2+b$.
-/

/-- `good_nats` is the set of natural numbers satisfying the
condition in the problem statement, namely the `a : ℕ` such that `n^4 + a` is not prime
for any `n : ℕ`. -/
def good_nats : set ℕ := {a : ℕ | ∀ n : ℕ, ¬ prime (n^4 + a)}

/--
The function $a = 4*(2+b)^4$.
-/
def a (b : ℕ) : ℕ := 4*(2+b)^4

/-
You should be able to prove that this is strict_mono (hence, injective) using dot-syntax lemmas. If not, this is a good reason to add more of them.
-/

lemma a_good (b : ℕ) : a b ∈ good_nats :=
polynomial_not_prime (show 1 < 2+b, by linarith)

/-
A good lemma for src/ (not_congr finite_image_iff): if f : α → β is inj_on s, then f '' s is an infinite set iff s is an infinite set. Related lemmas:

    if f is inj_on s and s is infinite and maps_to f s t, then t is infinite (above + monotonicity);
    if f is injective and [infinite α], then range f is an infinite set;
    if f is injective, [infinite α] and ∀ x, f x ∈ s, then s is an infinite set (this is what's I'd use in this problem).
-/

/-- `a` is a monotone function -/
lemma lt_a {b : ℕ} (hb : b ∈ good_nats) : b < a b :=
begin
  simp only [←subtype.coe_lt_coe, subtype.coe_mk, a],
  nlinarith [show (b : ℕ) ≤ b^2, { rw [pow_two], exact le_mul_self _ }],
end

/-- We conclude by using `a` to get a contradiction with the assumption that `good_nats` is
a `fintype`, since the elements of a `fintype` must have a maximal element. -/
theorem imo1969_q1 : set.infinite good_nats :=
⟨begin
  intro h,
  obtain ⟨m, hm1, hm2⟩ := h.elems.exists_maximal ⟨a 0, by apply h.complete⟩,
  exact hm2 (a m) (by apply h.complete) (lt_a m)
end⟩
