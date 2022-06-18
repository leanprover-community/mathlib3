import tactic.compute_degree

open polynomial tactic
open_locale polynomial
--set_option pp.all true

/-
example {F} [ring F] [nontrivial F] (a b c : F[X]) :
  nat_degree (a + a : F[X]) = 0 :=
begin
  compute_degree,
end
-/

example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by {
  compute_degree,
/-
  norm_num,
  simp only [polynomial.coeff_mul_X_pow', polynomial.coeff_monomial, polynomial.coeff_bit0_mul, polynomial.coeff_bit1_mul, polynomial.coeff_neg,
    zero_add, add_zero, polynomial.coeff_one, zero_eq_bit0, bit0_eq_zero, if_false, neg_zero', add_zero, one_ne_zero, not_false_iff],
  rw polynomial.coeff_one,
  norm_num,
  norm_num,
  --norm_num,
  squeeze_simp [coeff_one],
  simp only [coeff_one, zero_eq_bit0, bit0_eq_zero, if_false, neg_zero', add_zero, one_ne_zero, not_false_iff],
  {compute_degree.compute_degree_le_core ff},
  refine (polynomial.nat_degree_one.le.trans (nat.zero_le _)),
-/
  }
--#exit
example {R} [semiring R] [nontrivial R] {a b c d e : R} :
  nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  (C a * X ^ 0 + (C b * X ^ 5 + X ^ 10 + C c * X ^ 2) + --0 * X ^ 10 +
  X ^ 4 * X ^ 5) + C e * X ^ 9 + monomial 9 10) = 10 :=
begin
  compute_degree,
/-
  simp only [coeff_mul_X_pow', coeff_monomial],
  norm_num,

  simp only [coeff_C_mul, coeff_X_pow_self, mul_one, map_bit0, ne.def,
  coeff_mul_X_pow', bit1_le_bit1, bit0_le_bit0, nat.one_le_bit0_iff, nat.lt_one_iff, eq_self_iff_true,   if_true],
-/
end
example {R} [semiring R] (a b c : R) (h3 : (3 : R) ≠ 0) (f g h : R[X]) :
  (C a + X + monomial 3 3 : R[X]).nat_degree = 3 :=
begin
  compute_degree,
end

--#exit

example {R} [semiring R] (a b c : R) (h3 : (3 : R) ≠ 0) (f g h : R[X]) :
  (C a + X + 1 + C (c * 4 * a) * X ^ 2 + X + X + C 6 + monomial 3 3 + 1: R[X]).nat_degree = 3 :=
begin
  compute_degree,
end

/-- goal did not change
set_option pp.all true
example {F : Type*} [ring F] [nontrivial F] (a b c : F[X]) :
  nat_degree (X + a + X : F[X]) = 1 :=
begin
  compute_degree,
end
--/

example {R : Type*} [ring R] {p q : R[X]} (h : p.nat_degree + 1 ≤ q.nat_degree) :
  ( p * X : R[X]).nat_degree ≤ q.nat_degree :=
by compute_degree_le

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
by compute_degree_le

example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by {
  compute_degree,
  }
--#exit
variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

section tests_for_compute_degree

example {n : ℕ} (h : 1 + n < 11) :
  degree (X ^ 5 + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  exact nat.lt_succ_iff.mp h,
end

example (a0 : a ≠ 0) : nat_degree (C a * X ^ 2) = 2 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›",
  exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›
end

example (a0 : a ≠ 0) : nat_degree (C a * X) = 1 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›",
  exact polynomial.nat_degree_C_mul_X _ ‹_›
end

example : nat_degree (C a) = 0 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "Try this: exact polynomial.nat_degree_C _",
  exact polynomial.nat_degree_C _
end

example {R : Type*} [ring R] (a : R) (h : -a ≠ 0) :
  nat_degree (C a * X ^ 2 + 1 : polynomial R) = 2 :=
by { compute_degree, exact neg_ne_zero.mp h }

example {R : Type*} [ring R] (h : ¬ (2 : R) = 0) :
  nat_degree (2 * X ^ 2 + 1 : polynomial R) = 2 :=
by compute_degree

/--  Alex's example. -/
example [char_zero R] :
  nat_degree (2 * X ^ 2 + 1 : polynomial R) = 2 :=
by compute_degree

example {R : Type*} [ring R] (h : ¬ (21 : R) = 0) :
  nat_degree (21 * X ^ 2 + 1 : polynomial R) = 2 :=
by compute_degree

example {R : Type*} [ring R] (a : R) (h : -a ≠ 0) : nat_degree (C a * X + 1 : polynomial R) = 1 :=
by { compute_degree, exact neg_ne_zero.mp h }

/--  Michael's example. -/
example {F} [field F] : nat_degree (X ^ 4 + C 1 : F[X]) = 4 :=
by compute_degree

example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by {compute_degree,
  }

example {F} [field F] : nat_degree (C 1 * X ^ 4 + X + C 1 : F[X]) = 4 :=
by compute_degree

example {F} [field F] {a : F} (a0 : a ≠ 0) : nat_degree (C a * X + C 1 : F[X]) = 1 :=
by compute_degree

example {F} [field F] {a : F} (a0 : a ≠ 0) : nat_degree (C a * X ^ 2 + C 1 : F[X]) = 2 :=
by compute_degree

example (ha : a ≠ 0) : nat_degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
by compute_degree

example (ha : a ≠ 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
begin
  success_if_fail_with_msg {compute_degree_le}
    "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`",
  compute_degree,
end

section non_trivial_assumption
variable [nontrivial R]

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree

example : nat_degree (X : R[X]) = 1 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "Try this: exact polynomial.nat_degree_X",
  exact polynomial.nat_degree_X
end

example : nat_degree (X ^ 4 : R[X]) = 4 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "Try this: exact polynomial.nat_degree_X_pow _",
  exact polynomial.nat_degree_X_pow _
end

example : nat_degree (X + 1 : polynomial R) = 1 :=
by compute_degree

example : nat_degree (C 1 * X + 1 : polynomial R) = 1 :=
by compute_degree

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree

example : nat_degree (monomial 1 c + monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + 0 * X ^ 10 + monomial 9 1 + C e * X) = 9 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "'10' is the expected degree
--'9' is the given degree
--",
  rw zero_mul,
  compute_degree,
end

example [nontrivial R] : (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X).nat_degree = 10 :=
by compute_degree

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X + bit0 0 : R[X]) = 10 :=
begin
  compute_degree,
end

end non_trivial_assumption
example (n : ℕ) (h : 1 + n < 11) :
  degree (X ^ n + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  { exact nat.lt_succ_iff.mp h },
  { exact nat.lt_succ_iff.mp ((lt_one_add n).trans h) },
end

example {n : ℕ} (h : 1 + n < 11) :
  degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 :=
by compute_degree_le!

example {R : Type*} [semiring R] {n : ℕ} (a : R) (h : 1 + n ≤ 10) :
  degree (5 * X ^ 5 + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
end

example {n : ℕ} (h : 1 + n < 11) :
  degree (X ^ 5 + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  exact nat.lt_succ_iff.mp h,
end

end tests_for_compute_degree

section tests_for_compute_degree_le

example {m s: ℕ} (ms : m ≤ s) (s1 : 1 ≤ s) : nat_degree (C a * X ^ m + X + 5) ≤ s :=
by compute_degree_le; assumption

example : nat_degree (C 7 * X : R[X]) ≤ 1 :=
by compute_degree_le

example : (7 : polynomial R).nat_degree ≤ 4 :=
by compute_degree_le

example : (1 : polynomial R).nat_degree ≤ 0 :=
begin
--  success_if_fail_with_msg {compute_degree}
--    "Goal is not of the form
--`f.nat_degree = d` or `f.degree = d`",
  compute_degree_le
end

example : (1 : polynomial R).nat_degree ≤ 0 :=
by compute_degree_le

example : nat_degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
by compute_degree_le

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 :=
by compute_degree_le

example {n : ℕ} : nat_degree (0 * (X ^ 0 + X ^ n) * monomial 5 c * monomial 6 c) ≤ 9 :=
begin
  success_if_fail_with_msg {compute_degree_le}
    "the given polynomial has a term of expected degree
at least '11'",
  rw [zero_mul, zero_mul, zero_mul, nat_degree_zero],
  exact nat.zero_le _
end

example : nat_degree (monomial 0 c * (monomial 0 c * C 1) + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 :=
by compute_degree_le

example : nat_degree (C 0 : R[X]) ≤ 0 :=
by compute_degree_le

example {F} [ring F] {n m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : F} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le; assumption

example {F} [ring F] {n m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : F} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le; assumption

example {F} [ring F] : nat_degree (X ^ 4 + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le

end tests_for_compute_degree_le
