import tactic.compute_degree

open polynomial tactic
open_locale polynomial

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
begin
  compute_degree_le,
end

example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by compute_degree

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
  success_if_fail_with_msg {compute_degree}
    "Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›",
  exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›
end

example (a0 : a ≠ 0) : nat_degree (C a * X) = 1 :=
begin
  success_if_fail_with_msg {compute_degree}
    "Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›",
  exact polynomial.nat_degree_C_mul_X _ ‹_›
end

example : nat_degree (C a) = 0 :=
begin
  success_if_fail_with_msg {compute_degree}
    "Try this: exact polynomial.nat_degree_C _",
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
by compute_degree

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
  compute_degree
end

section non_trivial_assumption
variable [nontrivial R]

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree

example : nat_degree (X : R[X]) = 1 :=
begin
  success_if_fail_with_msg {compute_degree}
    "Try this: exact polynomial.nat_degree_X",
  exact polynomial.nat_degree_X
end

example : nat_degree (X ^ 4 : R[X]) = 4 :=
begin
  success_if_fail_with_msg {compute_degree}
    "Try this: exact polynomial.nat_degree_X_pow _",
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

example (h : 9 = 10) : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 9 :=
begin
  success_if_fail_with_msg {compute_degree}
    "should the nat_degree be '10'?",
  rw h,
  compute_degree
end

example (h : (9 : with_bot ℕ) = 10) : degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 9 :=
begin
  success_if_fail_with_msg {compute_degree}
    "should the degree be '10'?",
  rw h,
  compute_degree,
end

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X + bit0 0 : R[X]) = 10 :=
begin
  compute_degree,
end

end non_trivial_assumption

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
  success_if_fail_with_msg {compute_degree}
    "Goal is not of the form
`f.nat_degree = d` or `f.degree = d`",
  compute_degree_le
end

example : (1 : polynomial R).nat_degree ≤ 0 :=
by compute_degree_le

example : nat_degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
by compute_degree_le

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 :=
by compute_degree_le

--  fails with error message `should the degree bound be '10'?`
example (h : 9 = 11) : nat_degree (monomial 5 c * monomial 6 c) ≤ 9 :=
begin
  success_if_fail_with_msg {compute_degree_le}
    "success_if_fail combinator failed, given tactic succeeded",
  rw h,
  compute_degree_le
end

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C 7 * X ^ 10 + C e * X) ≤ 10 :=
by compute_degree_le

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
