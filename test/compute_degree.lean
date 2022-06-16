import tactic.compute_degree

open polynomial tactic
open_locale polynomial

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
begin
  compute_degree_le,
end

variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

section tests_for_compute_degree

example {n : ℕ} (h : 1 + n < 11) :
  degree (X ^ n + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  { exact nat.lt_succ_iff.mp h },
  { exact nat.lt_succ_iff.mp ((lt_one_add n).trans h) },
end

example {n : ℕ} (h : 1 + n < 11) :
  degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 :=
begin
  compute_degree_le!,
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
/-  this is commented, since `compute_degree_le` fails with a `success_if_fail` fails, but
--  I made it also trace a message of what should be the "correct" degree.
  success_if_fail_with_msg {compute_degree_le}
    "success_if_fail combinator failed, given tactic succeeded",
-/
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
