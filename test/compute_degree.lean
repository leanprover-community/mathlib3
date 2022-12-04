import tactic.compute_degree

open polynomial
open_locale polynomial

variables {R : Type*} [semiring R] {a b c d e : R}

example {R : Type*} [ring R] (h : ∀ {p q : R[X]}, p.nat_degree ≤ 0 → (p * q).nat_degree = 0) :
  nat_degree (- 1 * 1 : R[X]) = 0 :=
begin
  apply h _,
  compute_degree_le,
end

example {p : R[X]} {n : ℕ} {p0 : p.nat_degree = 0} :
 (p ^ n).nat_degree ≤ 0 :=
by compute_degree_le

example {p : R[X]} {n : ℕ} {p0 : p.nat_degree = 0} :
 (p ^ n).nat_degree ≤ 0 :=
by cases n; compute_degree_le

example {p q r : R[X]} {a b c d e f m n : ℕ} {p0 : p.nat_degree = a} {q0 : q.nat_degree = b}
  {r0 : r.nat_degree = c} :
  (((q ^ e * p ^ d) ^ m * r ^ f) ^ n).nat_degree ≤ ((b * e + a * d) * m + c * f) * n :=
begin
  compute_degree_le,
  rw [p0, q0, r0],
end

example {F} [ring F] {p : F[X]} (p0 : p.nat_degree ≤ 0) :
  p.nat_degree ≤ 0 :=
begin
  success_if_fail_with_msg {compute_degree_le} "Goal did not change",
  exact p0,
end

example {F} [ring F] {p q : F[X]} (h : p.nat_degree + 1 ≤ q.nat_degree) :
  (- p * X).nat_degree ≤ q.nat_degree :=
by compute_degree_le

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n - C a * X ^ 10 : F[X]) ≤ 10 :=
by compute_degree_le

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
by compute_degree_le

example (n : ℕ) (h : 1 + n < 11) :
  degree (5 * X ^ n + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  { exact nat.lt_succ_iff.mp h },
  { exact nat.lt_succ_iff.mp ((lt_one_add n).trans h) },
end

example {n : ℕ} (h : 1 + n < 11) :
  degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 :=
by compute_degree_le

example {m s: ℕ} (ms : m ≤ s) (s1 : 1 ≤ s) : nat_degree (C a * X ^ m + X + 5) ≤ s :=
by compute_degree_le; assumption

example : nat_degree (7 * X : R[X]) ≤ 1 :=
by compute_degree_le

example : (1 : R[X]).nat_degree ≤ 0 :=
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

example {F} [ring F] {n m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : F} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le; assumption

example {F} [ring F] : nat_degree (X ^ 4 + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le
