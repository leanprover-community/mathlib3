import tactic.compute_degree

open polynomial
open_locale polynomial

variables {R S : Type*} [ring R] [semiring S] {a b c d e : S} {p q r : S[X]} {n : ℕ}

section tests_for_compute_degree_le

example (h : ∀ {p q : R[X]}, p.nat_degree ≤ 0 → (p * q).nat_degree = 0) :
  nat_degree (- 1 * 1 : R[X]) = 0 :=
begin
  apply h _,
  compute_degree_le,
end

example {p0 : p.nat_degree = 0} :
 (p ^ n).nat_degree ≤ 0 :=
by compute_degree_le

example {p0 : p.nat_degree = 0} :
 (p ^ n).nat_degree ≤ 0 :=
by cases n; compute_degree_le

example {a b c d e f m n : ℕ} {p0 : p.nat_degree = a} {q0 : q.nat_degree = b}
  {r0 : r.nat_degree = c} :
  (((q ^ e * p ^ d) ^ m * r ^ f) ^ n).nat_degree ≤ ((b * e + a * d) * m + c * f) * n :=
begin
  compute_degree_le,
  rw [p0, q0, r0],
end

example (p0 : p.nat_degree ≤ 0) :
  p.nat_degree ≤ 0 :=
begin
  success_if_fail_with_msg {compute_degree_le} "Goal did not change",
  exact p0,
end

example {p q : R[X]} (h : p.nat_degree + 1 ≤ q.nat_degree) :
  (- p * X).nat_degree ≤ q.nat_degree :=
by compute_degree_le

example {a : R} (h : n ≤ 10) : nat_degree (X ^ n - C a * X ^ 10) ≤ 10 :=
by compute_degree_le

example (h : n ≤ 10) : nat_degree (X ^ n + C a * X ^ 10) ≤ 10 :=
by compute_degree_le

example (h : 1 + n < 11) :
  degree (250 * X ^ n + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  { exact nat.lt_succ_iff.mp h },
  { exact nat.lt_succ_iff.mp ((lt_one_add n).trans h) },
end

example (h : 1 + n < 11) :
  degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 :=
by compute_degree_le

example {m : ℕ} (ms : m ≤ n) (n1 : 1 ≤ n) : nat_degree (C a * X ^ m + X + 5) ≤ n :=
by compute_degree_le; assumption

example : nat_degree (7 * X : R[X]) ≤ 1 :=
by compute_degree_le

example : (1 : S[X]).nat_degree ≤ 0 :=
by compute_degree_le

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 :=
by compute_degree_le

example : nat_degree (0 * (X ^ 0 + X ^ n) * monomial 5 c * monomial 6 c) ≤ 9 :=
begin
  success_if_fail_with_msg {compute_degree_le}
    "the given polynomial has a term of expected degree\nat least '11'",
  rw [zero_mul, zero_mul, zero_mul, nat_degree_zero],
  exact nat.zero_le _
end

example : nat_degree (monomial 0 c * (monomial 0 c * C 1) + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 :=
by compute_degree_le

example {m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : R} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : R[X]) ≤ 4 :=
by compute_degree_le; assumption

example : nat_degree (X ^ 4 + bit1 1 : R[X]) ≤ 4 :=
by compute_degree_le

end tests_for_compute_degree_le

section tests_for_compute_degree_and_simp_coeff

example : (C a).coeff 0 = a :=
begin
  success_if_fail_with_msg {simp_lead_coeff with da l m} "Try this: simp_lead_coeff with da",
  simp_lead_coeff with da,
  refl,
end

example (h : (5 : S) ≠ 0) :
  (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 + 5 * monomial 11 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X).nat_degree = 11 :=
begin
  compute_degree,
  rwa mul_one,
end

variable [nontrivial R]

example : (X - X + X + 2 : R[X]).degree = 1 :=
begin
  compute_degree,
  norm_num,
end

example : (X - monomial 11 1 : R[X]).nat_degree = 11 :=
begin
  compute_degree,
  exact neg_ne_zero.mpr one_ne_zero,
end

example {a b c d e : R} :
  (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 - monomial 11 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X).nat_degree = 11 :=
begin
  compute_degree,
  exact neg_ne_zero.mpr one_ne_zero,
end

example {a b c d e : R} :
  (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 + monomial 11 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X).monic :=
by prove_monic

/-  The next example shows that `compute_degree!` solves a goal, while `compute_degree` flags
the same goal as "too simple" and returns a "Try this:". -/
example (a0 : a ≠ 0) : let p :=
  (X ^ 11 : R[X]).nat_degree = 11 ∧
  (C a).nat_degree = 0 ∧
  (X : R[X]).nat_degree = 1 ∧
  (C a * X ^ 11).nat_degree = 11 ∧
  (C a * X).nat_degree = 1 in p ∧ p :=
begin
  refine ⟨_, _⟩,
  { repeat { refine ⟨_, _⟩ <|> compute_degree! } },
  { refine ⟨_, _, _, _, _⟩,
    { success_if_fail_with_msg {compute_degree}
        "Try this: exact nat_degree_X_pow _\n\nor\n\nTry this: compute_degree!",
      exact nat_degree_X_pow _ },
    { success_if_fail_with_msg {compute_degree}
        "Try this: exact nat_degree_C _\n\nor\n\nTry this: compute_degree!",
      exact nat_degree_C _ },
    { success_if_fail_with_msg {compute_degree}
        "Try this: exact nat_degree_X\n\nor\n\nTry this: compute_degree!",
      exact nat_degree_X },
    { success_if_fail_with_msg {compute_degree}
        "Try this: exact nat_degree_C_mul_X_pow _ a a0\n\nor\n\nTry this: compute_degree!",
      exact nat_degree_C_mul_X_pow _ a a0 },
    { success_if_fail_with_msg {compute_degree}
        "Try this: exact nat_degree_C_mul_X a a0\n\nor\n\nTry this: compute_degree!",
      exact nat_degree_C_mul_X a a0 } }
end

example {a b : R} {h2 : (2 : R) ≠ 0} :
  ∀ p ∈ [X ^ 2, X ^ 2 - C a * X - C b, X ^ 2 + C b, 2 * X ^ 2, - X ^ 2], nat_degree p = 2 :=
begin
  simp only [list.mem_cons_iff, list.mem_singleton, forall_eq_or_imp, forall_eq],
  repeat
  { try { split },
    compute_degree!;
    rwa mul_one <|> exact neg_ne_zero.mpr one_ne_zero },
end

end tests_for_compute_degree_and_simp_coeff
