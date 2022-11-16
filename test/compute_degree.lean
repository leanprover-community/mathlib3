import tactic.compute_degree

open polynomial
open_locale polynomial
--universe u

example {F : Type*} [comm_ring F] (t : ((2 : ℕ) : F) ≠ 0) (a b c : F[X])
  (a0 : a.nat_degree = 0) :
  nat_degree (X + a + X : F[X]) = 1 :=
begin
--  sorry;
  compute_degree,
  { exact a0.le },
  rw ← two_mul,
  compute_degree,
end

section suggestions
variables {F : Type*} [ring F] [nontrivial F] (n : ℕ) (a : F)

/-
Should these commented examples be solved by `compute_degree`?
example : degree (X ^ n : F[X]) = n :=
example : degree (X ^ n : F[X]) = n :=
example (a0 : a ≠ 0) : degree (C a : F[X]) = 0 :=
example : degree (X : F[X]) = 1 :=
example (a0 : a ≠ 0) : degree (C a * X ^ n : F[X]) = n :=
example (a0 : a ≠ 0) : degree (C a * X : F[X]) = 1 :=
-/

example : nat_degree (X ^ n : F[X]) = n :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_X_pow _",
     exact polynomial.nat_degree_X_pow _ }

example : nat_degree (C a : F[X]) = 0 :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_C _",
     exact polynomial.nat_degree_C _ }

example : nat_degree (X : F[X]) = 1 :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_X",
     exact polynomial.nat_degree_X }

example (a0 : a ≠ 0) : nat_degree (C a * X ^ n : F[X]) = n :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›",
     exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_› }

example (a0 : a ≠ 0) : nat_degree (C a * X : F[X]) = 1 :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›",
     exact polynomial.nat_degree_C_mul_X _ ‹_› }

end suggestions

/-  Issue: goals hidden and needing recover. -/
example {F : Type*} [ring F] (h37 : ((37 : ℕ) : F) ≠ 0) :
  nat_degree (((2 * 2 + 2) ^ 2 + 1) * X + 1 : F[X]) = 1 :=
begin
--  have : ((((2 * 2 + 2) ^ 2 + 1)) : F[X]) = C ((((2 * 2 + 2) ^ 2 + 1) : ℕ) : F),
--  simp only [nat.cast_add, nat.cast_pow, nat.cast_mul, nat.cast_bit0, nat.cast_one, map_add, map_pow, map_mul, C_bit0, map_one],
--  rw this,
  compute_degree,
--  recover,  -- this is no longer needed.
end

/-  Issue: cannot use `norm_num` on one of the goals, since it times out
(and would likely not do much).
Seems to be resolved, but the tactic is still slow.
 -/
example {F : Type*} [ring F] (t : ((2 : ℕ) : F) ≠ 0) : degree (X + 0 + X : F[X]) = 1 :=
begin
  compute_degree,
  --  from here, could be automated, but currently is not.
  --  the issue though is that I would like to use `norm_num`
  --  to discharge other goals, but currently I cannot since here
  --  it would timeout.
--  norm_num, -- does not time out, but is very slow
  rw [← two_mul],
  compute_degree,
--  convert nat_degree_C_mul_X _ t,
--  simp only [nat.cast_bit0, nat.cast_one, C_bit0, map_one],
end

section one_term_polynomials
variables {F : Type*} [comm_semiring F] [nontrivial F] (n : ℕ) (a : F)

example : nat_degree (X ^ n : F[X]) = n :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_X_pow _",
     exact polynomial.nat_degree_X_pow _ }

example : nat_degree (C a : F[X]) = 0 :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_C _",
     exact polynomial.nat_degree_C _ }

example : nat_degree (X : F[X]) = 1 :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_X",
     exact polynomial.nat_degree_X }

example (a0 : a ≠ 0) : nat_degree (C a * X ^ n : F[X]) = n :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›",
     exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_› }

example (a0 : a ≠ 0) : nat_degree (C a * X : F[X]) = 1 :=
by { success_if_fail_with_msg {compute_degree}
       "Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›",
     exact polynomial.nat_degree_C_mul_X _ ‹_› }

end one_term_polynomials

example {F : Type*} [comm_semiring F] [nontrivial F] : nat_degree (1 + X : F[X]) = 1 :=
by compute_degree

example {F : Type*} [comm_semiring F] [nontrivial F] : nat_degree (1 * X : F[X]) = 1 :=
by {compute_degree, }

example {F : Type*} [semiring F] (h2 : (2 : F) ≠ 0) : nat_degree (X + 1 + X + 1 : F[X]) = 0 + 1 :=
begin
  compute_degree,
  rw ← two_mul,
  compute_degree,
end


example {F : Type*} [ring F] (h2 : (2 : F) ≠ 0) : degree (X ^ 4 + (- 3) + X ^ 4 : F[X]) = 4 :=
begin
--sorry;
  compute_degree,
--  norm_num, --times out, but does not using `{F : Type u}` or `[semiring F]`.
  rw ← two_mul,
  compute_degree,
--  norm_num,
--  assumption,
--  norm_num,
end

example : (X ^ 4 + 1 + X ^ 4 : polynomial ℕ).nat_degree = 1 + 1 + 1 + 1 :=
by {
  compute_degree,
  rw ← two_mul,
  compute_degree,
  }

example {R} [semiring R] [nontrivial R] {a b c d e : R} :
  nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  (C a * X ^ 0 + (C b * X ^ 5 + X ^ 10 + C c * X ^ 2) + --0 * X ^ 10 +
  X ^ 4 * X ^ 5) + C e * X ^ 9 + monomial 9 10) = 10 :=
begin
  compute_degree,
  repeat { refine nat.succ_le_succ _ },
  repeat { exact nat.zero_le _ },
end

example {R} [semiring R] (a b c : R) (h3 : (3 : R) ≠ 0) (f g h : R[X]) :
  (C a + X + monomial 3 3 : R[X]).nat_degree = 3 :=
begin
  compute_degree,
end

example {R} [semiring R] (a b c : R) (h3 : (3 : R) ≠ 0) (f g h : R[X]) :
  (C a + X + 1 + C (c * 4 * a) * X ^ 2 + X + X + C 6 + monomial 3 3 + 1: R[X]).nat_degree = 3 :=
begin
  compute_degree,
end

/- From here
This part should be better and about `compute_degree_le`. -/
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

/-  To here. -/
example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by compute_degree

section tests_for_compute_degree

example {n : ℕ} (h : 1 + n < 11) :
  degree (X ^ 5 + (X * monomial n 1 + X * X) + C a + C a * X ^ 10) ≤ 10 :=
begin
  compute_degree_le,
  repeat { refine nat.succ_le_succ _ },
  repeat { exact nat.zero_le _ <|> refl },
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
  success_if_fail_with_msg {compute_degree}
    "'10' is the expected degree
'9' is the given degree
",
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

example {F} [ring F] {n m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : F} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le; assumption

example {F} [ring F] : nat_degree (X ^ 4 + bit1 1 : F[X]) ≤ 4 :=
by {compute_degree_le }

end tests_for_compute_degree
