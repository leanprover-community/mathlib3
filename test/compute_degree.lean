import tactic.compute_degree

open polynomial tactic
open_locale polynomial

/-
example {F} [ring F] [nontrivial F] : degree (X ^ 4 + X + C (- 1) : F[X]) ≤ 4 :=
by {
--  refine polynomial.degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr _),
  compute_degree_le, norm_num}
-/
example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
begin
--by do  `(polynomial.nat_degree %%tl ≤ %%tr) ← target,
--  trace $ interactive.check_deg_le tl tr,
--  repeat $ target >>= interactive.resolve_sum_step
  compute_degree_le,
end

--#exit
example {F} [ring F] {a : F} (h : 1 = 10) :
  degree (X ^ 5 + (X + X * X) + C a + C a * X ^ 10 : F[X]) ≤ 10 :=
begin
  compute_degree_le,
end
--  any_goals { exact rfl.le },


--`(polynomial.nat_degree %%lhs ≤ %%rhs) ← target,
--  single_term_resolve_le lhs
/-
--#exit
example {F} [ring F] [nontrivial F] {a : F} :
  nat_degree (X : F[X]) ≤ 1 :=
by do t ← target,
interactive.resolve_sum_step t
--`(polynomial.nat_degree %%lhs ≤ %%rhs) ← target,
--  single_term_resolve_le lhs


--#exit
example {F} [ring F] [nontrivial F] {a : F} :
  nat_degree (C a * X ^ 5 + 1 + X * X + X ^ 4 + X + X * X + C (- 1) : F[X]) ≤ 4 :=
by do repeat (do gs ← get_goals,
    gs.mmap' (λ t, do typ ← infer_type t, trace typ, try $ interactive.resolve_sum_step typ)),
    `(polynomial.nat_degree %%lhs ≤ %%rhs) ← target,
  single_term_resolve_le lhs
--  t ← target,
--  interactive.resolve_sum_step t,
--  gs ← get_goals,
--  gs.mmap infer_type >>= trace

--  interactive.resolve_sum t


example {F} [ring F] [nontrivial F] : degree (X ^ 4 + X + C (- 1) : F[X]) = 4 :=
by do t ← target,
  interactive.resolve_sum t

--{compute_degree, norm_num}

#exit
-/
example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by compute_degree

--#exit
variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

/-
example : nat_degree (X ^ 10 + C e * X) ≤ 9 :=
begin
 compute_degree_le,

 any_goals { norm_num }
end

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 9 :=
by {compute_degree_le, any_goals { norm_num }, }
-/

--#exit
section tests_for_compute_degree

example (a0 : a ≠ 0) : nat_degree (C a * X ^ 2) = 2 :=
begin
  success_if_fail_with_msg { compute_degree }
    ("Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›"),
  exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›
end

example (a0 : a ≠ 0) : nat_degree (C a * X) = 1 :=
begin
  success_if_fail_with_msg { compute_degree }
    ("Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›"),
  exact polynomial.nat_degree_C_mul_X _ ‹_›
end

example : nat_degree (C a) = 0 :=
begin
  success_if_fail_with_msg { compute_degree }
    ("Try this: exact polynomial.nat_degree_C _"),
  exact polynomial.nat_degree_C _
end

--example {F} [semiring F] : nat_degree (C 1 * X ^ 4 + C 1 : F[X]) = 4 :=
--by compute_degree
--#exit
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
by compute_degree

section non_trivial_assumption
variable [nontrivial R]

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree

example : nat_degree (X : R[X]) = 1 :=
begin
  success_if_fail_with_msg { compute_degree }
    ("Try this: exact polynomial.nat_degree_X"),
  exact polynomial.nat_degree_X
end

example : nat_degree (X ^ 4 : R[X]) = 4 :=
begin
  success_if_fail_with_msg { compute_degree }
    ("Try this: exact polynomial.nat_degree_X_pow _"),
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
  success_if_fail_with_msg { compute_degree }
    ("should the nat_degree be '10'?"),
  rw h,
  compute_degree
end

example (h : (9 : with_bot ℕ) = 10) : degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 9 :=
begin
  success_if_fail_with_msg { compute_degree }
    ("should the degree be '10'?"),
  rw h,
  compute_degree,
end

--  The first `compute_degree` fails since there are non-closed `ℕ`-expressions.
--  The second one works, since the non-closed expressions are gone.
example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X + bit0 0 : R[X]) = 10 :=
begin
  compute_degree,
/-
  success_if_fail { compute_degree },
  have : ((monomial 5) c * (monomial 1) c + (monomial 7) d + C a * X ^ 0 + C b * X ^ 5 +
    C c * X ^ 2 + X ^ 10 + C e * X).nat_degree = 10,
  { compute_degree },
  rwa nat_degree_add_eq_left_of_nat_degree_lt,
  refine (le_of_eq (by simp : _ = 0)).trans_lt _,
  exact lt_of_lt_of_le nat.succ_pos' this.ge
-/
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
  success_if_fail_with_msg { compute_degree }
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

example : nat_degree (monomial 0 c * monomial 0 c + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 :=
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
