import tactic.compute_degree

open polynomial
open_locale polynomial

variables {R : Type*} [semiring R] [nontrivial R] {f g h : R[X]} {a b c d e : R}

example {h : C d ≠ 0} (f10 : f.nat_degree ≤ 10) :
  nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
begin
  compute_degree,
end

example {h : C d ≠ 0} (f10 : f.nat_degree ≤ 10) :
  nat_degree (monomial 1 c + monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
begin
  compute_degree,
end

/--  Michael's example. -/
example {F} [field F] : nat_degree (X ^ 4 + C 1 : F[X]) = 4 :=
by compute_degree

example {F} [field F] : nat_degree (X ^ 4 + X + C 1 : F[X]) = 4 :=
by compute_degree

/-
--  This test produces a suggestion.  I would like to uncomment it, but do not know how to
--  prevent a noisy file
/--  `Try this: exact nat_degree_X_pow _` -/
example {F} [division_ring F] : nat_degree (X ^ 4 : F[X]) = 4 :=
begin
  compute_degree,
end

--  This test produces a suggestion.  I would like to uncomment it, but do not know how to
--  prevent a noisy file
/--  `Try this: exact nat_degree_C _` -/
example {F} [field F] : nat_degree (C 4 : F[X]) = 0 :=
begin
  compute_degree,
end

--  This test produces a suggestion.  I would like to uncomment it, but do not know how to
--  prevent a noisy file
/--  `Try this: exact nat_degree_X` -/
example {F} [field F] : nat_degree (X : F[X]) = 1 :=
begin
  compute_degree,
end
-/

--  The first `compute_degree` fails since there are non-closed `ℕ`-expressions.
--  The second one works, since the non-closed expressions are gone.
example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X + bit0 0 : R[X]) = 10 :=
begin
  success_if_fail { compute_degree },
  have : ((monomial 5) c * (monomial 1) c + (monomial 7) d + C a * X ^ 0 + C b * X ^ 5 +
    C c * X ^ 2 + X ^ 10 + C e * X).nat_degree = 10,
  { compute_degree },
  rwa nat_degree_add_eq_left_of_nat_degree_lt,
  refine ((le_of_eq (by simp : _ = 0)).trans_lt _),
  exact lt_of_lt_of_le nat.succ_pos' this.ge
end
