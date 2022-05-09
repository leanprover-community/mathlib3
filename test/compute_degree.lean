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

lemma pro {h : C d ≠ 0} (f10 : f.nat_degree ≤ 10) :
  nat_degree (monomial 1 c + monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
begin
  compute_degree,
end

/--  Michael's example. -/
example {F} [field F] : nat_degree (X ^ 4 + C 1 : F[X]) = 4 :=
begin
  compute_degree,
end

/--  `Try this: exact nat_degree_X_pow _` -/
example {F} [division_ring F] : nat_degree (X ^ 4 : F[X]) = 4 :=
begin
  compute_degree,
end

/--  `Try this: exact nat_degree_C _` -/
example {F} [field F] : nat_degree (C 4 : F[X]) = 0 :=
begin
  compute_degree,
end

/--  `Try this: exact nat_degree_X` -/
example {F} [field F] : nat_degree (X : F[X]) = 1 :=
begin
  compute_degree,
end

example {F} [field F] : nat_degree (X ^ 4 + X + C 1 : F[X]) = 4 :=
by compute_degree

/-  This fails since there are non-closed `ℕ`-expressions.
lemma pro {h : C d ≠ 0} (f10 : f.nat_degree ≤ 10) :
  nat_degree (monomial 5 c * monomial 1 c + f + monomial 7 d +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C d * X ^ 10 + C e * X + bit0 0 : R[X]) = 10 :=
begin
  compute_degree,
end
-/
