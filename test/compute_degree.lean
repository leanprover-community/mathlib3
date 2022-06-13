import tactic.compute_degree

open polynomial
open_locale polynomial

variables {R : Type*} [semiring R] [nontrivial R] {f g h : R[X]} {a b c d e : R}
set_option profiler true

example : nat_degree (C 7 * X : R[X]) ≤ 1 :=
by compute_degree_le
--#exit
example : (7 : polynomial R).nat_degree ≤ 4 :=
begin
  compute_degree_le,
--  refine (polynomial.nat_degree_one.le.trans (nat.zero_le _)),
end
--#exit
example {F} [ring F] [nontrivial F] {n m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : F} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : F[X]) ≤ 4 :=
by compute_degree_le; assumption

example : (1 : polynomial R).nat_degree ≤ 4 :=
begin
  compute_degree_le,
--  refine (polynomial.nat_degree_one.le.trans (nat.zero_le _)),
end
--#exit
--namespace tactic
--open expr
/-
meta def single_term_resolve_le : expr → tactic unit
--| `((⇑(@polynomial.C %%R1 %%nin1) %%a) * %%b) := do trace "here", failed
| (app `(⇑(@polynomial.monomial %%R %%inst %%n)) x) := do trace "here",
  refine ``((polynomial.nat_degree_monomial_le %%x).trans (by norm_num))
--  assumption <|> interactive.exact ``(one_ne_zero) <|> skip
| (app `(⇑(@polynomial.C %%R %%inst)) x) :=
  interactive.exact ``((polynomial.nat_degree_C _).le.trans (nat.zero_le _))
| `(@has_pow.pow (@polynomial %%R %%nin) ℕ %%inst %%mX %%n) :=
  nontriviality_by_assumption R *>
  refine ``(polynomial.nat_degree_X_pow %%n)
| `(@polynomial.X %%R %%inst) :=
  nontriviality_by_assumption R *>
  interactive.exact ``(polynomial.nat_degree_X)
| e := C_mul_terms e
-/

/-
#check guess_degree
meta def single_term_resolve_le : expr → tactic unit
| (app `(⇑(@polynomial.monomial %%R %%inst %%n)) x) := do trace "here",
  refine ``((polynomial.nat_degree_monomial_le %%x).trans (by norm_num))
| (app `(⇑(@polynomial.C %%R %%inst)) x) :=
  interactive.exact ``((polynomial.nat_degree_C _).le.trans (nat.zero_le _))
| `(@has_pow.pow (@polynomial %%R %%nin) ℕ %%inst %%mX %%n) :=
  refine ``((nat_degree_X_pow_le %%n).trans (by norm_num))
| `(@polynomial.X %%R %%inst) :=
  refine ``(nat_degree_X_le.trans (by norm_num))
| `(%%a * %%Xp) := do da ← guess_degree a, dXp ← guess_degree Xp,trace da, trace dXp,
  refine ``(nat_degree_mul_le.trans ((add_le_add _ _).trans (by norm_num : %%da + %%dXp ≤ _))),
  single_term_resolve_le a,
  single_term_resolve_le Xp
| e := C_mul_terms e

lemma pro : nat_degree (X ^ 0 : polynomial R) ≤ 10 :=
by
{ refine (nat_degree_X_pow_le _).trans _,

   refine (polynomial.nat_degree_monomial_le _).trans _,
  norm_num
  --single_term_resolve_le lhs
}
example : nat_degree (C a * X ^ 0) ≤ 10 :=
by
{ refine nat_degree_mul_le.trans (le_trans _ (by norm_num : 0 + 0 ≤ _)),
  refine add_le_add _ _,

  refine (nat_degree_C_mul_X_pow_le _ _).trans _,

   refine (polynomial.nat_degree_monomial_le _).trans _,
  norm_num
  --single_term_resolve_le lhs
}



example : nat_degree (X ^ 4 * monomial 6 c : polynomial R) ≤ 10 :=
by do `(polynomial.nat_degree %%lhs ≤ %%deg) ← target,
  single_term_resolve_le lhs
--  trace lhs,
--  apply polynomial.nat_degree_monomial_le,
--  target >>= trace

end tactic



#exit
--/
lemma pro : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree


example {m s: ℕ} (ms : m ≤ s) (s1 : 1 ≤ s) : nat_degree (C a * X ^ m + X + 5) ≤ s :=
by {compute_degree_le; assumption,
--  sorry,
--  refine (polynomial.nat_degree_mul_le.trans ((add_le_add _ _).trans (_ : 0 + m ≤ _))),
--assumption
}
--#exit
example : nat_degree (X + 1 : polynomial R) = 1 :=
by compute_degree

example : nat_degree (C 1 * X + 1 : polynomial R) = 1 :=
by {compute_degree}

example {R : Type*} [ring R] (a : R) (h : -a ≠ 0) :
  nat_degree (C a * X ^ 2 + 1 : polynomial R) = 2 :=
by { compute_degree, exact neg_ne_zero.mp h }

example {R : Type*} [ring R] (h : ¬ (2 : R) = 0) :
  nat_degree (2 * X ^ 2 + 1 : polynomial R) = 2 :=
by compute_degree

/--  Alex's example. -/
example {R : Type*} [semiring R] [char_zero R] :
  nat_degree (2 * X ^ 2 + 1 : polynomial R) = 2 :=
by compute_degree

example {R : Type*} [ring R] (h : ¬ (21 : R) = 0) :
  nat_degree (21 * X ^ 2 + 1 : polynomial R) = 2 :=
by compute_degree

example {R : Type*} [ring R] (a : R) (h : -a ≠ 0) : nat_degree (C a * X + 1 : polynomial R) = 1 :=
by { compute_degree, exact neg_ne_zero.mp h }

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by compute_degree

example : nat_degree (monomial 1 c + monomial 5 c * monomial 1 c + monomial 7 d + monomial 9 1 +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) = 10 :=
by {compute_degree, }

/--  Michael's example. -/
example {F} [field F] : nat_degree (X ^ 4 + C 1 : F[X]) = 4 :=
by compute_degree

example {F} [ring F] [nontrivial F] {n m : ℕ} (n4 : n ≤ 4) (m4 : m ≤ 4) {a : F} :
  nat_degree (C a * X ^ n + X ^ m + bit1 1 : F[X]) ≤ 4 :=
by { compute_degree_le; assumption,
--compute_degree_le,
 }

example {F} [ring F] : nat_degree (X ^ 4 + bit1 1 : F[X]) ≤ 4 :=
by {compute_degree_le, }

example {F} [ring F] [nontrivial F] : degree (X ^ 4 + C (- 1) : F[X]) = 4 :=
by compute_degree

example {F} [field F] : nat_degree (C 1 * X ^ 4 + X + C 1 : F[X]) = 4 :=
by compute_degree

example {F} [field F] {a : F} (a0 : a ≠ 0) : nat_degree (C a * X + C 1 : F[X]) = 1 :=
by compute_degree

example {F} [field F] {a : F} (a0 : a ≠ 0) : nat_degree (C a * X ^ 2 + C 1 : F[X]) = 2 :=
by compute_degree

example : nat_degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
by {compute_degree_le, }

example (ha : a ≠ 0) : nat_degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
by compute_degree

example (ha : a ≠ 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
by compute_degree

/-
--  This test produces a suggestion.  I would like to uncomment it, but do not know how to
--  prevent a noisy file
/--  `Try this: exact nat_degree_X_pow _` -/
example {F} [division_ring F] : nat_degree (X ^ 4 : F[X]) = 4 :=
by compute_degree

--  This test produces a suggestion.  I would like to uncomment it, but do not know how to
--  prevent a noisy file
/--  `Try this: exact nat_degree_C _` -/
example {F} [field F] : nat_degree (C 4 : F[X]) = 0 :=
by compute_degree

--  This test produces a suggestion.  I would like to uncomment it, but do not know how to
--  prevent a noisy file
/--  `Try this: exact nat_degree_X` -/
example {F} [field F] : nat_degree (X : F[X]) = 1 :=
by compute_degree
--/

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

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X : R[X]) ≤ 10 :=
by compute_degree_le

/-  fails with error message `should the degree be '10'?`
example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X : R[X]) = 9 :=
by compute_degree

--  fails with error message `should the degree bound be '10'?`
example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X : R[X]) ≤ 9 :=
by compute_degree_le
--/

example : nat_degree (monomial 5 c * monomial 1 c + monomial 7 d +
  C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C 7 * X ^ 10 + C e * X : R[X]) ≤ 10 :=
by compute_degree_le

example : nat_degree (monomial 0 c * monomial 0 c + monomial 0 d + C 1 + C a * X ^ 0 : R[X]) ≤ 0 :=
by compute_degree_le

example : nat_degree (C 1 : R[X]) ≤ 0 :=
by compute_degree_le
