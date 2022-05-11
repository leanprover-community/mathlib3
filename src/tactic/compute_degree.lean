/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.move_add
import data.polynomial.degree.lemmas

/-! # `compute_degree` a tactic for compute `nat_degree`s of polynomials

This file defines two main tactics `compute_degree` and `compute_degree_le`.
Applied when the goal is of the form `f.nat_degree = d` or `f.nat_degree ≤ d`, they try to solve it.

See the corresponding doc-strings for more details.

##  Future work

* Add functionality to deal with exponents that are not necessarily natural numbers.
  It may not be hard to allow an option argument to be passed to `compute_degree` that would
  let the tactic know which one is the term of highest degree.  This would bypass the step
  where the exponents get sorted and may make it accessible to continue with the rest of the
  argument with minimal change.
* Add functionality to close `monic` goals and compute `leading_coeff`s.

##  Implementation details

We start with a goal of the form `f.nat_degree = d` (the case `f.nat_degree ≤ d` follows a similar,
easier pattern).

First, we focus on an elementary term of the polynomial `f` and we extract the degree in easy cases:
if `f` is
* `monomial n r`, then we guess `n`,
* `C a`, then we guess `0`,
* `polynomial.X`, then we guess `1`,
* `X ^ n`, then we guess `n`,
* everything else, then we guess `f.nat_degree`.
This happens in `extract_deg_single_term`.

Second, with input a product, we sum the guesses made above on each factor and add them up.
This happens in `extract_deg_single_summand`.

Third, we scan the summands of `f`, searching for one with highest guessed degree.  Here, if a
guess is not a closed term of type `ℕ`, the tactic fails.  This could be improved, but is not
currently in scope.  We return the first term with highest degree and the guessed degree.
This happens in `extract_top_degree_term_and_deg`.

Now, `compute_degree_le` chains together a few lemmas to conclude.  It guesses that the degree of a
sum of terms is at most the degree of each individual term.

_Heuristic:_ there is no cancellation among the terms, at least the ones of highest degree.

Finally, `compute_degree` takes one extra step.  It isolates the term of highest guessed degree
and assumes that all remaining terms have smaller degree.  It checks that the degree of the highest
term is what it is claimed (and further assumes that the highest term is a pure `X`-power, `X ^ n`,
a pure `X` term or a product of one of these by `C a` and checks that the assumption `a ≠ 0` is in
context).
`compute_degree` then outsources the rest of the computation to `compute_degree_le`, once the goal
has been appropriately replaced.

###  Error reporting
The tactics report that
* naturals involving variables are not allowed in exponents;
* when a simple lemma application would have sufficed (via a `Try this: ...`);
* when the guessed degree is incompatible with the goal, suggesting a sharper value.
-/

namespace polynomial
open_locale polynomial
variables {R : Type*} [semiring R]

lemma nat_degree_monomial_le (a : R) {m n : ℕ} (mn : m ≤ n) :
  (monomial m a).nat_degree ≤ n :=
begin
  classical,
  rw polynomial.nat_degree_monomial,
  split_ifs; simp [mn],
end

lemma nat_degree_X_pow_le {m n : ℕ} (mn : m ≤ n) :
  (X ^ m : R[X]).nat_degree ≤ n :=
begin
  nontriviality R,
  rwa polynomial.nat_degree_X_pow,
end

lemma nat_degree_add_le_iff_left {m n : ℕ} (mn : m ≤ n) (f g : R[X]) (gm : g.nat_degree ≤ m) :
  (f + g).nat_degree ≤ n ↔ f.nat_degree ≤ n :=
begin
  by_cases fm : f.nat_degree ≤ m,
  { refine ⟨λ h, fm.trans mn, λ fn, _⟩,
    refine (nat_degree_add_le _ _).trans (max_le fn (gm.trans mn)) },
  { rw nat_degree_add_eq_left_of_nat_degree_lt,
    exact gm.trans_lt (not_le.mp fm) }
end

/--  Useful for hiding the `classical` in the proof. -/
lemma nat_degree_monomial_eq {R : Type*} [semiring R] (i : ℕ) {r : R} (r0 : r ≠ 0) :
  (monomial i r).nat_degree = i :=
begin
  classical,
  exact eq.trans (nat_degree_monomial _ _) (if_neg r0),
end

/-- Useful to expose easy hypotheses:
* `df` should be dealt with by `single_term_resolve`,
* `dg` should be dealt with by `compute_degree_le`.
-/
lemma nat_degree_add_left_succ {R : Type*} [semiring R] (n : ℕ) (f g : polynomial R)
  (df : f.nat_degree = n + 1) (dg : g.nat_degree ≤ n) :
  (g + f).nat_degree = n + 1 :=
by rwa nat_degree_add_eq_right_of_nat_degree_lt (dg.trans_lt (nat.lt_of_succ_le df.ge))

end polynomial

namespace tactic.interactive
open tactic
setup_tactic_parser

/-- `C_mul_terms e` produces a proof of `e.nat_degree = ??` in the case in which `e` is of the form
`C a * X (^ n)?`.  It has special support for `C 1`, when there is a `nontrivial` assumption on the
base-semiring. -/
meta def C_mul_terms : expr → tactic unit
| `(has_mul.mul %%C %%X) := match X with
  | `(@polynomial.X %%R %%inst) := do
      refine ``(polynomial.nat_degree_C_mul_X _ _),
      assumption <|> exact ``(one_ne_zero)
  | `(@has_pow.pow (@polynomial %%R %%nin) %%N %%inst %%mX %%n) := do
      nontriviality_by_assumption R,
      refine ``(polynomial.nat_degree_C_mul_X_pow %%n _ _),
      assumption <|> exact ``(one_ne_zero)
  | _ := trace "The leading term is not of the form\n`C a * X (^ n)`\n\n"
  end
| _ := fail "The leading term is not of the form\n`C a * X (^ n)`\n\n"

--    nontriviality_by_assumption R,
/--  Let `e` be an expression.  Assume that `e` is either a pure `X`-power or `C a` times a pure
`X`-power in a polynomial ring over `R`.
`single_term_resolve e` produces a proof of the goal `e.nat_degree = d`, where `d` is the
exponent of `X`.

Assumptions: either there is an assumption in context asserting that the constant in front of the
power of `X` is non-zero, or the tactic `nontriviality R` succeeds. -/
meta def single_term_resolve (e : expr) : tactic unit :=
  match e.app_fn with
  | `(coe_fn $ @polynomial.monomial %%R %%inst %%n) := do
      refine ``(polynomial.nat_degree_monomial_eq %%n _),
      assumption <|> exact ``(one_ne_zero)
  | `(coe_fn $ @polynomial.C %%R %%inst) := do
      exact ``(polynomial.nat_degree_C _)
  | a := do C_mul_terms e <|>  -- either `e` is `C a * (X ^ n)` and `C_mul_terms e` handles it or
    match e with
    | `(@has_pow.pow (@polynomial %%R %%nin) %%N %%inst %%mX %%n) := do
        nontriviality_by_assumption R,
        refine ``(polynomial.nat_degree_X_pow %%n)
    | `(@polynomial.X %%R %%inst) := do
      nontriviality_by_assumption R,
      exact ``(polynomial.nat_degree_X)
    | _ := tactic.trace "The leading term is not of the form\n`C a * X (^ n)`\n\n"
    --"`compute_deg` failed to compute the degree of the leading term\n\n"
    end
  end

/--  Given an expression `e`, assuming it is a polyomial, `extract_deg_single_term e` tries to guess
the `nat_degree` of `e`.  Currently, it supports:
* `monomial n r`, guessing `n`,
* `C a`, guessing `0`,
* `polynomial.X`, guessing `1`,
* `X ^ n`, guessing `n`,
* everything else, guessing `e.nat_degree`.

The expectation is that the argument of `extract_deg_single_term` is a factor of a summand of an
expression in a polynomial ring. -/
meta def extract_deg_single_term : expr → tactic expr
| `(polynomial.X) := to_expr ``(1)
| e := match e.app_fn with
  | `(coe_fn $ polynomial.monomial %%n) := return n
  | `(coe_fn $ polynomial.C) := to_expr ``(0)
  | a := do e.get_app_args.nth 4 >>= return <|>
         do val ← to_expr ``(polynomial.nat_degree),
           return $ expr.mk_app val [e]
  end

/--  `extract_deg_single_summand e` takes apart "factors" in the expression `e` and returns them
as sums of their "guessed degrees", via `extract_deg_single_term`.  When applied to an expression
that is a summand in a polynomial, it should correctly guess its `nat_degree`. -/
meta def extract_deg_single_summand : expr → tactic expr
| `(has_mul.mul %%a %%b) := do
                              ga ← extract_deg_single_summand a,
                              gb ← extract_deg_single_summand b,
                              mk_app `has_add.add [ga, gb] >>= return
| e := extract_deg_single_term e >>= return

/-- `extract_top_degree_term_and_deg e` takes an expression `e` looks for summands in `e`
(assuming the Type of `e` is `R[X]`), and produces the pairs `(e',deg)`, where `e'` is
a summand of `e` of maximal guessed degree equal to `deg`.

The tactic fails if `e` contains no summand (this probably means something else went wrong
somewhere else). -/
meta def extract_top_degree_term_and_deg (e : expr) : tactic (expr × ℕ) :=
let summ := get_summands e in
do nat_degs ← summ.mmap extract_deg_single_summand,
  eval_nat_degs ← nat_degs.mmap (eval_expr ℕ) <|>
    tactic.fail "Only closed naturals are supported in exponents\n\n",
  let summ_and_degs := summ.zip eval_nat_degs in
  match summ_and_degs.argmax (λ e : expr × ℕ, e.2) with
  | none := tactic.fail
      "'`compute_degree`' could not find summands: something has gone very wrong!\n\n"
  | (some first) := return first
  end

/--  `compute_degree_le` tries to solve a goal of the form `f.nat_degree ≤ d`, where `d : ℕ` and `f`
satisfies:
* `f` is a sum of expression of the form
  `C a * X ^ n, C a * X, C a, X ^ n, X, monomial n a, monomial n a * monomial m b`,
* all exponents and the `n` in `monomial n a` are *closed* terms of type `ℕ`.

If the given degree is smaller than the one that the tactic computes,
then the tactic suggests the degree that it computed.

The tactic also reports when it is used with non-closed natural numbers as exponents. -/
meta def compute_degree_le : tactic unit :=
--Should be written to stay in meta-mode.
do repeat (refine ``((polynomial.nat_degree_add_le_iff_left rfl.le _ _ _).mpr _)),
  `[repeat { rw polynomial.monomial_mul_monomial }],
  try (any_goals' (refine ``(polynomial.nat_degree_monomial_le _ _  ))),
  repeat (refine ``((polynomial.nat_degree_C_mul_le _ _).trans _)),
  repeat (refine ``(polynomial.nat_degree_X_pow_le _)),
  repeat (refine ``(polynomial.nat_degree_X_le.trans _)),
  `[try {any_goals { norm_num } }] <|>
do `(polynomial.nat_degree %%tl ≤ %%tr) ← target,
  (lead,m') ← extract_top_degree_term_and_deg tl,
  td ← eval_expr ℕ tr,trace td, trace m',
  if td < m' then tactic.fail format!"should the degree bound be '{m'}'?\n\n" else
  tactic.fail "sorry, the tactic failed."

/--  These are the cases in which an easy lemma computes the degree. -/
meta def single_term_suggestions : tactic unit :=
do exact ``(polynomial.nat_degree_X_pow _)  *> trace "Try this: exact nat_degree_X_pow _" <|>
   exact ``(polynomial.nat_degree_C _)      *> trace "Try this: exact nat_degree_C _"     <|>
   exact ``(polynomial.nat_degree_X)      *> trace "Try this: exact nat_degree_X"       <|>
   fail "easy lemmas do not work"

/--  `compute_degree` tries to solve a goal of the form `f.nat_degree = d`, where `d : ℕ` and `f`
satisfies:
* `f` is a sum of expression of the form
  `C a * X ^ n, C a * X, C a, X ^ n, X, monomial n a, monomial n a * monomial m b`;
* all exponents and the `n` in `monomial n a` are *closed* terms of type `ℕ`,
* the term with largest exponent is `C a * X ^ n, X ^ n, C a * X, X, C a` and is the unique term of
  its degree (repetitions are allowed in terms of smaller degree);
* if the leading term involves a product with `C a`, there must be in context the assumption
  `a ≠ 0`.

If the given degree does not match what the tactic computes,
then the tactic suggests the degree that it computed.

The tactic also reports when it is used with non-closed natural numbers as exponents. -/
meta def compute_degree : tactic unit :=
single_term_suggestions <|>
do `(polynomial.nat_degree %%tl = %%tr) ← target,
  (lead,m') ← extract_top_degree_term_and_deg tl,
  td ← eval_expr ℕ tr,
  if m' ≠ td then tactic.fail format!"should the degree be '{m'}'?\n\n" else
  move_add_with_errors [(ff, pexpr.of_expr lead)] none,
    refine ``(polynomial.nat_degree_add_left_succ _ %%lead _ _ _),
    single_term_resolve lead,
    compute_degree_le

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree],
  tags := ["arithmetic"] }

add_tactic_doc
{ name := "compute_degree",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree],
  tags := ["arithmetic, finishing"] }

end tactic.interactive
