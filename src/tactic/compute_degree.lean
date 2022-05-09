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

See the corresponding doc-strings for more details. -/

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

lemma nat_degree_add_le_of {m n : ℕ} (mn : m ≤ n) (f g : R[X]) (gm : g.nat_degree ≤ m) :
  (f + g).nat_degree ≤ n ↔ f.nat_degree ≤ n :=
begin
  by_cases fm : f.nat_degree ≤ m,
  { refine ⟨λ h, fm.trans mn, λ fn, _⟩,
    refine (nat_degree_add_le _ _).trans (max_le fn (gm.trans mn)) },
  { rw nat_degree_add_eq_left_of_nat_degree_lt,
    exact gm.trans_lt (not_le.mp fm) }
end

end polynomial

namespace tactic.interactive
open tactic
setup_tactic_parser

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

/--  These are the cases in which an easy lemma computes the degree. -/
meta def single_term_suggestions : tactic unit :=
do `[ exact nat_degree_X_pow _ ] *> trace "Try this: exact nat_degree_X_pow _" <|>
   `[ exact nat_degree_C _ ]     *> trace "Try this: exact nat_degree_C _"     <|>
   `[ exact nat_degree_X ]       *> trace "Try this: exact nat_degree_X"       <|>
   fail "easy lemmas do not work"

/--  `compute_degree_le` tries to solve a goal of the form `f.nat_degree ≤ d`, where `d : ℕ` and `f`
satisfies:
* `f` is a sum of expression of the form
  `C a * X ^ n, C a * X, C a, X ^ n, X, monomial n a, monomial n a * monomial m b`,
* all exponents and the `n` in `monomial n a` are *closed* terms of type `ℕ`.

If the given degree is smaller than the one that the tactic computes,
then the tactic suggests the degree that it computed.

The tactic also reports when it is used with non-closed natural numbers as exponents. -/
meta def compute_degree_le : tactic unit :=
`[repeat { refine (polynomial.nat_degree_add_le_of rfl.le _ _ _).mpr _ },
  repeat { rw polynomial.monomial_mul_monomial },
  try { any_goals { refine polynomial.nat_degree_monomial_le _ _  } },
  try { any_goals { refine (polynomial.nat_degree_C_mul_le _ _).trans _ } },
  try { any_goals { norm_num } },
  all_goals { refl } ] <|>
do `(polynomial.nat_degree %%tl ≤ %%tr) ← target,
  (lead,m') ← extract_top_degree_term_and_deg tl,
  td ← eval_expr ℕ tr,
  if td < m' then tactic.fail format!"should the degree bound be '{m'}'?\n\n" else
  tactic.fail "sorry, the tactic failed."

/--  `compute_degree` tries to solve a goal of the form `f.nat_degree = d`, where `d : ℕ` and `f`
satisfies:
* `f` is a sum of expression of the form
  `C a * X ^ n, C a * X, C a, X ^ n, X, monomial n a, monomial n a * monomial m b`,
* all exponents and the `n` in `monomial n a` are *closed* terms of type `ℕ`,
* the term with largest exponent is `X ^ n` and is the unique term of its degree (repetitions are
  allowed in terms of smaller degree).

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
  `[rw [polynomial.nat_degree_add_eq_right_of_nat_degree_lt, polynomial.nat_degree_X_pow],
    rw [polynomial.nat_degree_X_pow],
    refine nat.lt_succ_of_le _ ],
  compute_degree_le


end tactic.interactive
