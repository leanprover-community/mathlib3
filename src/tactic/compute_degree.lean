/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.lemmas

/-! # `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `f.nat_degree ≤ d`, tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with goals of the form `f.(nat_)degree = d` (PR #14040 does exactly this).
* Add better functionality to deal with exponents that are not necessarily closed natural numbers.
* Add support for proving goals of the from `f.(nat_)degree ≠ 0`.
* Make sure that `degree` and `nat_degree` are equally supported.

##  Implementation details

We start with a goal of the form `f.(nat_)degree ≤ d`.  Recurse into `f` breaking apart sums,
products and powers.  Take care of numerals, `C a, X (^ n), monomial a n` separately. -/

namespace tactic
namespace compute_degree
open expr polynomial

/--  `guess_degree e` assumes that `e` is an expression in a polynomial ring, and makes an attempt
at guessing the `nat_degree` of `e`.  Heuristics for `guess_degree`:
* `0, 1, C a`,      guess `0`,
* `polynomial.X`,   guess `1`,
*  `bit0/1 f, -f`,  guess `guess_degree f`,
* `f + g, f - g`,   guess `max (guess_degree f) (guess_degree g)`,
* `f * g`,          guess `guess_degree f + guess_degree g`,
* `f ^ n`,          guess `guess_degree f * n`,
* `monomial n r`,   guess `n`,
* `f` not as above, guess `f.nat_degree`.

The guessed degree should coincide with the behaviour of `resolve_sum_step`:
`resolve_sum_step` cannot solve a goal `f.nat_degree ≤ d` if `guess_degree f < d`.
 -/
meta def guess_degree : expr → tactic expr
| `(has_zero.zero)           := pure `(0)
| `(has_one.one)             := pure `(0)
| `(- %%f)                   := guess_degree f
| (app `(⇑C) x)              := pure `(0)
| `(X)                       := pure `(1)
| `(bit0 %%a)                := guess_degree a
| `(bit1 %%a)                := guess_degree a
| `(%%a + %%b)               := do [da, db] ← [a, b].mmap guess_degree,
                                pure $ expr.mk_app `(max : ℕ → ℕ → ℕ) [da, db]
| `(%%a - %%b)               := do [da, db] ← [a, b].mmap guess_degree,
                                pure $ expr.mk_app `(max : ℕ → ℕ → ℕ) [da, db]
| `(%%a * %%b)               := do [da, db] ← [a, b].mmap guess_degree,
                                pure $ expr.mk_app `((+) : ℕ → ℕ → ℕ) [da, db]
| `(%%a ^ %%b)               := do da ← guess_degree a,
                                pure $ expr.mk_app `((*) : ℕ → ℕ → ℕ) [da, b]
| (app `(⇑(monomial %%n)) x) := pure n
| e                          := do `(@polynomial %%R %%inst) ← infer_type e,
                                pe ← to_expr ``(@nat_degree %%R %%inst) tt ff,
                                pure $ expr.mk_app pe [e]

/-- `resolve_sum_step` assumes that the current goal is of the form `f.nat_degree ≤ d`, failing
otherwise.  It tries to make progress on the goal by progressing into `f` if `f` is
* a sum, difference, opposite, product, or a power;
* a monomial;
* `C a`;
* `0, 1` or `bit0 a, bit1 a` (to deal with numerals).

The side-goals produced by `resolve_sum_step` are either again of the same shape `f'.nat_degree ≤ d`
or of the form `m ≤ n`, where `m n : ℕ`.

If `d` is less than `guess_degree f`, this tactic will create unsolvable goals.
-/
meta def resolve_sum_step : tactic unit := do
t ← target >>= instantiate_mvars,
`(nat_degree %%tl ≤ %%tr) ← whnf t reducible | fail!("Goal is not of the form `f.nat_degree ≤ d`"),
match tl with
| `(%%tl1 + %%tl2) := refine ``((nat_degree_add_le_iff_left _ _ _).mpr _)
| `(%%tl1 - %%tl2) := refine ``((nat_degree_sub_le_iff_left _).mpr _)
| `(%%tl1 * %%tl2) := do [d1, d2] ← [tl1, tl2].mmap guess_degree,
  refine ``(nat_degree_mul_le.trans $ (add_le_add _ _).trans (_ : %%d1 + %%d2 ≤ %%tr))
| `(- %%f)         := refine ``((nat_degree_neg _).le.trans _)
| `(X ^ %%n)       := refine ``((nat_degree_X_pow_le %%n).trans _)
| (app `(⇑(@monomial %%R %%inst %%n)) x) := refine ``((nat_degree_monomial_le %%x).trans _)
| (app `(⇑C) x)    := refine ``((nat_degree_C %%x).le.trans (nat.zero_le %%tr))
| `(X)             := refine ``(nat_degree_X_le.trans _)
| `(has_zero.zero) := refine ``(nat_degree_zero.le.trans (nat.zero_le _))
| `(has_one.one)   := refine ``(nat_degree_one.le.trans (nat.zero_le _))
| `(bit0 %%a)      := refine ``((nat_degree_bit0 %%a).trans _)
| `(bit1 %%a)      := refine ``((nat_degree_bit1 %%a).trans _)
| `(%%tl1 ^ %%n)   := do
    refine ``(nat_degree_pow_le.trans _),
    refine ``(dite (%%n = 0) (λ (n0 : %%n = 0), (by simp only [n0, zero_mul, zero_le])) _),
    n0 ← get_unused_name "n0" >>= intro,
    refine ``((mul_comm _ _).le.trans ((nat.le_div_iff_mul_le' (nat.pos_of_ne_zero %%n0)).mp _)),
    lem1 ← to_expr ``(nat.mul_div_cancel _ (nat.pos_of_ne_zero %%n0)) tt ff,
    lem2 ← to_expr ``(nat.div_self (nat.pos_of_ne_zero %%n0)) tt ff,
    focus1 (refine ``((%%n0 rfl).elim) <|> rewrite_target lem1 <|> rewrite_target lem2) <|> skip
| e                := fail!"'{e}' is not supported"
end

/--  `norm_assum` simply tries `norm_num` and `assumption`.
It is used to try to discharge as many as possible of the side-goals of `compute_degree_le`.
Several side-goals are of the form `m ≤ n`, for natural numbers `m, n` or of the form `c ≠ 0`,
with `c` a coefficient of the polynomial `f` in question. -/
meta def norm_assum : tactic unit :=
try `[ norm_num ] >> try assumption

/--  `eval_guessing n e` takes a natural number `n` and an expression `e` and gives an
estimate for the evaluation of `eval_expr' ℕ e`.  It is tailor made for estimating degrees of
polynomials.

It decomposes `e` recursively as a sequence of additions, multiplications and `max`.
On the atoms of the process, `eval_guessing` tries to use `eval_expr' ℕ`, resorting to using
`n` if `eval_expr' ℕ` fails.

For use with degree of polynomials, we mostly use `n = 0`. -/
meta def eval_guessing (n : ℕ) : expr → tactic ℕ
| `(%%a + %%b)   := (+) <$> eval_guessing a <*> eval_guessing b
| `(%%a * %%b)   := (*) <$> eval_guessing a <*> eval_guessing b
| `(max %%a %%b) := max <$> eval_guessing a <*> eval_guessing b
| e              := eval_expr' ℕ e <|> pure n

/--  A general description of `compute_degree_le_aux` is in the doc-string of `compute_degree`.
The difference between the two is that `compute_degree_le_aux` makes no effort to close side-goals,
nor fails if the goal does not change. -/
meta def compute_degree_le_aux : tactic unit := do
try $ refine ``(degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr _)),
`(nat_degree %%tl ≤ %%tr) ← target |
  fail "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`",
expected_deg ← guess_degree tl >>= eval_guessing 0,
deg_bound ← eval_expr' ℕ tr <|> pure expected_deg,
if deg_bound < expected_deg
then fail sformat!"the given polynomial has a term of expected degree\nat least '{expected_deg}'"
else repeat $ resolve_sum_step

end compute_degree

namespace interactive
open compute_degree polynomial

/--  `compute_degree_le` tries to solve a goal of the form `f.nat_degree ≤ d` or `f.degree ≤ d`,
where `f : R[X]` and `d : ℕ` or `d : with_bot ℕ`.

If the given degree `d` is smaller than the one that the tactic computes,
then the tactic suggests the degree that it computed.

Examples:

```lean
open polynomial
open_locale polynomial

variables {R : Type*} [semiring R] {a b c d e : R}

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
by compute_degree_le

example : nat_degree (7 * X : R[X]) ≤ 1 :=
by compute_degree_le

example {p : R[X]} {n : ℕ} {p0 : p.nat_degree = 0} :
 (p ^ n).nat_degree ≤ 0 :=
by compute_degree_le
```
-/
meta def compute_degree_le : tactic unit :=
focus1 $ do check_target_changes compute_degree_le_aux,
  try $ any_goals' norm_assum

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree_le],
  tags := ["arithmetic", "finishing"] }

end interactive

end tactic
