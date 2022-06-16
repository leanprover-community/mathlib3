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

There is also a second version `compute_degree_le!` that recurses more aggressively into powers.
If there are exponents that are not closed naturals that could be zero, then the `!`-version
could leave unsolvable side-goals.

See the doc-string for more details.

##  Future work

* Deal with goals of the form `f.(nat_)degree = d` (PR #14040 does exactly this).
* Add better functionality to deal with exponents that are not necessarily natural numbers.
* Add support for proving goals of the from `f.(nat_)degree ≠ 0`.
* Make sure that `degree` and `nat_degree` are equally supported.

##  Implementation details

We start with a goal of the form `f.nat_degree ≤ d`.  Recurse into `f` breaking apart sums and
products.  Take care of numerals, `C a, X (^ n), monomial a n` separately. -/

namespace polynomial
variables {R : Type*} [semiring R] (a : polynomial R)

lemma nat_degree_sub_le_iff_left {R : Type*} [ring R] {n : ℕ} (p q : polynomial R)
  (qn : q.nat_degree ≤ n) :
  (p - q).nat_degree ≤ n ↔ p.nat_degree ≤ n :=
begin
  rw [sub_eq_add_neg, nat_degree_add_le_iff_left],
  rwa nat_degree_neg,
end

lemma nat_degree_bit0 : (bit0 a).nat_degree ≤ a.nat_degree :=
(nat_degree_add_le _ _).trans (by simp)

lemma nat_degree_bit1 : (bit1 a).nat_degree ≤ a.nat_degree :=
(nat_degree_add_le _ _).trans (by simp [nat_degree_bit0])

end polynomial

namespace tactic
namespace compute_degree
open expr

/--  `guess_degree e` assumes that `e` is an expression in a polynomial ring, and makes an attempt
at guessing the degree of `e`.  Heuristics for `guess_degree`:
* `0, 1`,            guessing `0`,
* `C a`,             guessing `0`,
* `polynomial.X`,    guessing `1`,
*  `bit0 f, bit1 f`, guessing `guess_degree f`,
                              (this could give wrong results, e.g. `bit0 f = 0` if the
                               characteristic of the ground ring is `2`),
* `f + g`,           guessing `max (guess_degree f) (guess_degree g)`,
* `f * g`,           guessing `guess_degree f + guess_degree g`,
* `f ^ n`,           guessing `guess_degree f * n`,
* `monomial n r`,    guessing `n`,
* `f` not as above,  guessing `f.nat_degree`.
 -/
meta def guess_degree : expr → tactic expr
| `(has_zero.zero)         := pure `(0)
| `(has_one.one)           := pure `(0)
| `(- %%f)                 := guess_degree f
| (app `(⇑polynomial.C) x) := pure `(0)
| `(polynomial.X)          := pure `(1)
| `(bit0 %%a)              := guess_degree a
| `(bit1 %%a)              := guess_degree a
| `(%%a + %%b)             := do da ← guess_degree a, db ← guess_degree b,
                              pure $ expr.mk_app `(max : ℕ → ℕ → ℕ) [da, db]
| `(%%a - %%b)             := do da ← guess_degree a, db ← guess_degree b,
                              pure $ expr.mk_app `(max : ℕ → ℕ → ℕ) [da, db]
| `(%%a * %%b)             := do da ← guess_degree a, db ← guess_degree b,
                              pure $ expr.mk_app `((+) : ℕ → ℕ → ℕ) [da, db]
| `(%%a ^ %%b)             := do da ← guess_degree a,
                              pure $ expr.mk_app `((*) : ℕ → ℕ → ℕ) [da, b]
| (app `(⇑(polynomial.monomial %%n)) x) := pure n
| e                        := do `(@polynomial %%R %%inst) ← infer_type e,
                              pe ← to_expr ``(polynomial.nat_degree) tt ff,
                              pure $ expr.mk_app pe [e]

/--  `resolve_sum_step tf e` takes a boolean `tf` and an expression `e` as inputs.
It assumes that `e` is of the form `f.nat_degree ≤ d`,failing otherwise.
`resolve_sum_step` progresses into `f` if `f` is
*  a sum, difference, opposite or product;
* (a power of) `X`;
* a monomial;
* `C a`;
* `0, 1` or `bit0 a, bit1 a` (to deal with numerals);

The boolean `tf` determines whether `resolve_sum_step` aggressively simplifies powers.
If `tf` is `false`, then `resolve_sum_step` will fail on powers other than `X ^ n`.

If `tf` is `true`, then `resolve_sum_step` tries to make progress on powers.
Use it only if you know how to prove that exponents of terms other than `X ^ ??` are non-zero!

The side-goals produced by `resolve_sum_step` are either again of the same shape `f'.nat_degree ≤ d`
or of the form `m ≤ n`, where `m n : ℕ`, or, if `tf = true`, also of the form `0 < m`. -/
meta def resolve_sum_step (pows : bool) : expr → tactic unit
| `(polynomial.nat_degree %%tl ≤ %%tr) := match tl with
  | `(%%tl1 + %%tl2) := do
      refine ``((polynomial.nat_degree_add_le_iff_left _ _ _).mpr _)
  | `(%%tl1 - %%tl2) := do
      refine ``((polynomial.nat_degree_sub_le_iff_left _ _ _).mpr _)
  | `(%%tl1 * %%tl2) := do
    d1 ← guess_degree tl1,
    d2 ← guess_degree tl2,
    refine ``(polynomial.nat_degree_mul_le.trans ((add_le_add _ _).trans (_ : %%d1 + %%d2 ≤ %%tr)))
  | `(- %%f) := do
    refine ``((polynomial.nat_degree_neg _).le.trans _)
  | `(polynomial.X ^ %%n) :=
    refine ``((polynomial.nat_degree_X_pow_le %%n).trans _)
  | (app `(⇑(@polynomial.monomial %%R %%inst %%n)) x) :=
    refine ``((polynomial.nat_degree_monomial_le %%x).trans _)
  | (app `(⇑polynomial.C) x) :=
    interactive.exact ``((polynomial.nat_degree_C _).le.trans (nat.zero_le _))
  | `(polynomial.X) :=
    refine ``(polynomial.nat_degree_X_le.trans _)
  | `(has_zero.zero) := do
    refine ``(polynomial.nat_degree_zero.le.trans (nat.zero_le _))
  | `(has_one.one)   := do
    refine ``(polynomial.nat_degree_one.le.trans (nat.zero_le _))
  | `(bit0 %%a)      := do
    refine ``((polynomial.nat_degree_bit0 %%a).trans _)
  | `(bit1 %%a)      := do
    refine ``((polynomial.nat_degree_bit1 %%a).trans _)
  | `(%%tl1 ^ %%n)   :=
    if pows then do
      refine ``(polynomial.nat_degree_pow_le.trans $
        (mul_comm _ _).le.trans ((nat.le_div_iff_mul_le' _).mp _))
    else failed
  | e                := do ppe ← pp e, fail format!"'{e}' is not supported"
  end
| e := do ppe ← pp e, fail format!("'resolve_sum_step' was called on\n" ++
  "{ppe}\nbut it expects `f.nat_degree ≤ d`")

/--  `norm_assum` simply tries `norm_num, apply_instance` and `assumption`.
It is used to try to discharge as many as possible of the side-goals of `compute_degree_le`.
Several side-goals are of the form `m ≤ n`, for natural numbers `m, n` or of the form `a ≠ 0`
with `a` is a coefficient of the polynomial `f` in question. -/
meta def norm_assum : tactic unit :=
try `[ norm_num <|> apply_instance ] >> try assumption

/--  `eval_guessing n e` takes a natural number `n` and an expression `e` and gives an
estimate for the evaluation of `eval_expr ℕ e`.  It is tailor made for estimating degrees of
polynomials.

It decomposes `e` recursively as a sequence of additions, multiplications and `max`.
On the atoms of the process, `eval_guessing` tries to use `eval_expr ℕ`, resorting to using
`n` if `eval_expr ℕ` fails.

For use with degree of polynomials, we mostly use `n = 0`. -/
meta def eval_guessing (n : ℕ) : expr → tactic ℕ
| `(%%a + %%b)   := do ca ← eval_guessing a, cb ← eval_guessing b, return $ ca + cb
| `(%%a * %%b)   := do ca ← eval_guessing a, cb ← eval_guessing b, return $ ca * cb
| `(max %%a %%b) := do ca ← eval_guessing a, cb ← eval_guessing b, return $ max ca cb
| e := do cond ← succeeds $ eval_expr ℕ e, if cond then eval_expr ℕ e else pure n

end compute_degree

namespace interactive
open compute_degree
setup_tactic_parser

/--  `compute_degree_le` tries to solve a goal of the form `f.nat_degree ≤ d` or  `f.degree ≤ d`,
where `d : ℕ` or `d : with_bot ℕ` and `f : R[X]`.

If the given degree `d` is smaller than the one that the tactic computes,
then the tactic suggests the degree that it computed.

Using `compute_degree_le!` also recurses inside powers.
Use it only if you know how to prove that exponents of terms other than `X ^ ??` are non-zero!
 -/
meta def compute_degree_le (expos : parse (tk "!" )?) : tactic unit :=
do t ← target,
  try $ refine ``(polynomial.degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr _)),
  `(polynomial.nat_degree %%tl ≤ %%tr) ← target |
    fail "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`",
  exp_deg ← guess_degree tl >>= eval_guessing 0,
  cond ← succeeds $ eval_expr ℕ tr,
  deg_bou ← if cond then eval_expr ℕ tr else pure exp_deg,
  if deg_bou < exp_deg
  then fail sformat!"the given polynomial has a term of expected degree\nat least '{exp_deg}'"
  else
    repeat $ target >>= resolve_sum_step (if expos.is_some then tt else ff),
    gs ← get_goals,
    os ← gs.mmap infer_type >>= list.mfilter (λ e, succeeds $ unify t e),
    guard (os.length = 0) <|> fail "Goal did not change",
    try $ any_goals' norm_assum

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree_le],
  tags := ["arithmetic, finishing"] }

end interactive

end tactic
