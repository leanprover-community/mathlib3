/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.move_add
import data.polynomial.degree.lemmas

/-! # `compute_degree, compute_degree_le` tactics for computing degrees of polynomials

This file defines two main tactics `compute_degree` and `compute_degree_le`.
Applied when the goal is of the form `f.(nat_)degree = d` or `f.(nat_)degree ≤ d`, they try to
solve it.
They may leave side-goals, in case they are not entirely successful.

See the corresponding doc-strings for more details.

##  Future work

* Add better functionality to deal with exponents that are not necessarily closed natural numbers.
* It may not be hard to allow an optional argument to be passed to `compute_degree` that would
  let the tactic know which ones are the terms of highest degree.  This would bypass the step
  where the exponents get sorted and may make it accessible to continue with the rest of the
  argument with minimal change.
* Add functionality to close `monic` goals and compute `leading_coeff`s.
* Add support for proving goals of the from `f.(nat_)degree ≠ 0`.
* Make sure that `degree` and `nat_degree` are equally supported.

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
This happens in `extract_top_degree_terms_and_deg`.

Now, `compute_degree_le` chains together a few lemmas to conclude.  It guesses that the degree of a
sum of terms is at most the degree of each individual term.
We start with a goal of the form `f.nat_degree ≤ d`.  Recurse into `f` breaking apart sums and
products.  Take care of numerals, `C a, X (^ n), monomial a n` separately.

_Heuristic:_ the terms of "apparent" highest degree do not cancel.

Finally, `compute_degree` takes one extra step.  It isolates the term of highest guessed degree
and assumes that all remaining terms have smaller degree.  It checks that the degree of the highest
term is what it is claimed (and further assumes that the highest term is a pure `X`-power, `X ^ n`,
a pure `X` term or a product of one of these by `C a` and checks that the assumption `a ≠ 0` is in
context).
`compute_degree` then outsources the rest of the computation to `compute_degree_le`, once the goal
has been appropriately replaced.

###  Error reporting
The tactics report that
* naturals involving variables are not allowed in exponents for `compute_deg`;
* when a simple lemma application would have sufficed (via a `Try this: ...`);
* when the guessed degree is incompatible with the goal, suggesting a sharper value.
-/

namespace polynomial
variables {R : Type*} [semiring R] (a : polynomial R)

/-- Useful to expose easy hypotheses:
* `df` should be dealt with by `single_term_resolve`,
* `dg` should be dealt with by `compute_degree_le`.
-/
lemma nat_degree_add_left_succ (n : ℕ) (f g : polynomial R)
  (df : f.nat_degree = n.succ) (dg : g.nat_degree ≤ n) :
  (f + g).nat_degree = n.succ :=
by rwa nat_degree_add_eq_left_of_nat_degree_lt (dg.trans_lt (nat.lt_of_succ_le df.ge))

lemma nat_degree_add_right_succ (n : ℕ) (f g : polynomial R)
  (df : f.nat_degree ≤ n) (dg : g.nat_degree = n.succ) :
  (f + g).nat_degree = n.succ :=
by rwa nat_degree_add_eq_right_of_nat_degree_lt (df.trans_lt (nat.lt_of_succ_le dg.ge))

lemma monic_of_le_of_coeff_eq_one [nontrivial R] {n : ℕ} {f : polynomial R}
  (fn : f.nat_degree ≤ n) (f0 : f.coeff n = 1) :
  f.monic :=
by rw [monic, ← f0, leading_coeff,
       nat_degree_eq_of_le_of_coeff_ne_zero fn (λ h, (one_ne_zero (f0.symm.trans h)))]

lemma coeff_C_eq_zero_of_succ (n : ℕ) (a : R) :
  (C a).coeff (n + 1) = 0 :=
by simp [coeff_C]

lemma nat_degree_eq_iff_le_and_coeff_ne_zero {n : ℕ} (n0 : n ≠ 0) (f : polynomial R) :
  f.nat_degree = n ↔ f.nat_degree ≤ n ∧ f.coeff n ≠ 0 :=
begin
  refine ⟨_, λ ⟨fn, f0⟩, nat_degree_eq_of_le_of_coeff_ne_zero fn f0⟩,
  rintro rfl,
  exact ⟨rfl.le, leading_coeff_ne_zero.mpr (ne_zero_of_nat_degree_gt (nat.pos_of_ne_zero n0))⟩,
end

end polynomial

namespace tactic
namespace compute_degree
open expr polynomial

/--  If an expression `e` is an iterated suquence of `bit0` and `bit1` starting from `0` or `1`,
then `num_to_nat e` returns `some n`, where `n` is the natural number obtained from the same
sequence of `bit0` and `bit1` applied to `0` or `1`.  Otherwise, `num_to_nat e = none`. -/
-- for the application, the line `| `(has_zero.zero) := some 0` step is unnecessary: the standard
-- assumption is that the coefficient of the term of highest-looking term is non-zero.
meta def num_to_nat : expr → option ℕ
| `(has_zero.zero) := some 0
| `(has_one.one)   := some 1
| `(bit0 %%a)      := bit0 <$> num_to_nat a
| `(bit1 %%a)      := bit1 <$> num_to_nat a
| `(%%a + %%b)     := (+) <$> num_to_nat a <*> num_to_nat b
| `(%%a * %%b)     := (*) <$> num_to_nat a <*> num_to_nat b
| `(%%a ^ %%b)     := (^) <$> num_to_nat a <*> num_to_nat b
| _ := none

/--  `convert_num_to_C_num a` takes an expression `a`, assuming that it is a term in a polynomial
ring `R[X]`.  If `a` is an iterated application of `bit0` and `bit1` to `0` or `1`, then
`convert_num_to_C_num` produces a proof of the equality
`a = C (a : R)` and rewrites the goal with this identity.  Otherwise, the tactic does nothing. -/
meta def convert_num_to_C_num (a : expr) : tactic unit :=
match num_to_nat a with
| (some an) := do
  `(@polynomial %%R %%inst) ← infer_type a,
  aexp ← to_expr ``(%%`(an)) tt ff,
  n_eq_Cn ← to_expr ``(%%a = C (%%aexp : %%R)),
  (_, nproof) ← solve_aux n_eq_Cn
    -- the reason to use `simp + norm_num` is to speed-up and avoid timeouts.  `norm_num` would
    -- be enough, but then some of the tests time out.
    `[ simp only [nat.cast_bit1, nat.cast_bit0, nat.cast_one, C_bit1, C_bit0, map_one, nat.cast_add,
         nat.cast_pow, nat.cast_mul, map_add, map_pow, map_mul, C_bit0, map_one]; norm_num
     ],
  rewrite_target nproof
| none := skip
end

/--  Let `e` be an expression.  Assume that `e` is
* `C a * X (^ n)`,
* `num * X (^ n)`, where `num` is a sequence of `bit0` and `bit1` applied to `1`,
* `monomial n a`,
* `X (^ n)`,
in a polynomial ring over `R`.
`single_term_resolve e` produces a proof of the goal `e.nat_degree = d`, where `d` is the
exponent of `X`.

Assumptions: the tactic tries to discharge the proof that constant in front of the power of `X` is
non-zero using `assumption <|> ...`.
When it is needed, `single_term_resolve` produces a `nontriviality` assumption using tactic
`nontriviality R` or fails. -/
meta def single_term_resolve : tactic unit := do
`(nat_degree %%pol = %%_) ← target,
match pol with
| `(has_mul.mul %%a %%X) := do
  convert_num_to_C_num a,
    refine ``(nat_degree_C_mul_X _ _) <|>
    refine ``(nat_degree_C_mul_X_pow _ _ _) <|>
    fail "The leading term is not of the form\n`C a * X (^ n)`\n\n",
  assumption <|> interactive.exact ``(one_ne_zero) <|> skip
| (app `(⇑(monomial %%n)) x) := do
  refine ``(nat_degree_monomial_eq %%n _),
  assumption <|> interactive.exact ``(one_ne_zero) <|> skip
| (app `(⇑C) x) :=
  interactive.exact ``(nat_degree_C _)
| `(@has_pow.pow (@polynomial %%R %%_) ℕ %%_ %%_ %%_) :=
  (nontriviality_by_assumption R <|> fail format!"could not find a 'nontrivial {R}' assumption") >>
      refine ``(nat_degree_X_pow _)
| `(@X %%R %%_) :=
  (nontriviality_by_assumption R <|>
    fail format!"could not find a 'nontrivial {R}' assumption") >>
      interactive.exact ``(nat_degree_X)
| e := do ppe ← pp e,
  fail format!"'{ppe}' is not a supported term: can you change it to `C a * X (^ n)`?\n
See the docstring of `tactic.compute_degree.single_term_resolve` for more shapes. "
end

/--  `guess_degree e` assumes that `e` is an expression in a polynomial ring, and makes an attempt
at guessing the `nat_degree` of `e`.  Heuristics for `guess_degree`:
* `0, 1, C a`,      guess `0`,
* `X`,              guess `1`,
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

/-- `resolve_sum_step` assumes that the current goal is of the form `f.nat_degree ≤ d`, failing
otherwise.  It tries to make progress on the goal by reducing it to subgoals.

`resolve_sum_step` progresses into `f` if `f` is
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

/--  These are the cases in which an easy lemma computes the degree. -/
meta def single_term_suggestions : tactic unit := do
success_if_fail (interactive.exact ``(polynomial.nat_degree_X_pow _)) <|>
  fail "Try this: exact polynomial.nat_degree_X_pow _",
success_if_fail (interactive.exact ``(polynomial.nat_degree_C _)) <|>
  fail "Try this: exact polynomial.nat_degree_C _",
success_if_fail (interactive.exact ``(polynomial.nat_degree_X)) <|>
  fail "Try this: exact polynomial.nat_degree_X",
success_if_fail (interactive.exact ``(polynomial.nat_degree_C_mul_X_pow _ _ ‹_›)) <|>
  fail "Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›",
success_if_fail (interactive.exact ``(polynomial.nat_degree_C_mul_X _ ‹_›)) <|>
  fail "Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›",
skip
  --fail "'compute_degree' works better with polynomials involving more than one term\n"

/--  A simple check: `check_target_changes t` fails if `t` unifies with one of the current
goals.  I use it to make sure that the tactics are actually making progress, by feeding the target
`t`, stored before applying them. -/
meta def check_target_changes (t : expr) : tactic unit :=
do gs ← get_goals >>= list.mmap infer_type,
  (success_if_fail $ gs.mfirst $ unify t) <|> fail "Goal did not change"

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

/--  A general description of `compute_degree_le_aux` is in the doc-string of `compute_degree`.
The difference betweem the two is that `compute_degree_le_aux` makes no effort to close side-goals,
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
check_target_changes compute_degree_le_aux >> (try $ any_goals' norm_assum)

/--  A slightly better sum of a list.  It is used for lists that have length at least one. -/
meta def _root_.list.gsum (op : expr) : list expr → expr
| [] := `(0)
| [a] := a
| (a::as) := as.foldl (λ f g, op.mk_app [f,g]) a

/--  `compute_degree` tries to solve a goal of the form `f.nat_degree = d` or  `f.degree = d`,
where `d : ℕ` and `f` satisfies:
* `f` is a sum of expressions of the form
  `C a * X ^ n, C a * X, C a, X ^ n, X, monomial n a, monomial n a * monomial m b`;
* all exponents and the `n` in `monomial n a` are *closed* terms of type `ℕ`;
* the term with largest exponent is `C a * X ^ n, X ^ n, C a * X, X, C a` and is the unique term of
  its degree (repetitions are allowed in terms of smaller degree);
* if the leading term involves a product with `C a`, there must be in context the assumption
  `a ≠ 0`;
* if the goal is computing `degree`, instead of `nat_degree`, then the expected degree `d` should
  not be `⊥`.

If the given degree does not match what the tactic computes,
then the tactic suggests the degree that it computed.

You can also pass an optional argument to `compute_degree`, letting the tactic know which term is
the one of highest degree.  The syntax is `compute_degree [<expression for one term>]`.  The
expression can involve underscore, and Lean will try to unify them with one of the summands in the
goal.  This opens the possibility of working with polynomials whose exponents are not closed natural
numbers, though this is mostly unimplemented still.

The tactic also reports when it is used with non-closed natural numbers as exponents. -/
meta def compute_degree : tactic unit :=
do t ← target,
  match t with
    -- the `degree` match implicitly assumes that the `nat_degree` is strictly positive
  | `(    degree %%_ = %%_) := refine ``((degree_eq_iff_nat_degree_eq_of_pos _).mpr _) >> rotate
  | `(nat_degree %%_ = %%_) := single_term_suggestions
  | _ := fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`"
  end,
  `(nat_degree %%pol = %%degv) ← target |
    fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`",
  deg ← guess_degree pol >>= eval_guessing 0,
  degvn ← eval_guessing 0 degv,
  guard (deg = degvn) <|>
  ( do ppe ← pp deg, ppg ← pp degvn,
    fail sformat!("'{ppe}' is the expected degree\n'{ppg}' is the given degree\n") ),
  ad ← to_expr ``(has_add.add) tt ff,
  summ ← list_binary_operands ad pol,
  (lg_degs, sm_degs) ← summ.mpartition
    (λ t, do dt ← guess_degree t >>= eval_guessing 0, return (deg = dt)),
  if (sm_degs.length ≠ 0) then do
    eq_sm_add_lg ← mk_app `eq [pol, ad.mk_app [lg_degs.gsum ad, sm_degs.gsum ad]],
    (_, prf) ← solve_aux (eq_sm_add_lg) $
      reflexivity <|>
      move_op (prod.mk tt <$> sm_degs.map to_pexpr) (interactive.loc.ns [none]) (to_pexpr ad),
    rewrite_target prf,
    refine ``(nat_degree_add_left_succ _ _ _ _ _),
    rotate >> try compute_degree_le_aux
  else skip,
  gs ← get_goals,
  focus' $ gs.map (λ g : expr, do gt ← infer_type g, match gt with
    | `(nat_degree (%%_ + %%_) = %%_) := skip
    | `(nat_degree %%_ ≤ %%_) := skip
    | `(nat_degree %%_ = %%_) := single_term_resolve >> norm_assum
    |_ := try norm_assum
     end)

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree_le],
  tags := ["arithmetic", "finishing"] }

add_tactic_doc
{ name := "compute_degree",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree],
  tags := ["arithmetic, finishing"] }

end interactive

end tactic
