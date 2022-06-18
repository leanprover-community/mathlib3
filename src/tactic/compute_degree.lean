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

There is also a version `compute_degree_le!` that recurses more aggressively into powers.
If there are exponents that are not closed naturals that could be zero, then the `!`-version
could leave unsolvable side-goals.

See the corresponding doc-strings for more details.

##  Future work

* Add better functionality to deal with exponents that are not necessarily natural numbers.
* It may not be hard to allow an optional argument to be passed to `compute_degree` that would
  let the tactic know which ones are the terms of highest degree.  This would bypass the step
  where the exponents get sorted and may make it accessible to continue with the rest of the
  argument with minimal change.
* Add functionality to close `monic` goals and compute `leading_coeff`s.
* Add support for proving goals of the from `f.nat_degree ≠ 0`.
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
  (df : f.nat_degree = n + 1) (dg : g.nat_degree ≤ n) :
  (f + g).nat_degree = n + 1 :=
by rwa nat_degree_add_eq_left_of_nat_degree_lt (dg.trans_lt (nat.lt_of_succ_le df.ge))

lemma nat_degree_add_right_succ (n : ℕ) (f g : polynomial R)
  (df : f.nat_degree ≤ n) (dg : g.nat_degree = n + 1) :
  (f + g).nat_degree = n + 1 :=
by rwa nat_degree_add_eq_right_of_nat_degree_lt (df.trans_lt (nat.lt_of_succ_le dg.ge))

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

lemma nat_degree_eq_of_le_of_coeff_ne_zero {n : ℕ} {f : polynomial R}
  (fn : f.nat_degree ≤ n) (f0 : f.coeff n ≠ 0) :
  f.nat_degree = n :=
le_antisymm fn (le_nat_degree_of_ne_zero f0)

lemma monic_of_le_of_coeff_eq_one [nontrivial R] {n : ℕ} {f : polynomial R}
  (fn : f.nat_degree ≤ n) (f0 : f.coeff n = 1) :
  f.monic :=
begin
  rw [monic, ← f0, leading_coeff],
  congr,
  refine nat_degree_eq_of_le_of_coeff_ne_zero fn (λ h, (one_ne_zero (f0.symm.trans h))),
end

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
open expr

/--  If an expression `e` is an iterated suquence of `bit0` and `bit1` starting from `0` or `1`,
then `num_to_nat e` returns `some n`, where `n` is the natural number obtained from the same
sequence of `bit0` and `bit1` applied to `0` or `1`.  Otherwise, `num_to_nat e = none`. -/
-- for the application, the line `| `(has_zero.zero) := some 0` step is unnecessary: the standard
-- assumption is that the coefficient of the term of highest-looking term is non-zero.
meta def num_to_nat : expr → option ℕ
| `(has_zero.zero) := some 0
| `(has_one.one) := some 1
| `(bit0 %%a) := match num_to_nat a with
  | some an := some (bit0 an)
  | none := none
  end
| `(bit1 %%a) := match num_to_nat a with
  | some an := some (bit1 an)
  | none := none
  end
| _ := none

/--  `convert_num_to_C_num a` takes an expression `a`, assuming that it is a term in a polynomial
ring `R[X]`.  If `a` is an iterated application of `bit0` and `bit1` to `0` or `1`, then
`convert_num_to_C_num` produces a proof of the equality
`a = C (a : R)` and rewrites the goal with this identity.  Otherwise, the tactic does nothing. -/
meta def convert_num_to_C_num (a : expr) : tactic unit :=
match num_to_nat a with
| (some an) := do
  `(@polynomial %%R %%inst) ← infer_type a,
  n_eq_Cn ← to_expr ``(%%a = polynomial.C (%%an : %%R)),
  (_, nproof) ← solve_aux n_eq_Cn
    `[ simp only [nat.cast_bit1, nat.cast_bit0, nat.cast_one, C_bit1, C_bit0, map_one] ],
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
meta def single_term_resolve : expr → tactic unit
| `(has_mul.mul %%a %%X) := do
  convert_num_to_C_num a,
  refine ``(polynomial.nat_degree_C_mul_X _ _) <|>
    refine ``(polynomial.nat_degree_C_mul_X_pow _ _ _) <|>
    fail "The leading term is not of the form\n`C a * X (^ n)`\n\n",
  assumption <|> interactive.exact ``(one_ne_zero) <|> skip
| (app `(⇑(@polynomial.monomial %%R %%inst %%n)) x) := do
  refine ``(polynomial.nat_degree_monomial_eq %%n _),
  assumption <|> interactive.exact ``(one_ne_zero) <|> skip
| (app `(⇑(@polynomial.C %%R %%inst)) x) :=
  interactive.exact ``(polynomial.nat_degree_C _)
| `(@has_pow.pow (@polynomial %%R %%nin) ℕ %%inst %%mX %%n) :=
  (nontriviality_by_assumption R <|>
    fail format!"could not produce a 'nontrivial {R}' assumption") >>
  refine ``(polynomial.nat_degree_X_pow %%n)
| `(@polynomial.X %%R %%inst) :=
  (nontriviality_by_assumption R <|>
    fail format!"could not produce a 'nontrivial {R}' assumption") >>
  interactive.exact ``(polynomial.nat_degree_X)
| e := do ppe ← pp e,
  fail format!"'{ppe}' is not a supported term: can you change it to `C a * X (^ n)`?\n
See the docstring of `tactic.compute_degree.single_term_resolve` for more shapes. "

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
                              pe ← to_expr ``(@polynomial.nat_degree %%R %%inst) tt ff,
                              pure $ expr.mk_app pe [e]

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

/--  `resolve_sum_step tf e` takes a boolean `tf` and an expression `e` as inputs.
It assumes that `e` is of the form `f.nat_degree ≤ d`,failing otherwise.
`resolve_sum_step` progresses into `f` if `f` is
*  a sum, difference, opposite or product;
* (a power of) `X`;
* a monomial;
* `C a`;
* `0, 1` or `bit0 a, bit1 a` (to deal with numerals).

The boolean `tf` determines whether `resolve_sum_step` aggressively simplifies powers.
If `tf` is `false`, then `resolve_sum_step` will fail on powers other than `X ^ n`.

If `tf` is `true`, then `resolve_sum_step` tries to make progress on powers.
Use it only if you know how to prove that exponents of terms other than `X ^ ??` are non-zero!

The side-goals produced by `resolve_sum_step` are either again of the same shape `f'.nat_degree ≤ d`
or of the form `m ≤ n`, where `m n : ℕ`, or, if `tf = true`, also of the form `0 < m`. -/
meta def resolve_sum_step (pows : bool) : expr → tactic unit
| `(polynomial.nat_degree %%tl ≤ %%tr) := do `(@polynomial %%R %%inst) ← infer_type tl,
  match tl with
  | `(%%tl1 + %%tl2) := do
      refine ``((polynomial.nat_degree_add_le_iff_left (%%tl1 : polynomial %%R) (%%tl2 : polynomial %%R) _).mpr _)
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
  | e                := do ppe ← pp e, fail format!"'{ppe}' is not supported"
  end
| e := do ppe ← pp e, fail format!("'resolve_sum_step' was called on\n" ++
  "{ppe}\nbut it expects `f.nat_degree ≤ d`")

/--  `norm_assum` simply tries `norm_num` and `assumption`.
It is used to try to discharge as many as possible of the side-goals of `compute_degree_le`.
Several side-goals are of the form `m ≤ n`, for natural numbers `m, n` or of the form `c ≠ 0`,
with `c` a coefficient of the polynomial `f` in question. -/
meta def norm_assum : tactic unit :=
try `[ norm_num ] >> try assumption

meta def compute_step (deg : ℕ) : expr → tactic unit
| `(%%l + %%r) := do [dle, dre] ← [l, r].mmap guess_degree,
  [dl, dr] ← [dle, dre].mmap $ eval_guessing 0,
  if dr < deg then do
    refine ``(polynomial.nat_degree_add_left_succ _ %%l %%r _ _)
  else
  if dl < deg then do
    refine ``(polynomial.nat_degree_add_right_succ _ %%l %%r _ _)
  else
    fail "sorry, there are two or more terms of highest expected degree"
| _ := failed

/--  These are the cases in which an easy lemma computes the degree. -/
meta def single_term_suggestions : tactic unit := do
bo ← succeeds $ interactive.exact ``(polynomial.nat_degree_X_pow _),
if bo then fail "Try this: exact polynomial.nat_degree_X_pow _"
else do
bo ← succeeds $ interactive.exact ``(polynomial.nat_degree_C _),
if bo then fail "Try this: exact polynomial.nat_degree_C _"
else do
bo ← succeeds $ interactive.exact ``(polynomial.nat_degree_X),
if bo then fail "Try this: exact polynomial.nat_degree_X"
else do
bo ← succeeds $ interactive.exact ``(polynomial.nat_degree_C_mul_X_pow _ _ ‹_›),
if bo then fail "Try this: exact polynomial.nat_degree_C_mul_X_pow _ _ ‹_›"
else do
bo ← succeeds $ interactive.exact ``(polynomial.nat_degree_C_mul_X _ ‹_›),
if bo then fail "Try this: exact polynomial.nat_degree_C_mul_X _ ‹_›"
else
  skip
  --fail "'compute_degree' works better with polynomials involving more than one term\n"

/--  A simple check: `check_target_changes t` changes if `t` unifies with one of the current
goals.  I use it to make sure that the tactics are actually making progress, by feeding the target
`t`, stored before applying them. -/
meta def check_target_changes (t : expr) : tactic unit :=
do gs ← get_goals,
  os ← gs.mmap infer_type >>= list.mfilter (λ e, succeeds $ unify t e),
  guard (os.length = 0) <|> fail "Goal did not change"

/--  `compute_degree_le_core` differs from `compute_degree_le` simply since it takes a `bool`
input, instead of parsing a `!` token. -/
meta def compute_degree_le_core (expos : bool) : tactic unit :=
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
    repeat $ target >>= resolve_sum_step expos,
  check_target_changes t,
  try $ any_goals' norm_assum

meta def remove_one_coeff (fc : expr) : tactic unit :=
do n ← get_unused_name "h",
  R ← infer_type fc,
  zer ← to_expr ``(0 : %%R) tt ff,
  --az ← to_expr ``(add_zero (_ : %%R)) tt ff,
  --za ← to_expr ``(zero_add (_ : %%R)) tt ff,
  c0 ← mk_app `eq [fc, zer],
  hc0 ← assert n c0,
  refine ``(polynomial.coeff_eq_zero_of_nat_degree_lt (nat.lt_succ_of_le _)),
  focus1 (compute_degree_le_core ff),
  interactive.rotate,
  try $ rewrite_target hc0,
  clear hc0
  --,
  --rewrite_target az <|> rewrite_target za

meta def progressively_remove : tactic unit :=
do `(%%a + %%b ≠ 0) ← target,
  match b with
  | `(polynomial.coeff %%pol %%n) := do de ← guess_degree pol, d ← eval_guessing 0 de,
    nn ← eval_expr ℕ n,
    if d < nn then
      compute_degree.remove_one_coeff b
    else skip
  | _ := skip
  end

--  trace mapps,
--  apps ← summ.mfilter (λ e : expr,
--    do `(some %%arg) ← e.get_app_args.nth 3, darg ← guess_degree arg,
--    narg ← eval_guessing 0 darg, return $ narg < 9 ),
--  trace apps,
--  trace "summ",summ.mmap (λ e : expr, e.get_app_fn) >>= trace,
----  let small_deg := summ.mfilter
----    (λ e : expr, let co:= e.get_fn_app in de ← guess_degree d, nd ← eval_guessing 0 de,
----      return (nd < tar_deg : bool)),
--    trace "*****************************",
--    trace small_deg,
--  (ne::rest) ← summ.mfilter
--    (λ e, do de ← guess_degree e, nd ← eval_guessing 0 de, return (nd < tar_deg : bool)) | trace "nonono",
--    trace ne,
--  remove_one_coeff ne
--  trace small_deg,
--  gd ← summ.mmap guess_degree,
--  nat_degs ← gd.mmap $ eval_guessing 0,trace nat_degs
--  summands ← list_binary_operands
--  lids ←


meta def compute_degree_core (expos : bool) : tactic unit :=
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
    repeat $ target >>= resolve_sum_step expos,
  check_target_changes t
    --,
    --try $ any_goals' norm_assum

/-- `extract_top_degree_terms_and_deg e` takes an expression `e` looks for summands in `e`
(assuming the Type of `e` is `R[X]`), and produces the pairs `(e',deg)`, where `e'` is
the list of summands of `e` of maximal guessed degree equal to `deg`.

The tactic fails if `e` contains no summand (this probably means something else went wrong
somewhere else). -/
meta def extract_top_degree_terms_and_deg (e : expr) : tactic (list expr × ℕ) :=
do te ← infer_type e,
  ad ← to_expr ``((+) : %%te → %%te → %%te) tt ff,
  summ ← list_binary_operands ad e,
  gd ← summ.mmap guess_degree,
  nat_degs ← gd.mmap $ eval_guessing 0,
  let summ_and_degs := summ.zip nat_degs,
  let max_deg := summ_and_degs.argmax (λ e : expr × ℕ, e.2),
  match max_deg with
  | none := fail
      "'`compute_degree`' could not find summands: something has gone very wrong!\n\n"
  | (some first) := return $
    (prod.fst <$> summ_and_degs.filter (λ f : expr × ℕ, f.2 = first.2), first.2)
  end

end compute_degree
--#check to_nat
namespace interactive
open compute_degree
#check polynomial.coeff_mul_X_pow'
#check polynomial.coeff_monomial
#check polynomial.coeff_bit0_mul
#check polynomial.coeff_bit1_mul
#check polynomial.coeff_neg
#check zero_add
#check add_zero
#check polynomial.coeff_neg

#check polynomial.coeff_mul_X_pow'
#check polynomial.coeff_monomial
#check polynomial.coeff_bit0_mul
#check polynomial.coeff_bit1_mul
#check polynomial.coeff_neg
#check zero_add
#check add_zero
#check polynomial.coeff_one
#check zero_eq_bit0
#check bit0_eq_zero
#check if_false
#check neg_zero'
#check add_zero
#check one_ne_zero
#check not_false_iff


meta def compute_degree : tactic unit :=
do try $ ( refine ``((polynomial.degree_eq_iff_nat_degree_eq_of_pos _).mpr _) >>
    rotate ),
   `(@polynomial.nat_degree %%R %%inst %%pol = %%deg) ← target,
  refine ``(le_antisymm _ (polynomial.le_nat_degree_of_ne_zero _)),
  focus1 ( compute_degree_le_core ff >> done ),
  ad ← to_expr ``((+) : (%%R) → (%%R) → (%%R)) tt ff,
--  trace deg, infer_type deg >>= trace,
  tar_deg ← eval_expr ℕ deg,
--trace tar_deg,
--  summ ← list_binary_operands ad pol,trace summ,
  `[ repeat { rw coeff_add } ],
--  te ← infer_type pol,
  --trace target,
  --trace sum_coefs,
  --trace "summ0",
  --let napps := summ.map (λ e, (e.get_app_args.nth 2).get_or_else e),--trace napps,
--  repeat (do
--  target >>= trace,
  `(%%sum_coefs ≠ %%z) ← target | fail "oyoyoy",
  summ ← list_binary_operands ad sum_coefs,--trace summ,
  trace "mapps",
  mapps ← summ.mfilter (λ e, do
    let f := (e.get_app_args.nth 2).get_or_else e,
    gf ← (guess_degree f) ,
    ef ← eval_guessing 0 gf,
    return (ef < tar_deg : bool)),--trace mapps,
  mapps.mmap' (λ x, try $ remove_one_coeff x),
--  gs ← get_goals,
--  gt ← gs.mmap infer_type,
--  trace gt,
--  target >>= trace,
   --try $
--    `[ simp [ polynomial.coeff_one ]],
     try $ any_goals' `[ simp only [polynomial.coeff_C, polynomial.coeff_mul_X_pow', polynomial.coeff_monomial, polynomial.coeff_bit0_mul, polynomial.coeff_bit1_mul, polynomial.coeff_neg,
    zero_add, add_zero, polynomial.coeff_one, zero_eq_bit0, bit0_eq_zero, if_false, neg_zero', add_zero, one_ne_zero, not_false_iff] ],
  try $ any_goals' `[ norm_num ],
--  gs ← get_goals,
--  gt ← gs.mmap infer_type,
--  trace gt,
--  target >>= trace,trace gs.length,
  --iterate_at_most 4 $ any_goals' norm_assum,
    try $ any_goals' `[ simp only [polynomial.coeff_C, polynomial.coeff_one
    , zero_eq_bit0, bit0_eq_zero, if_false, neg_zero', add_zero, one_ne_zero, not_false_iff
    ]],
    try $ any_goals' assumption

meta def compute_degree_1 : tactic unit :=
do try $ ( refine ``((polynomial.degree_eq_iff_nat_degree_eq_of_pos _).mpr _) >>
    rotate ),
  single_term_suggestions,
  t ← target,
  `(polynomial.nat_degree %%pol = %%degv) ← target |
  fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`",
  gde ← guess_degree pol,
  deg ← eval_guessing 0 gde,
  degvn ← eval_expr ℕ degv,
  guard (deg = degvn) <|>
  ( do ppe ← pp deg, ppg ← pp degvn,
    fail sformat!("'{ppe}' is the expected degree\n" ++ "'{ppg}' is the given degree\n") ),
  repeat $
  ( do `(polynomial.nat_degree %%po = _) ← target,
    compute_step deg po ),
  check_target_changes t,
  any_goals' $ try $ compute_degree_le_core ff,
  `(polynomial.nat_degree %%pol = %%degv) ← target,
  any_goals' $ try $ single_term_resolve pol,
  try $ any_goals' norm_assum

/--  `compute_degree.with_lead lead` assumes that `lead` is an expression for the highest degree
term of a polynomial and proceeds to try to close a goal of the form
`f.nat_degree = d` or `f.degree = d`. -/
meta def _root_.tactic.compute_degree.with_lead_ (lead : expr) : tactic unit := do
move_op.with_errors ``((+)) [(ff, pexpr.of_expr lead)] none,
refine ``(polynomial.nat_degree_add_left_succ _ %%lead _ _ _) <|>
  single_term_suggestions,
single_term_resolve lead,
gs ← get_goals,
gts ← gs.mmap infer_type,
-- `is_ineq` is a list of tactics, one for each goal:
-- * if the goal has the form `f.nat_degree ≤ d`, the tactic is `compute_degree_le`
-- * otherwise, it is the tactic that tries `norm_num` and `assumption`
is_ineq ← gts.mmap (λ t : expr, do match t with
  | `(polynomial.nat_degree %%_ ≤ %%_) := return $ compute_degree_le_core ff
  | _                                  := return norm_assum end),
focus' is_ineq

setup_tactic_parser

/--  `compute_degree_le` tries to solve a goal of the form `f.nat_degree ≤ d` or  `f.degree ≤ d`,
where `d : ℕ` or `d : with_bot ℕ` and `f : R[X]`.

If the given degree `d` is smaller than the one that the tactic computes,
then the tactic suggests the degree that it computed.

Using `compute_degree_le!` also recurses inside powers.
Use it only if you know how to prove that exponents of terms other than `X ^ ??` are non-zero!
 -/
meta def compute_degree_le (expos : parse (tk "!" )?) : tactic unit :=
if expos.is_some then compute_degree_le_core tt else compute_degree_le_core ff

#exit
/--  `compute_degree.with_lead lead` assumes that `lead` is an expression for the highest degree
term of a polynomial and proceeds to try to close a goal of the form
`f.nat_degree = d` or `f.degree = d`. -/
meta def _root_.tactic.compute_degree.with_lead (args : list expr) : tactic unit := do
let larg := args.map (λ e, (ff, pexpr.of_expr e)),
move_op.with_errors ``((+)) larg none,
match args with
| [] := fail "oops, no terms of top degree?"
| (a::as) := do
  `(@polynomial.nat_degree %%R %%inst %%pol = %%deg) ← target,
  mad ← to_expr ``(has_add.add : polynomial %%R → polynomial %%R → polynomial %%R) tt ff,
  meq ← to_expr ``((=) : ℕ → ℕ → Prop) tt ff,
  mdeg ← to_expr ``(polynomial.nat_degree : polynomial %%R → ℕ) tt ff,
  n ← get_unused_name "h",
  --pR ← infer_type sum, --trace pR,
  --pR ← instantiate_mvars pR, --trace pR,
  summands ← pol.list_summands | skip,
  (r::rs) ← summands.mfilter (λ e : expr, do farg ← args.mfilter (λ g : expr, succeeds $ unify e g),
    return (farg.length = 0)) | skip,
  (expr.const na ls) ← return pol.get_app_fn,
  let sum := as.foldl (λ e, mad.mk_app [e]) a,
  let sum := sum.instantiate_univ_params $ [na].zip ls,--trace "invs", trace sum,
  trace "it sum",
  its ← infer_type sum,
  ppr ← to_expr ``(@polynomial %%R %%inst) tt ff,
  trace $ succeeds $ unify its ppr,
  let sum_rs := rs.foldl (λ e, mad.mk_app [e]) r,
  let sum_rs := sum_rs.instantiate_univ_params $ [na].zip ls,--trace "invs", trace sum_rs,
  let re_sum := mad.mk_app [sum_rs, sum],trace re_sum,
  let re_sum := re_sum.instantiate_univ_params $ [na].zip ls,trace "re_sum", trace re_sum,
  let top_deg := expr.mk_app mdeg [sum],
--  unify pR `(@polynomial %%R %%inst),
  top_eq ← mk_app `eq [top_deg, deg],
  neq ← assert n top_eq,
  rotate,
  --(@expr.const tt na ls, es) ← return mdeg.get_app_fn_args,

  --trace "ls mdeg", trace ls,trace mdeg,
    --te ← infer_type e, instantiate_univ_params, unify te `(polynomial %%R),
--  (@expr.const tt na ls, es) ← return sum.get_app_fn_args,trace "ls sum", trace ls,trace sum,
  --ls.mmap infer_type >>= trace,

  toph ← get_local n,
  re_eq ← mk_app `eq [pol, re_sum],
  --trace re_eq,
  (_, prf) ← solve_aux re_eq (reflexivity <|> `[{ simp only [add_assoc], done }]), --trace prf,
  --gs ← get_goals, gs.mmap infer_type >>= trace,
  rewrite_target prf,
  refine ``(polynomial.nat_degree_add_left_succ _ _ _ _ _) <|>
    single_term_suggestions,
  tactic.exact toph--,
--  compute_degree_le_core ff
--  `[ rw nat_degree_add_eq_left_of_nat_degree_lt ],
--  rewrite_target toph
--  rewrite_target neq
  --trace prf
--  let rest := summands.filter (λ e : expr, e ∈ args.mfilter (λ g : expr, succeeds $ unify e g)), trace rest

--  rest ← summands.mfilter (λ f, succeeds $ unify f a), trace rest
end
--  let rest := summands.filter (λ e, e ∉ args), trace rest
  --let sum_rest := (rest).foldl (λ e, mad.mk_app [e]) r, trace sum_rest,
#check list.band
--  repeat $ rewrite_target add_assoc (X + X + X)
#eval [4,5].filter (∈ [4])
#check list.remove_all
/-
refine ``(polynomial.nat_degree_add_left_succ _ %%lead _ _ _) <|>
  single_term_suggestions,
single_term_resolve lead,
gs ← get_goals,
gts ← gs.mmap infer_type,
-- `is_ineq` is a list of tactics, one for each goal:
-- * if the goal has the form `f.nat_degree ≤ d`, the tactic is `compute_degree_le`
-- * otherwise, it is the tactic that tries `norm_num` and `assumption`
is_ineq ← gts.mmap (λ t : expr, do match t with
  | `(polynomial.nat_degree %%_ ≤ %%_) := return $ compute_degree_le_core ff
  | _                                  := return norm_assum end),
focus' is_ineq
-/

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
meta def compute_degree_old : parse opt_pexpr_list → tactic unit
| [] := do is_deg ← succeeds $ refine ``((polynomial.degree_eq_iff_nat_degree_eq_of_pos _).mpr _) >>
  interactive.rotate,
  `(polynomial.nat_degree %%tl = %%tr) ← target |
    fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`",
  (lead, m') ← extract_top_degree_terms_and_deg tl,
  td ← eval_expr ℕ tr,
  if m' ≠ td then do
    pptl ← pp tl, ppm' ← pp m',
    if is_deg then
      fail sformat!"should the degree be '{m'}'?"
    else
     fail sformat!"should the nat_degree be '{m'}'?"
  else do
    tactic.compute_degree.with_lead (lead)
| [lead] := do `(polynomial.nat_degree %%tl = %%tr) ← target |
    fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`",
  tls ← tl.list_summands,
  lead ← to_expr lead,
  (lead :: hs) ← tls.mfilter $ λ e', succeeds $ unify lead e',
  tactic.compute_degree.with_lead [lead]
| _  := fail "'compute_degree' only accepts one leading term"

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree],
  tags := ["arithmetic, finishing"] }

add_tactic_doc
{ name := "compute_degree",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree],
  tags := ["arithmetic, finishing"] }

end interactive

end tactic
