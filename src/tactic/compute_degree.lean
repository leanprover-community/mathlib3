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

namespace polynomial
open_locale polynomial

variables {R : Type*}

section semiring
variables [semiring R] {f g : R[X]} {d e n : ℕ}

lemma coeff_bit0 (P : R[X]) (n : ℕ) :
  (bit0 P).coeff n = bit0 P.coeff n :=
coeff_add _ _ _

lemma coeff_bit1_zero (P : R[X]) :
  (bit1 P).coeff 0 = bit1 P.coeff 0 :=
by simp only [bit1, coeff_add, coeff_bit0, coeff_one_zero, pi.add_apply, pi.one_apply]

lemma nat_degree_eq_of_le_of_coeff_ne_zero {n : ℕ} {f : polynomial R}
  (fn : f.nat_degree ≤ n) (f0 : f.coeff n ≠ 0) :
  f.nat_degree = n :=
fn.antisymm (le_nat_degree_of_ne_zero f0)

/-
lemma nat_degree_add_of_nat_degree_eq' {n : ℕ}
  (df : f.nat_degree ≤ n) (dg : g.nat_degree ≤ n) (fg : f.coeff n + g.coeff n ≠ 0) :
  (f + g).nat_degree = n :=
nat_degree_eq_of_le_of_coeff_ne_zero ((nat_degree_add_le _ _).trans (max_le ‹_› ‹_›))
  (by rwa coeff_add)
-/

lemma coeff_mul_of_nat_degree_le (df : f.nat_degree ≤ d) (eg : g.nat_degree ≤ e) :
  (f * g).coeff (d + e) = f.coeff d * g.coeff e :=
begin
  refine (coeff_mul _ _ _).trans _,
  refine finset.sum_eq_single (d, e) _ (by simp),
  rintros ⟨d1, e1⟩ h de,
  rcases (trichotomous d1 d : d1 < d ∨ _) with k|rfl|k,
  { convert mul_zero _,
    refine coeff_eq_zero_of_nat_degree_lt (eg.trans_lt _),
    linarith [finset.nat.mem_antidiagonal.mp h] },
  { exact (de (by simpa using h)).elim },
  { convert zero_mul _,
    exact coeff_eq_zero_of_nat_degree_lt (df.trans_lt k) }
end

lemma coeff_mul_of_nat_degree_le' (de : d + e = n) (df : f.nat_degree ≤ d) (eg : g.nat_degree ≤ e) :
  (f * g).coeff n = f.coeff d * g.coeff e :=
by rwa [← de, coeff_mul_of_nat_degree_le df eg]

lemma coeff_pow_of_nat_degree_le {d e : ℕ}
  (df : f.nat_degree ≤ d) :
  (f ^ e).coeff (d * e) = (f.coeff d) ^ e :=
begin
  induction e with e he,
  { simp },
  { rw [pow_succ', pow_succ', ← he, nat.mul_succ, coeff_mul_of_nat_degree_le _ df],
    refine nat_degree_pow_le.trans (le_trans _ (mul_comm _ _).le),
    exact mul_le_mul_of_nonneg_left df e.zero_le }
end

lemma coeff_pow_of_nat_degree_le' (de : d * e = n) (df : f.nat_degree ≤ d) :
  (f ^ e).coeff n = (f.coeff d) ^ e :=
by rwa [← de, coeff_pow_of_nat_degree_le]

lemma coeff_add_eq_left_of_succ (n : ℕ) (dg : g.nat_degree ≤ n) :
  (f + g).coeff (n + 1) = f.coeff (n + 1) :=
(coeff_add _ _ _).trans $ (congr_arg _ $ coeff_eq_zero_of_nat_degree_lt $
  nat.lt_succ_iff.mpr dg).trans $ add_zero _

lemma coeff_add_eq_right_of_succ (n : ℕ) (df : f.nat_degree ≤ n) :
  (f + g).coeff (n + 1) = g.coeff (n + 1) :=
by { rw add_comm, exact coeff_add_eq_left_of_succ _ df }

lemma monic_of_nat_degree_le_of_coeff_eq_one (fn : f.nat_degree ≤ n) (fc : f.coeff n = 1) :
  monic f :=
begin
  nontriviality,
  unfold monic,
  unfold leading_coeff,
  convert fc,
  refine le_antisymm fn _,
  exact le_nat_degree_of_ne_zero (ne_of_eq_of_ne fc one_ne_zero),
end


end semiring

section ring
variables [ring R] {f g : R[X]} (n : ℕ)

lemma coeff_sub_eq_left_of_succ (dg : g.nat_degree ≤ n) :
  (f - g).coeff (n + 1) = f.coeff (n + 1) :=
by {rw [sub_eq_add_neg, coeff_add_eq_left_of_succ], rwa nat_degree_neg }

lemma coeff_sub_eq_right_of_succ (df : f.nat_degree ≤ n) :
  (f - g).coeff (n + 1) = - g.coeff (n + 1) :=
by rwa [sub_eq_add_neg, coeff_add_eq_right_of_succ, coeff_neg]

end ring

end polynomial

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

/-- `resolve_sum_step e` takes the type of the current goal `e` as input.
It tries to make progress on the goal `e` by reducing it to subgoals.
It assumes that `e` is of the form `f.nat_degree ≤ d`, failing otherwise.

`resolve_sum_step` progresses into `f` if `f` is
* a sum, difference, opposite, product, or a power;
* a monomial;
* `C a`;
* `0, 1` or `bit0 a, bit1 a` (to deal with numerals).

The side-goals produced by `resolve_sum_step` are either again of the same shape `f'.nat_degree ≤ d`
or of the form `m ≤ n`, where `m n : ℕ`.

If `d` is less than `guess_degree f`, this tactic will create unsolvable goals.
-/
meta def resolve_sum_step : expr → tactic unit
| `(nat_degree %%tl ≤ %%tr) := match tl with
  | `(%%tl1 + %%tl2) := refine ``((nat_degree_add_le_iff_left _ _ _).mpr _)
  | `(%%tl1 - %%tl2) := refine ``((nat_degree_sub_le_iff_left _ _ _).mpr _)
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
| e := fail!("'resolve_sum_step' was called on\n" ++
  "{e}\nbut it expects `f.nat_degree ≤ d`")

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

/--
`get_lead_coeff R e` assumes that `R` is an expression representing a `(semi)_ring` and that `e`
is an expression representing a polynomial with coefficients in the type `R`.  It returns an
expression representing the "visible leading coefficient" of `e`.  This means that it guesses the
degree of each term and simply discards the terms whose guessed degree is smaller than the top
degree.

It is important that `get_lead_coeff` does not do any other simplifications of the expression.
Indeed, `resolve_coeff` starts with the equality between `coeff e <top_degree of e>` and
`get_lead_coeff R e` and peels off one by one the operations that make up the expression of
`get_lead_coeff R e`.  Thus, `get_lead_coeff` guides the simplifications in the coefficients.
In particular, there is some duplication of code with which `norm_num` could deal, but, following
the current strategy, we are able to reach places where `norm_num` would not reach: most notably,
`resolve_coeff` deals with degrees of products and of powers.

The implementation of `get_lead_coeff` is a straightforward match on the elementary operations
that can be performed on a polynomial.
-/
meta def get_lead_coeff (R : expr) : expr → tactic expr
| (app `(⇑C) a) :=
  pure a
| (app `(⇑(monomial %%n)) x) :=
  pure x
| `(X) := do
  oner ← to_expr ``(has_one.one : %%R) tt ff,
  pure oner
| `(X ^ %%n) := do
  oner ← to_expr ``(has_one.one : %%R) tt ff,
  pure oner
| `(bit0 %%a) := do
  ta ← get_lead_coeff a,
  op ← to_expr ``(bit0 : %%R → %%R) tt ff,
  return $ op.mk_app [ta]
| `(bit1 %%a) := do
  ta ← get_lead_coeff a,
  op ← to_expr ``(bit1 : %%R → %%R) tt ff,
  return $ op.mk_app [ta]
| `(%%a + %%b) := do
  [da, db] ← [a,b].mmap $ λ f, guess_degree f >>= eval_guessing 0,
  if da ≠ db then
    if da < db then
      get_lead_coeff b
    else
      get_lead_coeff a
  else do
    [ta, tb] ← [a, b].mmap get_lead_coeff,
    op ← to_expr ``(has_add.add : %%R → %%R → %%R),
    return $ op.mk_app [ta, tb]
| `(%%a - %%b) := do
  [da, db] ← [a,b].mmap $ λ f, guess_degree f >>= eval_guessing 0,
  if da ≠ db then
    if da < db then do
      op ← to_expr ``(has_neg.neg : %%R → %%R) tt ff,
      tb ← get_lead_coeff b,
      return $ op.mk_app [tb]
    else
      get_lead_coeff a
  else do
    [ta, tb] ← [a, b].mmap get_lead_coeff,
    op ← to_expr ``(has_sub.sub : %%R → %%R → %%R) tt ff,
    return $ op.mk_app [ta, tb]
| `(%%a * %%b) := do
  [la, lb] ← [a, b].mmap get_lead_coeff,
  op ← to_expr ``(has_mul.mul : %%R → %%R → %%R),
  return $ op.mk_app [la, lb]
| `(%%a ^ %%n) := do
  la ← get_lead_coeff a,
  op ← to_expr ``(has_pow.pow : %%R → ℕ → %%R),
  return $ op.mk_app [la, n]
| `(- %%a) := do
  la ← get_lead_coeff a,
  op ← to_expr ``(has_neg.neg : %%R → %%R),
  return $ op.mk_app [la]
| e := do
  deg ← guess_degree e,
  op ← to_expr ``(coeff : polynomial %%R → ℕ → %%R),
  return $ op.mk_app [e, deg]

end compute_degree

namespace interactive
open compute_degree polynomial expr

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
focus1 $ do t ← target,
  try $ refine ``(degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr _)),
  `(nat_degree %%tl ≤ %%tr) ← target |
    fail "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`",
  expected_deg ← guess_degree tl >>= eval_guessing 0,
  deg_bound ← eval_expr' ℕ tr <|> pure expected_deg,
  if deg_bound < expected_deg
  then fail sformat!"the given polynomial has a term of expected degree\nat least '{expected_deg}'"
  else
    repeat $ target >>= resolve_sum_step,
    (do gs ← get_goals >>= list.mmap infer_type,
      success_if_fail $ gs.mfirst $ unify t) <|> fail "Goal did not change",
    try $ any_goals' norm_assum

end interactive

open interactive polynomial expr compute_degree
/--
`resolve_coeff` assumes that the goal has the form `f.coeff n = x`.  It is important that `x`
is the result of applying `lead_coeff` to `f`!  Indeed, `resolve_coeff` reads through the expression
making up `f` and matches each step with what `lead_coeff` would do in the current situation.
This means that all the side-goals that `resolve_coeff` leaves are always of the same shape
`f'.coeff n' = lead_coeff R f'`.

In some sense, this views `coeff _ <visible_top_degree>` and a "monad" converting between
`R[X]` and `R`.  `resolve_coeff` performs the operations building `f` across the monad.
-/
meta def resolve_coeff : tactic unit := focus1 $ do
`(coeff %%f %%n = _) ← target >>= instantiate_mvars,
--do `(coeff %%f %%n = _) ← whnf t reducible | fail!"{t} has the wrong form",
match f with
| (app `(⇑C) _) := try $ refine ``(coeff_C_zero)
| (app `(⇑(@monomial %%R %%inst %%n)) x) := (try $ refine ``(coeff_monomial))
| `(X) := try $ refine ``(coeff_X_one)
| `(X ^ %%n) := try $ refine ``(coeff_X_pow_self %%n)
| `(bit0 %%a) := do
  refine ``((coeff_bit0 _ _).trans _),
  refine ``((pi.bit0_apply _ _).trans _),
  refine ``(congr_arg bit0 _),
  reflexivity <|> resolve_coeff
| `(bit1 %%a) := do
  refine ``((coeff_bit1_zero _).trans _),
  refine ``((pi.bit1_apply _ _).trans _),
  refine ``(congr_arg bit1 _),
  reflexivity <|> resolve_coeff
| `(%%a + %%b) := do
  [da, db] ← [a,b].mmap (λ e, guess_degree e >>= eval_guessing 0),
  (if da ≠ db then do
    if da < db then refine ``((coeff_add_eq_right_of_succ _ _).trans _)
    else refine ``((coeff_add_eq_left_of_succ _ _).trans _),
    compute_degree_le
  else refine ``((coeff_add _ _ _).trans _);
  congr' (some 1));
  resolve_coeff
| `(%%a - %%b) := do
  [da, db] ← [a,b].mmap (λ e, guess_degree e >>= eval_guessing 0),
  (if da ≠ db then do
    if da < db then refine ``((coeff_sub_eq_right_of_succ _ _).trans (neg_inj.mpr _))
    else refine ``((coeff_sub_eq_left_of_succ _ _).trans _),
    compute_degree_le
  else refine ``((coeff_sub _ _ _).trans _) >> congr' (some 1));
  resolve_coeff
| `(%%a * %%b) := do
  [da, db] ← [a,b].mmap guess_degree,
  refine ``((coeff_mul_of_nat_degree_le' (by norm_num : %%da + %%db = %%n) _ _).trans _),
  iterate_at_most' 2 compute_degree_le,
  try $ congr' (some 1);
  resolve_coeff
| `(%%a ^ %%ex) := do
  da ← guess_degree a,
  refine ``((coeff_pow_of_nat_degree_le' (by norm_num : %%da * %%ex = _) _).trans _),
  compute_degree_le,
  try $ congr' (some 1);
  resolve_coeff
| `(- %%a) := do
  refine ``((coeff_neg _ _).trans (neg_inj.mpr _)),
  resolve_coeff
| e := skip
end

namespace interactive
open compute_degree

/--
`simp_coeff` assumes that the target is either of the form `f.coeff n = x` or of the form
`f.coeff n ≠ x`.  It then proceeds to simplify `f.coeff n` recurring to the pair
`lead_coeff/resolve_coeff` to scan the expression of `f` and producing a hopefully simpler
expression.  After this, it calls on `simp only [a few lemmas]` and `norm_num` to simplify further.
-/
meta def simp_coeff : tactic unit :=
do t ← target >>= instantiate_mvars,
  (t_is_eq, f, m) ← match t with
    | `(coeff %%f %%m = _) := return (tt, f, m)
    | `(coeff %%f %%m ≠ _) := return (ff, f, m)
    | _ := fail "Goal is not of the form `f.coeff n = x` or `f.coeff n ≠ x`"
    end,
  exp_deg ← guess_degree f,
  [d_nat, m_nat] ← [exp_deg, m].mmap $ eval_expr' ℕ,
  guard (d_nat = m_nat) <|> fail!(
  "`simp_coeff` checks that the expected degree is equal to the degree appearing in `coeff`\n" ++
  "the expected degree is `{d_nat}`, but you are asking about the coefficient of degree `{m_nat}`"),
  `(@polynomial %%R %%inst) ← infer_type f,
  lc ← get_lead_coeff R f,
  nn ← get_unused_name "c_c",
  cf ← to_expr ``(coeff : polynomial %%R → ℕ → %%R),
  co_eq_co ← mk_app `eq [cf.mk_app [f, m], lc],
  c_c ← assert nn co_eq_co,
  interactive.swap,
  if t_is_eq then refine ``(eq.trans %%c_c _) else refine ``(ne_of_eq_of_ne %%c_c _),
  try $ tactic.clear c_c,
  interactive.swap,
  resolve_coeff,
  try $ any_goals' $
    `[{ simp only [pi.bit0_apply, coeff_bit0, coeff_bit1, coeff_one_zero, map_one]; norm_num }]

section parsing
setup_tactic_parser

/--
Reduce coeff takes a polynomial `f` as an input and produces a hypothesis of the form
`c_c : f.coeff n = <simplified expression>`, where the simplified expression is obtained via the
`lead_coeff/resolve_coeff` pair.
-/
meta def reduce_coeff (fp : parse texpr) : tactic unit :=
do
  f ← to_expr ``(%%fp) tt ff,
  exp_deg ← guess_degree f >>= eval_expr' ℕ,
  `(@polynomial %%R %%inst) ← infer_type f,
  lc ← get_lead_coeff R f,
  nn ← get_unused_name "c_c",
  cf ← to_expr ``(coeff : polynomial %%R → ℕ → %%R),
  co_eq_co ← mk_app `eq [cf.mk_app [f, `(exp_deg)], lc],
  c_c ← assert nn co_eq_co,
  resolve_coeff
  --,
  --try `[ conv_rhs at c_c {norm_num} ]
end parsing

/--  `compute_degree` tries to close goals of the form `f.(nat_)degree = d`.  It converts the
goal to showing that
* the degree is at most `d`, calling `compute_degree_le` to solve this case;
* the coefficient of degree `n` is non-zero, calling `simp_coeff` to simplify this goal.
Unless the polynomial is particularly complicated, `compute_degree` with either succeed of leave
a simpler goal to prove.
 -/
meta def compute_degree : tactic unit := focus $ do
t ← target >>= (λ f, whnf f reducible),
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
refine ``(nat_degree_eq_of_le_of_coeff_ne_zero _ _),
focus' [compute_degree_le, simp_coeff]

/--  `prove_monic` tries to close goals of the form `monic f`.  It converts the
goal to showing that
* the degree is at most `d`, calling `compute_degree_le` to solve this case;
* the coefficient of degree `n` equals `1`, calling `simp_coeff` to simplify this goal.
Unless the polynomial is particularly complicated, `prove_monic` with either succeed of leave
a simpler goal to prove.
 -/
meta def prove_monic : tactic unit := focus $ do
`(monic %%pol) ← target >>= (λ f, whnf f reducible) | fail"Goal is not of the form `monic f`",
deg ← guess_degree pol,
refine ``(monic_of_nat_degree_le_of_coeff_eq_one (_ : nat_degree %%pol ≤ %%deg) _),
focus' [compute_degree_le, simp_coeff],
try reflexivity

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree_le],
  tags := ["arithmetic", "finishing"] }

end interactive
end tactic
