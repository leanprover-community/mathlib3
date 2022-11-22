/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.lemmas

/-!
# `compute_degree` & Co: tactics for computing degrees of polynomials

This file defines four tactics:
* `tactic.interactive.compute_degree_le` tries to solve goals of the form `f.(nat_)degree ≤ d`;
* `tactic.interactive.compute_degree` tries to solve goals of the form `f.(nat_)degree = d`;
* `tactic.interactive.prove_monic` tries to solve goals of the form `f.monic`;
* `tactic.interactive.simp_lead_coeff` tries to solve goals of the form `f.coeff n = x`,
  assuming that `n` is the expected degree of `f`.

All of these tactics may leave side-goals, in case they are not entirely successful.

See the respective doc-strings for more details.

##  Future work

* Add better functionality to deal with exponents that are not necessarily closed natural numbers.
* Add support for proving goals of the from `f.(nat_)degree ≠ 0`.
* Make sure that `degree` and `nat_degree` are equally supported, especially `f.degree = 0`.
* Should the tactic handle `f.degree = ⊥`?.

##  Implementation details

The tactics apply when the goal contains a polynomial `f`.  They recurse into `f` breaking apart
sums, products and powers.  They handle numerals, `C a, X (^ n), monomial a n` separately.
-/

namespace polynomial
open_locale polynomial

variables {R : Type*}

section semiring
variables [semiring R] {f g : R[X]} {d e n : ℕ}

lemma coeff_bit1_zero (P : R[X]) :
  (bit1 P).coeff 0 = bit1 (P.coeff 0) :=
by simp only [bit1, bit0, coeff_add, coeff_one_zero, pi.add_apply, pi.one_apply]

/-  This lemma is useful to expose the right hypotheses for `tactic.interactive.compute_degree`. -/
lemma coeff_mul_of_nat_degree_le' (de : d + e = n) (df : f.nat_degree ≤ d) (eg : g.nat_degree ≤ e) :
  (f * g).coeff n = f.coeff d * g.coeff e :=
by rwa [← de, coeff_mul_of_nat_degree_le df eg]

/-  This lemma is useful to expose the right hypotheses for `tactic.interactive.compute_degree`. -/
lemma coeff_pow_of_nat_degree_le' (de : d * e = n) (df : f.nat_degree ≤ d) :
  (f ^ e).coeff n = (f.coeff d) ^ e :=
by rwa [← de, coeff_pow_of_nat_degree_le]

lemma coeff_monomial_self {a : R} : coeff (monomial n a) n = a :=
coeff_monomial.trans $ if_pos rfl

end semiring

end polynomial

namespace tactic

open expr polynomial
namespace compute_degree

/--  `guess_degree_with fn e` takes as inputs a function `fn : expr → tactic expr` and an `e` that
is an expression in a polynomial ring.  It makes an attempt at guessing the `nat_degree` of `e`,
using the function `fn` to inform some choices.  Heuristics for `guess_degree_with`:
* `0, 1, C a`,      guess `0`,
* `polynomial.X`,   guess `1`,
*  `bit0/1 f, -f`,  guess `guess_degree_with f`,
* `f + g, f - g`,   guess `max (guess_degree_with f) (guess_degree_with g)`,
* `f * g`,          guess `guess_degree_with f + guess_degree_with g`,
* `f ^ n`,          guess `guess_degree_with f * (fn n)`,
* `monomial n r`,   guess `fn n`,
* `f` not as above, guess `fn f.nat_degree`.

In the applications (`tactic.compute_degree.guess_degree, tactic.compute_degree.guess_degree'`),
the function `fn` is either the identity (`pure : expr → tactic expr` to be precise) or
the function that returns
* the expression itself, if it represents a closed natural number, or
* zero, otherwise.
-/
meta def guess_degree_with (fn : expr → tactic expr) : expr → tactic expr
| `(has_zero.zero)           := pure `(0)
| `(has_one.one)             := pure `(0)
| `(- %%f)                   := guess_degree_with f
| (app `(⇑C) x)              := pure `(0)
| `(X)                       := pure `(1)
| `(bit0 %%a)                := guess_degree_with a
| `(bit1 %%a)                := guess_degree_with a
| `(%%a + %%b)               := do [da, db] ← [a, b].mmap guess_degree_with,
                                pure $ expr.mk_app `(max : ℕ → ℕ → ℕ) [da, db]
| `(%%a - %%b)               := do [da, db] ← [a, b].mmap guess_degree_with,
                                pure $ expr.mk_app `(max : ℕ → ℕ → ℕ) [da, db]
| `(%%a * %%b)               := do [da, db] ← [a, b].mmap guess_degree_with,
                                pure $ expr.mk_app `((+) : ℕ → ℕ → ℕ) [da, db]
| `(%%a ^ %%n)               := do da ← guess_degree_with a,
                                nn ← fn n,
                                pure $ expr.mk_app `((*) : ℕ → ℕ → ℕ) [da, nn]
| (app `(⇑(monomial %%n)) x) := fn n
| e                          := do `(@polynomial %%R %%inst) ← infer_type e,
                                pe ← to_expr ``(@nat_degree %%R %%inst) tt ff,
                                fn $ expr.mk_app pe [e]

/--  `guess_degree e` returns a guess for the degree of `e`, assuming that `e` represents a
polynomial.  The resulting output may be an expression representing a non-closed term of type `ℕ`.

The guessed degree should coincide with the behaviour of `tactic.compute_degree.resolve_sum_step`:
if `guess_degree f < d`, then `resolve_sum_step` cannot solve the goal `f.nat_degree ≤ d`. -/
meta def guess_degree (e : expr) : tactic expr := guess_degree_with pure e

/--  `guess_degree' e` returns a guess for the degree of `e`, assuming that `e` represents a
polynomial.  The resulting output is a closed term of type `ℕ`: whenever a non-closed term
might appear, the tactic replaces it with `0`.  This allows `tactic.interactive.compute_degree_le`
to succeeds in some situations where the degrees are not closed terms of type `ℕ`. -/
meta def guess_degree' (e : expr) : tactic ℕ :=
guess_degree_with (λ f, eval_expr' ℕ f >> pure f <|> pure `(0)) e >>= eval_expr ℕ

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

If `d` is less than `guess_degree f`, then this tactic will create unsolvable goals. -/
meta def resolve_sum_step : expr → tactic unit
| `(nat_degree %%tl ≤ %%tr) := match tl with
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
      refine ``(nat_degree_pow_le.trans _), -- goal: `⊢ %%n * nat_degree %%tl1 ≤ %%tr`
      -- If `%%n` is 0, we show that the degree is also 0.
      refine ``(dite (%%n = 0) (λ _, (by simp only [*, zero_mul, zero_le])) _),
      -- Otherwise, divide both sides by `%%n` to get a goal of the form `nat_degree _ ≤ _`.
      n0 ← get_unused_name "n0" >>= intro,
      -- goal: `%%n0 : %%n ≠ 0 ⊢ %%n * nat_degree %%tl1 ≤ %%tr`
      refine ``((mul_comm _ _).le.trans ((nat.le_div_iff_mul_le' (nat.pos_of_ne_zero %%n0)).mp _)),
      -- Handle the probable outputs of `guess_degree`.
      -- goal: `%%n0 : %%n ≠ 0 ⊢ nat_degree %%tl1 ≤ %%tr / %%n`
      focus1 (refine ``((%%n0 rfl).elim) <|>
        to_expr ``(nat.mul_div_cancel _ (nat.pos_of_ne_zero %%n0)) tt ff >>= rewrite_target <|>
        to_expr ``(nat.div_self (nat.pos_of_ne_zero %%n0)) tt ff >>= rewrite_target) <|>
      skip
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

/--  These are the cases in which an available lemma computes the degree.
`single_term_suggestions` returns a pair `(e1, e2)`, where `e1` pretty-prints to something
suitable for a "Try this:", while `e2` is an expression that unifies with the target. -/
meta def single_term_suggestions : tactic (expr × (expr ff)) :=
do
  t ← target,
  [``(polynomial.nat_degree_X_pow _),
   ``(polynomial.nat_degree_C _),
   ``(polynomial.nat_degree_X),
   ``(polynomial.nat_degree_C_mul_X_pow _ _ ‹_›),
   ``(polynomial.nat_degree_C_mul_X _ ‹_›)].mfirst
    (λ st, do
      na ← to_expr st tt ff,
      infer_type na >>= unify t >> return (replace_mvars na, st))

/--
`get_lead_coeff c e` assumes that `c` is an `instance_cache` of a `(semi_)ring R` and that `e`
is an expression representing a polynomial with coefficients in the type `R`.  It returns an
expression representing the "visible leading coefficient" of `e`.  This means that it guesses the
degree of each term and simply discards the terms whose guessed degree is smaller than the top
degree.

It is important that `get_lead_coeff` does not do any other simplifications of the expression.
Indeed, `resolve_coeff` starts with the equality between `coeff e <top_degree of e>` and
`get_lead_coeff c e` and peels off one by one the operations that make up the expression of
`get_lead_coeff c e`.  Thus, `get_lead_coeff` guides the simplifications in the coefficients.
In particular, there is some duplication of code with which `norm_num` could deal, but, following
the current strategy, we are able to reach places where `norm_num` would not reach: most notably,
`resolve_coeff` deals with degrees of products and of powers.

The implementation of `get_lead_coeff` is a straightforward match on the elementary operations
that can be performed on a polynomial.
-/
meta def get_lead_coeff (c : instance_cache) : expr → tactic (instance_cache × expr)
| (app `(⇑C) a) := pure (c, a)
| (app `(⇑(monomial %%n)) x) := pure (c, x)
| `(@has_one.one (@polynomial %%R %%_) %%_) := c.mk_app ``has_one.one []
| `(@has_zero.zero (@polynomial %%R %%_) %%_) := c.mk_app ``has_zero.zero []
| `(X) := c.mk_app ``has_one.one []
| `(X ^ %%n) := c.mk_app ``has_one.one []
| `(bit0 %%a) := do
  (c, ta) ← get_lead_coeff a,
  c.mk_bit0 ta
| `(bit1 %%a) := do
  (c, ta) ← get_lead_coeff a,
  c.mk_bit1 ta
| `(%%a + %%b) := do
  [da, db] ← [a,b].mmap guess_degree',
  if da ≠ db then
    if da < db then
      get_lead_coeff b
    else
      get_lead_coeff a
  else do
    [(c1, ta), (c2, tb)] ← [a, b].mmap $ get_lead_coeff,
    c1.mk_app ``has_add.add [ta, tb]
| `(%%a - %%b) := do
  [da, db] ← [a,b].mmap guess_degree',
  if da ≠ db then
    if da < db then do
      (c, tb) ← get_lead_coeff b,
      c.mk_app ``has_neg.neg [tb]
    else
      get_lead_coeff a
  else do
    [(c1, ta), (c2, tb)] ← [a, b].mmap get_lead_coeff,
    c1.mk_app ``has_sub.sub [ta, tb]
| `(%%a * %%b) := do
  [(c1, ta), (c2, tb)] ← [a, b].mmap get_lead_coeff,
  c1.mk_app ``has_mul.mul [ta, tb]
| `(%%a ^ %%n) := do
  (c, ta) ← get_lead_coeff a,
  op ← to_expr ``(has_pow.pow : %%c.α → ℕ → %%c.α),
  return $ (c, op.mk_app [ta, n])
| `(- %%a) := do
  (c, ta) ← get_lead_coeff a,
  c.mk_app ``has_neg.neg [ta]
| e := do
  deg ← guess_degree e,
  op ← to_expr ``(coeff : polynomial %%c.α → ℕ → %%c.α),
  return $ (c, op.mk_app [e, deg])

end compute_degree

namespace interactive
open compute_degree

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
focus1 $ do
  t ← target,
  try $ refine ``(degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr _)),
  `(nat_degree %%tl ≤ %%tr) ← target |
    fail "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`",
  expected_deg ← guess_degree' tl,
  deg_bound ← eval_expr' ℕ tr <|> pure expected_deg,
  if deg_bound < expected_deg
  then fail sformat!"the given polynomial has a term of expected degree\nat least '{expected_deg}'"
  else repeat $ target >>= instantiate_mvars >>= resolve_sum_step,
  (do gs ← get_goals >>= list.mmap infer_type,
    success_if_fail $ gs.mfirst $ unify t) <|> fail "Goal did not change",
  try $ any_goals' norm_assum

end interactive

namespace compute_degree
open interactive
/--
`resolve_coeff` assumes that the goal has the form `f.coeff n = x`.  It is important that `x`
is the result of applying `get_lead_coeff` to `f`!  Indeed, `resolve_coeff` reads through the
expression making up `f` and matches each step with what `get_lead_coeff` would do in the current
situation.  This means that all the side-goals that `resolve_coeff` leaves are always of the same
shape `f'.coeff n' = get_lead_coeff c f'`.

In some sense, this views `coeff _ <visible_top_degree>` as a "monad" converting between
`R[X]` and `R`.  `resolve_coeff` performs the operations building `f` across the monad.
-/
meta def resolve_coeff : tactic unit :=
focus1 $ do
  tg ← target >>= instantiate_mvars,
  `(coeff %%f %%n = _) ← pure tg | fail!"{tg} is not of the form\n`f.coeff n = x`",
  match f with
  | `(@has_one.one %%RX %%_)            := refine ``(coeff_one_zero)
  | (app `(⇑C) _)                       := refine ``(coeff_C_zero)
  | (app `(⇑(@monomial %%R %%_ %%n)) x) := refine ``(coeff_monomial_self)
  | `(X)                                := refine ``(coeff_X_one)
  | `(X ^ %%n)                          := refine ``(coeff_X_pow_self %%n)
  | `(bit0 %%a) := do
    refine ``((coeff_bit0 _ _).trans _),
    refine ``(congr_arg bit0 _),
    reflexivity <|> resolve_coeff
  | `(bit1 %%a) := do
    refine ``((coeff_bit1_zero _).trans _),
    refine ``(congr_arg bit1 _),
    reflexivity <|> resolve_coeff
  | `(%%a + %%b) := do
    [da, db] ← [a,b].mmap guess_degree',
    (if da ≠ db then do
      if da < db then refine ``((coeff_add_eq_right_of_lt (nat.lt_succ_iff.mpr _)).trans _)
      else refine ``((coeff_add_eq_left_of_lt (nat.lt_succ_iff.mpr _)).trans _),
      compute_degree_le
    else refine ``((coeff_add _ _ _).trans _);
    congr' (some 1));
    resolve_coeff
  | `(%%a - %%b) := do
    [da, db] ← [a,b].mmap guess_degree',
    (if da ≠ db then do
      if da < db then refine ``((coeff_sub_eq_neg_right_of_lt (nat.lt_succ_iff.mpr _)).trans
        (neg_inj.mpr _))
      else refine ``((coeff_sub_eq_left_of_lt (nat.lt_succ_iff.mpr _)).trans _),
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
    try compute_degree_le,
    try $ congr' (some 1);
    resolve_coeff
  | `(- %%a) := do
    refine ``((coeff_neg _ _).trans (neg_inj.mpr _)),
    resolve_coeff
  | e := skip
  end

setup_tactic_parser
/--  `poly_and_deg_to_equation f deg (with na)?` takes as input
* an expression `f` representing a polynomial,
* an expression `deg` representing an natural number and
* an optional `with h` argument to assign a name to the side-goal that the tactic produces.
It returns
* a term `h` of type `f.coeff deg = lc`, where `lc` is the leading coefficient of `f`, computed by
  `get_lead_coeff`;
* as a side-goal to show the equality ``f.coeff deg = lc`.
-/
meta def poly_and_deg_to_equation (f deg : expr) (na : parse with_ident_list) :
  tactic expr :=
do
  `(@polynomial %%R %%_) ← infer_type f,
  c ← mk_instance_cache R,
  (c, lc) ← get_lead_coeff c f,
  ide ← match na with
    | []      := pure `c_c
    | [a]     := pure a
    | (a::as) := do pa ← pp a,
      fail format!"Try this: simp_lead_coeff with {pa}"
    end,
  nn ← get_unused_name ide,
  cf ← to_expr ``(coeff : polynomial %%R → ℕ → %%R),
  co_eq_co ← mk_app `eq [cf.mk_app [f, deg], lc],
  assert nn co_eq_co

end compute_degree

namespace interactive
open compute_degree

section parsing
setup_tactic_parser

/--
`simp_lead_coeff (with h)?` assumes that the target is either of the form `f.coeff n = x` or of
the form `f.coeff n ≠ x`.  It then proceeds to simplify `f.coeff n` recurring to the pair
`get_lead_coeff/resolve_coeff` to scan the expression of `f` and producing a hopefully simpler
expression.  After this, it calls on `simp only [a few lemmas]` and `norm_num` to simplify further.
If the optional `with h` argument is given, then `h` is the name that `simp_lead_coeff` assigns to
possible side-goals.
-/
meta def simp_lead_coeff (na : parse with_ident_list) : tactic unit :=
do t ← target >>= instantiate_mvars,
  (t_is_eq, f, m) ← match t with
    | `(coeff %%f %%m = _) := return (tt, f, m)
    | `(coeff %%f %%m ≠ _) := return (ff, f, m)
    | _ := fail "Goal is not of the form `f.coeff n = x` or `f.coeff n ≠ x`"
    end,
  d_nat ← guess_degree' f,
  m_nat ← eval_expr' ℕ m,
  guard (d_nat = m_nat) <|> fail!(
  "`simp_lead_coeff` checks that the expected degree equals the degree appearing in `coeff`\n" ++
  "the expected degree is `{d_nat}`, but you are asking about the coefficient of degree `{m_nat}`"),
  c_c ← poly_and_deg_to_equation f m na,
  interactive.swap,
  if t_is_eq then refine ``(eq.trans %%c_c _) else refine ``(ne_of_eq_of_ne %%c_c _),
  try $ tactic.clear c_c,
  refine ``(one_ne_zero) <|> interactive.swap,
  resolve_coeff

/--  `compute_degree` tries to close goals of the form `f.(nat_)degree = d`.  It converts the
goal to showing that
* the degree is at most `d`, calling `compute_degree_le` to solve this case;
* the coefficient of degree `d` is non-zero, calling `simp_lead_coeff` to simplify this goal.

`compute_degree` will suggest a term-mode proof if it's a oneliner. If you want to disable these
suggestions, for example when you're working on multiple goals at once, use `compute_degree!`.

Unless the polynomial is particularly complicated, `compute_degree` either succeeds of leaves
a simpler goal to prove.  Continue reading for a discussion of what are the current
limitations to the tactic.

`compute_degree` scans the polynomial `f` and computes the largest degree `n` that it sees.
It then assumes that this degree `n` equals the expected degree `d`, failing otherwise.

In practice, this means that if the goal is `nat_degree (X - X + 1 : ℤ[X]) = 0`, then
`compute_degree` gives an error, since there are terms of degree `1` in the expression
(the cancelling pair `X, -X`) and the tactic expects `1` to be the degree.  Note that this is not
an issue if the cancellation arises in terms of degrees smaller than the maximum:
```lean
example : nat_degree (X ^ 2 + X - X : ℤ[X]) = 2 := by compute_degree
```
works. -/
meta def compute_degree (silent : parse (tk "!" )?) : tactic unit :=
focus $ do
  t ← target >>= (λ f, whnf f reducible),
  match t with
  -- the `degree` match implicitly assumes that the `nat_degree` is strictly positive
  | `(    degree %%_ = %%n) :=
    refine ``((degree_eq_iff_nat_degree_eq_of_pos (by norm_num : 0 < _)).mpr _)
  | `(nat_degree %%_ = %%_) := do
    -- Try to solve the goal with a oneliner.
    -- If this succeeds, we close the goal in `compute_degree!` mode.
    -- In the normal `compute_degree` mode, we ask the user to use the oneliner instead.
    potential_suggestion ← try_core single_term_suggestions,
    match potential_suggestion with
    | some suggestion :=
      if silent.is_some then refine suggestion.2 -- Oneliner found: done!
      else (do -- Oneliner found: ask the user to try that instead.
        p_suggestion ← pp suggestion.1,
        fail!"Try this: exact {p_suggestion}\n\nor\n\nTry this: compute_degree!\n")
    | none := skip -- No oneliner found.
    end
  | _ := fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`"
  end;
  do `(nat_degree %%pol = %%degv) ← target |
      fail "Goal is not of the form\n`f.nat_degree = d` or `f.degree = d`",
  --  if we are trying to show that the degree is zero, we outsource to `compute_degree_le`
  unify degv `(0) >> refine ``(nat.eq_zero_of_le_zero _) >> compute_degree_le <|> do -- otherwise...
  deg ← guess_degree' pol,
  degvn ← eval_expr' ℕ degv,
  guard (deg = degvn) <|>
    ( do ppe ← pp deg, ppg ← pp degvn,
      fail sformat!("'{ppe}' is the expected degree\n'{ppg}' is the given degree\n") ),
  refine ``(le_antisymm _ (le_nat_degree_of_ne_zero _)),
  focus' [compute_degree_le, simp_lead_coeff []]

end parsing

/--  `prove_monic` tries to close goals of the form `monic f`.  It first determines a candidate
degree `d` for the polynomial `f`, using `tactic.compute_degree.guess_degree'`.  Next, it converts
the goal to showing that
* the degree of `f` is at most `d`, and using `compute_degree_le` to solve this goal;
* the coefficient of degree `d` equals `1`, and using `simp_lead_coeff` to simplify this goal.
If the term of largest degree appearing in `f` has non-zero coefficient (i.e., the terms of
highest degree do not cancel), then `prove_monic` should either succeed or leave
a simpler goal to prove.

An example of a polynomial where the current implementation of `prove_monic` fails is `X - X + 1`.
In this case, `prove_monic` tries to prove that the coefficient of `X` equals `1`, leaving a goal
of `1 - 1 = 1`, not realizing that the terms in `X` cancel out. -/
meta def prove_monic : tactic unit :=
focus $ do
  `(monic %%pol) ← target >>= (λ f, whnf f reducible) | fail"Goal is not of the form `monic f`",
  deg ← guess_degree' pol,
  deg ← to_expr deg.to_pexpr tt ff,
  refine ``(monic_of_nat_degree_le_of_coeff_eq_one %%deg _ _),
  focus' [compute_degree_le, simp_lead_coeff []],
  try reflexivity

add_tactic_doc
{ name := "compute_degree_le",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree_le],
  tags := ["arithmetic", "finishing"] }

add_tactic_doc
{ name := "simp_lead_coeff",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.simp_lead_coeff],
  tags := ["arithmetic", "finishing"] }

add_tactic_doc
{ name := "compute_degree",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.compute_degree],
  tags := ["arithmetic", "finishing"] }

add_tactic_doc
{ name := "prove_monic",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.prove_monic],
  tags := ["arithmetic", "finishing"] }

end interactive
end tactic
