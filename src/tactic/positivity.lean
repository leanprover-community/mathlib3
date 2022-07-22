/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import tactic.norm_num

/- # `positivity` tactic

The `positivity` tactic in this file solves goals of the form `0 ≤ x` and `0 < x`.  The tactic works
recursively according to the syntax of the expression `x`.  For example, a goal of the form
`0 ≤ 3 * a ^ 2 + b * c` can be solved either
* by a hypothesis such as `5 ≤ 3 * a ^ 2 + b * c` which directly implies the nonegativity of
  `3 * a ^ 2 + b * c`; or,
* by the application of the lemma `add_nonneg` and the success of the `positivity` tactic on the two
  sub-expressions `3 * a ^ 2` and `b * c`.

For each supported operation, one must write a small tactic, tagged with the attribute
`@[positivity]`, which operates only on goals whose leading function application is that operation.
Typically, this small tactic will run the full `positivity` tactic on one or more of the function's
arguments (which is where the recursion comes in), and if successful will combine this with an
appropriate lemma to give positivity of the full expression.

This file contains the core `positivity` logic and the small tactics handling the basic operations:
`min`, `max`, `+`, `*`, `/`, `⁻¹`, raising to natural powers, and taking absolute values.  Further
extensions, e.g. to handle `real.sqrt` and norms, can be found in the files of the library which
introduce these operations.

## Main declarations

* `tactic.positivity.base` is the base case of the recursion
* `tactic.positivity.attr` creates the `positivity` user attribute for tagging the extension tactics
  handling specific operations, and specifies the behaviour for a single step of the recursion
* `tactic.positivity.core` collects the list of tactics with the `@[positivity]` attribute and calls
  the first recursion step as specified in `tactic.positivity.attr`.  Its input is `e : expr` and
  its output (if it succeeds) is a pair `(bool, expr)`, with the `expr` a proof of the
  strict-positivity/nonnegativity of `e` and the `bool` indicating whether what could be proved was
  strict-positivity or nonnegativity
* `tactic.interactive.positivity` is the user-facing tactic.  It parses the goal and, if it is of
  one of the forms `0 ≤ e`, `0 < e`, `e > 0`, `e ≥ 0`, it sends `e` to `tactic.positivity.core`.

## TODO

Implement extensions for other operations (raising to non-numeral powers, `exp`, `log`, coercions
from `ℕ` and `ℝ≥0`).

-/

namespace tactic

/-- Given two tactics whose result is `bool × expr`, report a `bool × expr`:
- if at least one gives `tt`, report `tt` and one of the `tt` `expr`s
- if neither gives `tt` but at least one gives `ff`, report `ff` and one of the `ff` `expr`s
- if both fail, fail -/
meta def orelse' (tac1 tac2 : tactic (bool × expr)) : tactic (bool × expr) := do
  res ← try_core tac1,
  match res with
  | none := tac2
  | some res@(ff, _) := tac2 <|> pure res
  | some res@(tt, _) := pure res
  end

namespace positivity

/-! ### Core logic of the `positivity` tactic -/

private lemma lt_of_le_of_eq_of_lt {α} [preorder α] {a b b' c : α} :
  b = b' → a ≤ b' → b < c → a < c :=
λ h1 h2 h3, lt_of_le_of_lt (by rw h1; exact h2) h3

private lemma lt_of_lt_of_eq_of_le {α} [preorder α] {a b b' c : α} :
  b = b' → a < b' → b ≤ c → a < c :=
λ h1 h2 h3, lt_of_lt_of_le (by rw h1; exact h2) h3

private lemma le_of_eq_of_le'' {α} [preorder α] {a a' b : α} : a = a' → a ≤ b → a' ≤ b :=
λ h1 h2, le_of_eq_of_le h1.symm h2

private lemma lt_of_lt_of_eq'' {α} [preorder α] {b b' a : α} : b = b' → a < b' → a < b :=
λ h1 h2, lt_of_lt_of_eq h2 h1.symm

/-- Base case of the recursive tactic `positivity`. It proves an expression `e` is
positive/nonnegative either by `norm_num` directly on `e`, or by finding a hypothesis of the form
`a < e` or `a ≤ e` in which `a` can be proved positive/nonnegative by `norm_num`. -/
meta def base (e : expr) : tactic (bool × expr) :=
orelse' (do -- try `norm_num` to prove the goal positive directly
  (e', p) ← norm_num.derive e <|> refl_conv e,
  e'' ← e'.to_rat,
  typ ← infer_type e',
  ic ← mk_instance_cache typ,
  if e'' > 0 then do
    (ic, p₁) ← norm_num.prove_pos ic e',
    p ← mk_app ``lt_of_lt_of_eq'' [p, p₁],
    pure (tt, p)
  else if e'' = 0 then do
    p' ← mk_app ``ge_of_eq [p], -- check this lemma is the right one!
    pure (ff, p')
  else failed) $ -- loop over hypotheses
  local_context >>= list.foldl (λ tac p₃,
    orelse' tac $ do -- if RHS of the hypothesis is the object whose positivity is sought, try
    -- `norm_num` to prove positivity of the LHS and then apply transitivity
      p_typ ← infer_type p₃,
      (lo, hi, strict) ← match p_typ with
      | `(%%lo ≤ %%hi) := pure (lo, hi, ff)
      | `(%%hi ≥ %%lo) := pure (lo, hi, ff)
      | `(%%lo < %%hi) := pure (lo, hi, tt)
      | `(%%hi > %%lo) := pure (lo, hi, tt)
      | _ := failed
      end,
      is_def_eq e hi,
      (lo', p₂) ← norm_num.derive lo <|> refl_conv lo,
      typ ← infer_type lo',
      ic ← mk_instance_cache typ,
      if strict then do
        (ic, p₁) ← norm_num.prove_nonneg ic lo',
        p ← mk_app ``lt_of_le_of_eq_of_lt [p₂, p₁, p₃],
        pure (tt, p)
      else do
        z ← mk_mapp ``has_zero.zero [some typ, none], -- there was a way to get from instance cache?
        if lo' = z then do
          p ← mk_app ``le_of_eq_of_le'' [p₂, p₃],
          pure (ff, p)
        else do
          (ic, p₁) ← norm_num.prove_pos ic lo',
          p ← mk_app ``lt_of_lt_of_eq_of_le [p₂, p₁, p₃],
          pure (tt, p)) failed

/-- Attribute allowing a user to tag a tactic as an extension for the `positivity` tactic.  The main
(recursive) step of the `positivity` tactic is to try successively all the `positivity` extensions
on the goal, and also to try `tactic.positivity.base` on the goal. -/
@[user_attribute]
meta def attr : user_attribute (expr → tactic (bool × expr)) unit :=
{ name      := `positivity,
  descr     := "extensions handling particular operations for the `positivity` tactic",
  cache_cfg :=
  { mk_cache := λ ns, do
    { t ← ns.mfoldl
        (λ (t : expr → tactic (bool × expr)) n, do
          t' ← eval_expr (expr → tactic (bool × expr)) (expr.const n []),
          pure (λ e, orelse' (t' e) (t e)))
        (λ _, failed),
      pure (λ e, orelse' (base e) (t e)) },
    dependencies := [] } }

/-- Look for a proof of positivity/nonnegativity of an expression `e`; if found, return the proof
together with a boolean stating whether the proof found was for strict positivity (`tt`) or only
for nonnegativity (`ff`). -/
meta def core (e : expr) : tactic (bool × expr) := do
  f ← attr.get_cache,
  f e <|> fail "failed to prove positivity/nonnegativity"

end positivity

namespace interactive

setup_tactic_parser

/-- Tactic solving goals of the form `0 ≤ x` and `0 < x`.  The tactic works recursively according to
the syntax of the expression `x`, if the atoms composing the expression all have numeric lower
bounds which can be proved positive/nonnegative by `norm_num`.  This tactic either closes the goal
or fails. -/
meta def positivity : tactic unit := focus1 $ do
  t ← target,
  (a, strict_desired) ← match t with
  | `(0 ≤ %%e₂) := pure (e₂, ff)
  | `(%%e₂ ≥ 0) := pure (e₂, ff)
  | `(0 < %%e₂) := pure (e₂, tt)
  | `(%%e₂ > 0) := pure (e₂, tt)
  | _ := fail "not a positivity/nonnegativity goal"
  end,
  (strict_proved, p) ← tactic.positivity.core a,
  match strict_desired, strict_proved with
  | tt, ff := fail "failed to prove strict positivity, but it would be possible to prove nonnegativity if desired"
  | ff, tt := mk_app ``le_of_lt [p]
  | _, _ := pure p
  end >>= tactic.exact

end interactive

open positivity

variables {R : Type*}

/-! ### `positivity` extensions for particular arithmetic operations -/

private lemma le_min_of_lt_of_le [linear_order R] (a b c : R) (ha : a < b) (hb : a ≤ c) :
  a ≤ min b c :=
le_min ha.le hb

private lemma le_min_of_le_of_lt [linear_order R] (a b c : R) (ha : a ≤ b) (hb : a < c) :
  a ≤ min b c :=
le_min ha hb.le

/-- Extension for the `positivity` tactic: the `min` of two numbers is nonnegative if both are
nonnegative, and strictly positive if both are. -/
@[positivity]
meta def positivity_min : expr → tactic (bool × expr)
| `(min %%a %%b) := do
  (strict_a, pa) ← core a,
  (strict_b, pb) ← core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``lt_min [pa, pb]
  | tt, ff := prod.mk ff <$> mk_app ``le_min_of_lt_of_le [pa, pb]
  | ff, tt := prod.mk ff <$> mk_app ``le_min_of_le_of_lt [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``le_min [pa, pb]
  end
| _ := failed

/-- Extension for the `positivity` tactic: the `max` of two numbers is nonnegative if at least one
is nonnegative, and strictly positive if at least one is positive. -/
@[positivity]
meta def positivity_max : expr → tactic (bool × expr)
| `(max %%a %%b) := orelse' (do
      (strict_a, pa) ← core a,
      if strict_a then
        prod.mk tt <$> mk_mapp ``lt_max_of_lt_left [none, none, none, a, b, pa]
      else
        prod.mk ff <$> mk_mapp ``le_max_of_le_left [none, none, none, a, b, pa])
  (do
    (strict_b, pb) ← core b,
    if strict_b then
      prod.mk tt <$> mk_mapp ``lt_max_of_lt_right [none, none, none, a, b, pb]
    else do
      prod.mk ff <$> mk_mapp ``le_max_of_le_right [none, none, none, a, b, pb])
| _ := failed

/-- Extension for the `positivity` tactic: addition is nonnegative if both summands are nonnegative,
and strictly positive if at least one summand is. -/
@[positivity]
meta def positivity_add : expr → tactic (bool × expr)
| `(%%a + %%b) := do
  (strict_a, pa) ← core a,
  (strict_b, pb) ← core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``add_pos [pa, pb]
  | tt, ff := prod.mk tt <$> mk_app ``lt_add_of_pos_of_le [pa, pb]
  | ff, tt := prod.mk tt <$> mk_app ``lt_add_of_le_of_pos [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``add_nonneg [pa, pb]
  end
| _ := failed

private lemma mul_nonneg_of_pos_of_nonneg [linear_ordered_semiring R] (a b : R) (ha : 0 < a)
  (hb : 0 ≤ b) :
  0 ≤ a * b :=
mul_nonneg ha.le hb

private lemma mul_nonneg_of_nonneg_of_pos [linear_ordered_semiring R] (a b : R) (ha : 0 ≤ a)
  (hb : 0 < b) :
  0 ≤ a * b :=
mul_nonneg ha hb.le

/-- Extension for the `positivity` tactic: multiplication is nonnegative if both multiplicands are
nonnegative, and strictly positive if both multiplicands are. -/
@[positivity]
meta def positivity_mul : expr → tactic (bool × expr)
| `(%%a * %%b) := do
  (strict_a, pa) ← core a,
  (strict_b, pb) ← core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``mul_pos [pa, pb]
  | tt, ff := prod.mk ff <$> mk_app ``mul_nonneg_of_pos_of_nonneg [pa, pb]
  | ff, tt := prod.mk ff <$> mk_app ``mul_nonneg_of_nonneg_of_pos [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``mul_nonneg [pa, pb]
  end
| _ := failed

private lemma div_nonneg_of_pos_of_nonneg [linear_ordered_field R] {a b : R} (ha : 0 < a)
  (hb : 0 ≤ b) :
  0 ≤ a / b :=
div_nonneg ha.le hb

private lemma div_nonneg_of_nonneg_of_pos [linear_ordered_field R] {a b : R} (ha : 0 ≤ a)
  (hb : 0 < b) :
  0 ≤ a / b :=
div_nonneg ha hb.le

/-- Extension for the `positivity` tactic: division is nonnegative if both numerator and denominator
are nonnegative, and strictly positive if both numerator and denominator are. -/
@[positivity]
meta def positivity_div : expr → tactic (bool × expr)
| `(%%a / %%b) := do
  (strict_a, pa) ← core a,
  (strict_b, pb) ← core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``div_pos [pa, pb]
  | tt, ff := prod.mk ff <$> mk_app ``div_nonneg_of_pos_of_nonneg [pa, pb]
  | ff, tt := prod.mk ff <$> mk_app ``div_nonneg_of_nonneg_of_pos [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``div_nonneg [pa, pb] -- TODO handle eg `int.div_nonneg`
  end
| _ := failed

alias inv_pos ↔ _ inv_pos_of_pos
alias inv_nonneg ↔ _ inv_nonneg_of_nonneg

/-- Extension for the `positivity` tactic: an inverse of a positive number is positive, an inverse
of a nonnegative number is nonnegative. -/
@[positivity]
meta def positivity_inv : expr → tactic (bool × expr)
| `((%%a)⁻¹) := do
    (strict_a, pa) ← core a,
    if strict_a then
      prod.mk tt <$> mk_app ``inv_pos_of_pos [pa]
    else
      prod.mk ff <$> mk_app ``inv_nonneg_of_nonneg [pa]
| _ := failed

private lemma pow_zero_pos [ordered_semiring R] [nontrivial R] (a : R) : 0 < a ^ 0 :=
zero_lt_one.trans_le (pow_zero a).ge

/-- Extension for the `positivity` tactic: raising a number `a` to a natural number power `n` is
known to be positive if `n = 0` (since `a ^ 0 = 1`) or if `0 < a`, and is known to be nonnegative if
`n = 2` (squares are nonnegative) or if `0 ≤ a`. -/
@[positivity]
meta def positivity_pow : expr → tactic (bool × expr)
| `(%%a ^ %%n) := do
  n_typ ← infer_type n,
  match n_typ with
  | `(ℕ) := do
    if n = `(0) then do
      prod.mk tt <$> mk_app ``pow_zero_pos [a]
    else orelse' (do
      -- squares are nonnegative (TODO: similar for any `bit0` exponent?)
      prod.mk ff <$> mk_app ``sq_nonneg [a])
      -- moreover `a ^ n` is positive if `a` is and nonnegative if `a` is
      (do
        (strict_a, pa) ← core a,
        if strict_a then
          prod.mk tt <$> mk_app ``pow_pos [pa, n]
        else
          prod.mk ff <$> mk_app ``pow_nonneg [pa, n])
  | _ := failed -- TODO handle integer powers, maybe even real powers
  end
| _ := failed

/-- Extension for the `positivity` tactic: an absolute value is nonnegative, and is strictly
positive if its input is. -/
@[positivity]
meta def positivity_abs : expr → tactic (bool × expr)
| `(|%%a|) := do
  (do -- if can prove `0 < a`, report positivity
    (strict_a, pa) ← core a,
    prod.mk tt <$> mk_app ``abs_pos_of_pos [pa]) <|>
  prod.mk ff <$> mk_app ``abs_nonneg [a] -- else report nonnegativity
| _ := failed

end tactic
