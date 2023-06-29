/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
import tactic.norm_num
import algebra.order.field.power
import algebra.order.hom.basic
import data.nat.factorial.basic

/-! # `positivity` tactic

The `positivity` tactic in this file solves goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The
tactic works recursively according to the syntax of the expression `x`.  For example, a goal of the
form `0 ≤ 3 * a ^ 2 + b * c` can be solved either
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

* `tactic.norm_num.positivity` tries to prove positivity of an expression by running `norm_num` on
  it.  This is one of the base cases of the recursion.
* `tactic.positivity.compare_hyp` tries to prove positivity of an expression by comparing with a
  provided hypothesis.  If the hypothesis is of the form `a ≤ b` or similar, with `b` matching the
  expression whose proof of positivity is desired, then it will check whether `a` can be proved
  positive via `tactic.norm_num.positivity` and if so apply a transitivity lemma.  This is the other
  base case of the recursion.
* `tactic.positivity.attr` creates the `positivity` user attribute for tagging the extension
  tactics handling specific operations, and specifies the behaviour for a single step of the
  recursion
* `tactic.positivity.core` collects the list of tactics with the `@[positivity]` attribute and
  calls the first recursion step as specified in `tactic.positivity.attr`.  Its input is `e : expr`
  and its output (if it succeeds) is a term of a custom inductive type
  `tactic.positivity.strictness`, containing an `expr` which is a proof of the
  strict-positivity/nonnegativity of `e` as well as an indication of whether what could be proved
  was strict-positivity or nonnegativity
* `tactic.positivity.order_rel` is a custom inductive type recording whether the goal is
  `0 ≤ e`/`e ≥ 0`, `0 < e`/`e > 0`, `e ≠ 0` or `0 ≠ e`.
* `tactic.interactive.positivity` is the user-facing tactic.  It parses the goal and, if it is of
  one of the forms `0 ≤ e`, `0 < e`, `e > 0`, `e ≥ 0`, `e ≠ 0`, `0 ≠ e`, it sends `e` to
  `tactic.positivity.core`.

## TODO

Implement extensions for other operations (raising to non-numeral powers, `log`).
-/

namespace tactic

/-- Inductive type recording either `positive` and an expression (typically a proof of a fact
`0 < x`) or `nonnegative` and an expression (typically a proof of a fact `0 ≤ x`). -/
@[derive [decidable_eq]]
meta inductive positivity.strictness : Type
| positive : expr → positivity.strictness
| nonnegative : expr → positivity.strictness
| nonzero : expr → positivity.strictness

export positivity.strictness (positive nonnegative nonzero)

meta instance : has_to_string strictness :=
⟨λ s, match s with
  | positive p := "strictness.positive (" ++ to_string p ++ ")"
  | nonnegative p := "strictness.nonnegative (" ++ to_string p ++ ")"
  | nonzero p := "strictness.nonzero (" ++ to_string p ++ ")"
  end⟩

meta instance : has_to_format strictness := ⟨λ s, to_string s⟩

private lemma lt_of_eq_of_lt'' {α} [preorder α] {b b' a : α} : b = b' → a < b' → a < b :=
λ h1 h2, lt_of_lt_of_eq h2 h1.symm

/-- First base case of the `positivity` tactic.  We try `norm_num` to prove directly that an
expression `e` is positive, nonnegative or non-zero. -/
meta def norm_num.positivity (e : expr) : tactic strictness := do
  (e', p) ← norm_num.derive e <|> refl_conv e,
  e'' ← e'.to_rat,
  typ ← infer_type e',
  ic ← mk_instance_cache typ,
  if e'' > 0 then do
    (ic, p₁) ← norm_num.prove_pos ic e',
    positive <$> mk_app ``lt_of_eq_of_lt'' [p, p₁]
  else if e'' = 0 then
    nonnegative <$> mk_app ``ge_of_eq [p]
  else do
    (ic, p₁) ← norm_num.prove_ne_zero' ic e',
    nonzero <$> to_expr ``(ne_of_eq_of_ne %%p %%p₁)

/-- Second base case of the `positivity` tactic: Any element of a canonically ordered additive
monoid is nonnegative. -/
meta def positivity_canon : expr → tactic strictness
| `(%%a) := nonnegative <$> mk_app ``zero_le [a]

namespace positivity

/-- Inductive type recording whether the goal `positivity` is called on is nonnegativity, positivity
or different from `0`. -/
@[derive inhabited]
inductive order_rel : Type
| le  : order_rel -- `0 ≤ a`
| lt  : order_rel -- `0 < a`
| ne  : order_rel -- `a ≠ 0`
| ne' : order_rel -- `0 ≠ a`

meta instance : has_to_format order_rel :=
⟨λ r, match r with
  | order_rel.le := "order_rel.le"
  | order_rel.lt := "order_rel.lt"
  | order_rel.ne := "order_rel.ne"
  | order_rel.ne' := "order_rel.ne'"
  end⟩

/-- Given two tactics whose result is `strictness`, report a `strictness`:
- if at least one gives `positive`, report `positive` and one of the expressions giving a proof of
  positivity
- if one reports `nonnegative` and the other reports `nonzero`, report `positive`
- else if at least one reports `nonnegative`, report `nonnegative` and one of the
  expressions giving a proof of nonnegativity
- else if at least one reports `nonzero`, report `nonzero` and one of the expressions giving a proof
  of nonzeroness
- if both fail, fail -/
protected meta def orelse (tac1 tac2 : tactic strictness) : tactic strictness := do
  res1 ← try_core tac1,
  match res1 with
  | none := tac2
  | some p1@(positive _) := pure p1
  | some (nonnegative e1) := do
      res2 ← try_core tac2,
      match res2 with
      | some p2@(positive _) := pure p2
      | some (nonzero e2) := positive <$> mk_app ``lt_of_le_of_ne' [e1, e2]
      | _ := pure (nonnegative e1)
      end
  | some (nonzero e1) := do
      res2 ← try_core tac2,
      match res2 with
      | some p2@(positive _) := pure p2
      | some (nonnegative e2) := positive <$> mk_app ``lt_of_le_of_ne' [e2, e1]
      | _ := pure (nonzero e1)
      end
  end

localized "infixr ` ≤|≥ `:2 := tactic.positivity.orelse" in positivity

/-- This tactic fails with a message saying that `positivity` couldn't prove anything about `e`
if we only know that `a` and `b` are positive/nonnegative/nonzero (according to `pa` and `pb`). -/
meta def positivity_fail {α : Type*} (e a b : expr) (pa pb : strictness) : tactic α :=
do
  e' ← pp e,
  a' ← pp a,
  b' ← pp b,
  let f : strictness → format → format := λ p c, match p with
  | positive _ := "0 < " ++ c
  | nonnegative _ := "0 ≤ " ++ c
  | nonzero _ := c ++ " ≠ 0"
  end,
  fail (↑"`positivity` can't say anything about `" ++ e' ++ "` knowing only `" ++ f pa a' ++
    "` and `" ++ f pb b' ++ "`")

/-! ### Core logic of the `positivity` tactic -/

private lemma ne_of_ne_of_eq' {α : Type*} {a b c : α} (ha : a ≠ c) (h : a = b) : b ≠ c := by rwa ←h

/-- Calls `norm_num` on `a` to prove positivity/nonnegativity of `e` assuming `b` is defeq to `e`
and `p₂ : a ≤ b`. -/
meta def compare_hyp_le (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b,
  strict_a ← norm_num.positivity a,
  match strict_a with
  | positive p₁ := positive <$> mk_app ``lt_of_lt_of_le [p₁, p₂]
  | nonnegative p₁ := nonnegative <$> mk_app ``le_trans [p₁, p₂]
  | _ := do
          e' ← pp e,
          p₂' ← pp p₂,
          fail (↑"`norm_num` can't prove nonnegativity of " ++ e' ++ " using " ++ p₂')
  end

/-- Calls `norm_num` on `a` to prove positivity/nonnegativity of `e` assuming `b` is defeq to `e`
and `p₂ : a < b`. -/
meta def compare_hyp_lt (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b,
  strict_a ← norm_num.positivity a,
  match strict_a with
  | positive p₁ := positive <$> mk_app ``lt_trans [p₁, p₂]
  | nonnegative p₁ := positive <$> mk_app ``lt_of_le_of_lt [p₁, p₂]
  | _ := do
          e' ← pp e,
          p₂' ← pp p₂,
          fail (↑"`norm_num` can't prove positivity of " ++ e' ++ " using " ++ p₂')
  end

/-- Calls `norm_num` on `a` to prove positivity/nonnegativity/nonzeroness of `e` assuming `b` is
defeq to `e` and `p₂ : a = b`. -/
meta def compare_hyp_eq (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b,
  strict_a ← norm_num.positivity a,
  match strict_a with
  | positive p₁ := positive <$> mk_app ``lt_of_lt_of_eq [p₁, p₂]
  | nonnegative p₁ := nonnegative <$> mk_app ``le_of_le_of_eq [p₁, p₂]
  | nonzero p₁ := nonzero <$> to_expr ``(ne_of_ne_of_eq' %%p₁ %%p₂)
  end

/-- Calls `norm_num` on `a` to prove nonzeroness of `e` assuming `b` is defeq to `e` and
`p₂ : b ≠ a`. -/
meta def compare_hyp_ne (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b,
  (a', p₁) ← norm_num.derive a <|> refl_conv a,
  a'' ← a'.to_rat,
  if a'' = 0 then
    nonzero <$> mk_mapp ``ne_of_ne_of_eq [none, none, none, none, p₂, p₁]
  else do
    e' ← pp e,
    p₂' ← pp p₂,
    a' ← pp a,
    fail (↑"`norm_num` can't prove non-zeroness of " ++ e' ++ " using " ++ p₂' ++ " because "
      ++ a' ++ " is non-zero")

/-- Third base case of the `positivity` tactic.  Prove an expression `e` is
positive/nonnegative/nonzero by finding a hypothesis of the form `a < e`, `a ≤ e` or `a = e` in
which `a` can be proved positive/nonnegative/nonzero by `norm_num`. -/
meta def compare_hyp (e p₂ : expr) : tactic strictness := do
  p_typ ← infer_type p₂,
  match p_typ with
  | `(%%lo ≤ %%hi) := compare_hyp_le e lo hi p₂
  | `(%%hi ≥ %%lo) := compare_hyp_le e lo hi p₂
  | `(%%lo < %%hi) := compare_hyp_lt e lo hi p₂
  | `(%%hi > %%lo) := compare_hyp_lt e lo hi p₂
  | `(%%lo = %%hi) := compare_hyp_eq e lo hi p₂ <|> do
                        p₂' ← mk_app ``eq.symm [p₂],
                        compare_hyp_eq e hi lo p₂'
  | `(%%hi ≠ %%lo) := compare_hyp_ne e lo hi p₂ <|> do
                        p₂' ← mk_mapp ``ne.symm [none, none, none, p₂],
                        compare_hyp_ne e hi lo p₂'
  | e := do
             p₂' ← pp p₂,
             fail (p₂' ++ "is not of the form `a ≤ b`, `a < b`, `a = b` or `a ≠ b`")
  end

/-- Attribute allowing a user to tag a tactic as an extension for `tactic.interactive.positivity`.
The main (recursive) step of this tactic is to try successively all the extensions tagged with this
attribute on the expression at hand, and also to try the two "base case" tactics
`tactic.norm_num.positivity`, `tactic.positivity.compare_hyp` on the expression at hand. -/
@[user_attribute]
meta def attr : user_attribute (expr → tactic strictness) unit :=
{ name      := `positivity,
  descr     := "extensions handling particular operations for the `positivity` tactic",
  cache_cfg :=
  { mk_cache := λ ns, do
    { t ← ns.mfoldl
        (λ (t : expr → tactic strictness) n, do
          t' ← eval_expr (expr → tactic strictness) (expr.const n []),
          pure (λ e, t' e ≤|≥ t e))
        (λ _, failed),
      pure $ λ e,
            t e -- run all the extensions on `e`
        ≤|≥ norm_num.positivity e -- directly try `norm_num` on `e`
        ≤|≥ positivity_canon e -- try showing nonnegativity from canonicity of the order
            -- loop over hypotheses and try to compare with `e`
        ≤|≥ local_context >>= list.foldl (λ tac h, tac ≤|≥ compare_hyp e h)
              (fail "no applicable positivity extension found") },
    dependencies := [] } }

/-- Look for a proof of positivity/nonnegativity of an expression `e`; if found, return the proof
together with a `strictness` stating whether the proof found was for strict positivity
(`positive p`), nonnegativity (`nonnegative p`), or nonzeroness (`nonzero p`). -/
meta def core (e : expr) : tactic strictness := do
  f ← attr.get_cache,
  f e <|> fail "failed to prove positivity/nonnegativity/nonzeroness"

end positivity

open positivity
open_locale positivity

namespace interactive

setup_tactic_parser

/-- Tactic solving goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The tactic works recursively
according to the syntax of the expression `x`, if the atoms composing the expression all have
numeric lower bounds which can be proved positive/nonnegative/nonzero by `norm_num`.  This tactic
either closes the goal or fails.

Examples:
```
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity
```
-/
meta def positivity : tactic unit := focus1 $ do
  t ← target >>= instantiate_mvars,
  (rel_desired, a) ← match t with
  | `(0 ≤ %%e) := pure (order_rel.le, e)
  | `(%%e ≥ 0) := pure (order_rel.le, e)
  | `(0 < %%e) := pure (order_rel.lt, e)
  | `(%%e > 0) := pure (order_rel.lt, e)
  | `(%%e₁ ≠ %%e₂) := do
                        match e₂ with
                        | `(has_zero.zero) := pure (order_rel.ne, e₁)
                        | _ := match e₁ with
                          | `(has_zero.zero) := pure (order_rel.ne', e₂)
                          | _ := fail "not a positivity/nonnegativity/nonzeroness goal"
                          end
                        end
  | _ := fail "not a positivity/nonnegativity/nonzeroness goal"
  end,
  strictness_proved ← tactic.positivity.core a,
  match rel_desired, strictness_proved with
  | order_rel.lt, positive p := pure p
  | order_rel.lt, nonnegative _ := fail ("failed to prove strict positivity, but it would be " ++
    "possible to prove nonnegativity if desired")
  | order_rel.lt, nonzero _ := fail ("failed to prove strict positivity, but it would be " ++
    "possible to prove nonzeroness if desired")
  | order_rel.le, positive p := mk_app ``le_of_lt [p]
  | order_rel.le, nonnegative p := pure p
  | order_rel.le, nonzero _ := fail ("failed to prove nonnegativity, but it would be " ++
    "possible to prove nonzeroness if desired")
  | order_rel.ne, positive p := to_expr ``(ne_of_gt %%p)
  | order_rel.ne, nonnegative _ := fail ("failed to prove nonzeroness, but it would be " ++
    "possible to prove nonnegativity if desired")
  | order_rel.ne, nonzero p := pure p
  | order_rel.ne', positive p := to_expr ``(ne_of_lt %%p)
  | order_rel.ne', nonnegative _ := fail ("failed to prove nonzeroness, but it would be " ++
    "possible to prove nonnegativity if desired")
  | order_rel.ne', nonzero p := to_expr ``(ne.symm %%p)
  end >>= tactic.exact

add_tactic_doc
{ name := "positivity",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.positivity],
  tags := ["arithmetic", "monotonicity", "finishing"] }

end interactive

variables {ι α R : Type*}

/-! ### `positivity` extensions for particular arithmetic operations -/

section linear_order
variables [linear_order R] {a b c : R}

private lemma le_min_of_lt_of_le  (ha : a < b) (hb : a ≤ c) : a ≤ min b c := le_min ha.le hb
private lemma le_min_of_le_of_lt (ha : a ≤ b) (hb : a < c) : a ≤ min b c := le_min ha hb.le
private lemma min_ne (ha : a ≠ c) (hb : b ≠ c) : min a b ≠ c :=
by { rw min_def, split_ifs; assumption }
private lemma min_ne_of_ne_of_lt (ha : a ≠ c) (hb : c < b) : min a b ≠ c := min_ne ha hb.ne'
private lemma min_ne_of_lt_of_ne (ha : c < a) (hb : b ≠ c) : min a b ≠ c := min_ne ha.ne' hb

private lemma max_ne (ha : a ≠ c) (hb : b ≠ c) : max a b ≠ c :=
by { rw max_def, split_ifs; assumption }

end linear_order

/-- Extension for the `positivity` tactic: the `min` of two numbers is nonnegative if both are
nonnegative, and strictly positive if both are. -/
@[positivity]
meta def positivity_min : expr → tactic strictness
| e@`(min %%a %%b) := do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | (positive pa), (positive pb) := positive <$> mk_app ``lt_min [pa, pb]
  | (positive pa), (nonnegative pb) := nonnegative <$> mk_app ``le_min_of_lt_of_le [pa, pb]
  | (nonnegative pa), (positive pb)  := nonnegative <$> mk_app ``le_min_of_le_of_lt [pa, pb]
  | (nonnegative pa), (nonnegative pb)  := nonnegative <$> mk_app ``le_min [pa, pb]
  | positive pa, nonzero pb := nonzero <$> to_expr ``(min_ne_of_lt_of_ne %%pa %%pb)
  | nonzero pa, positive pb := nonzero <$> to_expr ``(min_ne_of_ne_of_lt %%pa %%pb)
  | nonzero pa, nonzero pb := nonzero <$> to_expr ``(min_ne %%pa %%pb)
  | sa@_, sb@ _ := positivity_fail e a b sa sb
  end
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `min a b`"

/-- Extension for the `positivity` tactic: the `max` of two numbers is nonnegative if at least one
is nonnegative, strictly positive if at least one is positive, and nonzero if both are nonzero. -/
@[positivity]
meta def positivity_max : expr → tactic strictness
| `(max %%a %%b) := do
  strictness_a ← try_core (core a),
  (do
      match strictness_a with
      | some (positive pa) := positive <$> mk_mapp ``lt_max_of_lt_left [none, none, none, a, b, pa]
      | some (nonnegative pa) :=
          nonnegative <$> mk_mapp ``le_max_of_le_left [none, none, none, a, b, pa]
      | _ := failed
        -- If `a ≠ 0`, we might prove `max a b ≠ 0` if `b ≠ 0` but we don't want to evaluate
        -- `b` before having ruled out `0 < a`, for performance. So we do that in the second branch
        -- of the `orelse'`.
      end) ≤|≥
    (do
      strictness_b ← core b,
      match strictness_b with
      | (positive pb) := positive <$> mk_mapp ``lt_max_of_lt_right [none, none, none, a, b, pb]
      | (nonnegative pb) :=
          nonnegative <$> mk_mapp ``le_max_of_le_right [none, none, none, a, b, pb]
      | nonzero pb := do
                        nonzero pa ← strictness_a,
                        nonzero <$> to_expr ``(max_ne %%pa %%pb)
      end)
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `max a b`"

/-- Extension for the `positivity` tactic: addition is nonnegative if both summands are nonnegative,
and strictly positive if at least one summand is. -/
@[positivity]
meta def positivity_add : expr → tactic strictness
| e@`(%%a + %%b) := do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | (positive pa), (positive pb) := positive <$> mk_app ``add_pos [pa, pb]
  | (positive pa), (nonnegative pb) := positive <$> mk_app ``lt_add_of_pos_of_le [pa, pb]
  | (nonnegative pa), (positive pb) := positive <$> mk_app ``lt_add_of_le_of_pos [pa, pb]
  | (nonnegative pa), (nonnegative pb) := nonnegative <$> mk_app ``add_nonneg [pa, pb]
  | sa@_, sb@ _ := positivity_fail e a b sa sb
  end
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a + b`"

section ordered_semiring
variables [ordered_semiring R] {a b : R}

private lemma mul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b :=
mul_nonneg ha.le hb

private lemma mul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b :=
mul_nonneg ha hb.le

private lemma mul_ne_zero_of_pos_of_ne_zero [no_zero_divisors R] (ha : 0 < a) (hb : b ≠ 0) :
  a * b ≠ 0 :=
mul_ne_zero ha.ne' hb

private lemma mul_ne_zero_of_ne_zero_of_pos [no_zero_divisors R] (ha : a ≠ 0) (hb : 0 < b) :
  a * b ≠ 0 :=
mul_ne_zero ha hb.ne'

end ordered_semiring

/-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
multiplicands are. -/
@[positivity]
meta def positivity_mul : expr → tactic strictness
| e@`(%%a * %%b) := do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | (positive pa), (positive pb) := positive <$> mk_app ``mul_pos [pa, pb]
  | (positive pa), (nonnegative pb) := nonnegative <$> mk_app ``mul_nonneg_of_pos_of_nonneg [pa, pb]
  | (nonnegative pa), (positive pb) := nonnegative <$> mk_app ``mul_nonneg_of_nonneg_of_pos [pa, pb]
  | (nonnegative pa), (nonnegative pb) := nonnegative <$> mk_app ``mul_nonneg [pa, pb]
  | positive pa, nonzero pb := nonzero <$> to_expr ``(mul_ne_zero_of_pos_of_ne_zero %%pa %%pb)
  | nonzero pa, positive pb := nonzero <$> to_expr ``(mul_ne_zero_of_ne_zero_of_pos %%pa %%pb)
  | nonzero pa, nonzero pb := nonzero <$> to_expr ``(mul_ne_zero %%pa %%pb)
  | sa@_, sb@ _ := positivity_fail e a b sa sb
  end
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a * b`"

section linear_ordered_semifield
variables [linear_ordered_semifield R] {a b : R}

private lemma div_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
div_nonneg ha.le hb

private lemma div_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
div_nonneg ha hb.le

private lemma div_ne_zero_of_pos_of_ne_zero (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 :=
div_ne_zero ha.ne' hb

private lemma div_ne_zero_of_ne_zero_of_pos (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 :=
div_ne_zero ha hb.ne'

end linear_ordered_semifield

private lemma int_div_self_pos {a : ℤ} (ha : 0 < a) : 0 < a / a :=
by { rw int.div_self ha.ne', exact zero_lt_one }

private lemma int_div_nonneg_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
int.div_nonneg ha.le hb

private lemma int_div_nonneg_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
int.div_nonneg ha hb.le

private lemma int_div_nonneg_of_pos_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b :=
int.div_nonneg ha.le hb.le

/-- Extension for the `positivity` tactic: division is nonnegative if both numerator and denominator
are nonnegative, and strictly positive if both numerator and denominator are. -/
@[positivity]
meta def positivity_div : expr → tactic strictness
| e@`(@has_div.div ℤ _ %%a %%b) := do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | positive pa, positive pb :=
      if a = b then -- Only attempts to prove `0 < a / a`, otherwise falls back to `0 ≤ a / b`
        positive <$> mk_app ``int_div_self_pos [pa]
      else
       nonnegative <$> mk_app ``int_div_nonneg_of_pos_of_pos [pa, pb]
  | positive pa, nonnegative pb :=
    nonnegative <$> mk_app ``int_div_nonneg_of_pos_of_nonneg [pa, pb]
  | nonnegative pa, positive pb :=
    nonnegative <$> mk_app ``int_div_nonneg_of_nonneg_of_pos [pa, pb]
  | nonnegative pa, nonnegative pb := nonnegative <$> mk_app ``int.div_nonneg [pa, pb]
  | sa@_, sb@ _ := positivity_fail e a b sa sb
  end
| e@`(%%a / %%b) := do
  strictness_a ← core a,
  strictness_b ← core b,
  match strictness_a, strictness_b with
  | positive pa, positive pb := positive <$> mk_app ``div_pos [pa, pb]
  | positive pa, nonnegative pb := nonnegative <$> mk_app ``div_nonneg_of_pos_of_nonneg [pa, pb]
  | nonnegative pa, positive pb := nonnegative <$> mk_app ``div_nonneg_of_nonneg_of_pos [pa, pb]
  | nonnegative pa, nonnegative pb := nonnegative <$> mk_app ``div_nonneg [pa, pb]
  | positive pa, nonzero pb := nonzero <$> to_expr ``(div_ne_zero_of_pos_of_ne_zero %%pa %%pb)
  | nonzero pa, positive pb := nonzero <$> to_expr ``(div_ne_zero_of_ne_zero_of_pos %%pa %%pb)
  | nonzero pa, nonzero pb := nonzero <$> to_expr ``(div_ne_zero %%pa %%pb)
  | sa@_, sb@ _ := positivity_fail e a b sa sb
  end
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a / b`"

/-- Extension for the `positivity` tactic: an inverse of a positive number is positive, an inverse
of a nonnegative number is nonnegative. -/
@[positivity]
meta def positivity_inv : expr → tactic strictness
| `((%%a)⁻¹) := do
      strictness_a ← core a,
      match strictness_a with
      | (positive pa) := positive <$> mk_app ``inv_pos_of_pos [pa]
      | (nonnegative pa) := nonnegative <$> mk_app ``inv_nonneg_of_nonneg [pa]
      | nonzero pa := nonzero <$> to_expr ``(inv_ne_zero %%pa)
      end
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a⁻¹`"

private lemma pow_zero_pos [ordered_semiring R] [nontrivial R] (a : R) : 0 < a ^ 0 :=
zero_lt_one.trans_le (pow_zero a).ge

private lemma zpow_zero_pos [linear_ordered_semifield R] (a : R) : 0 < a ^ (0 : ℤ) :=
zero_lt_one.trans_le (zpow_zero a).ge

/-- Extension for the `positivity` tactic: raising a number `a` to a natural/integer power `n` is
positive if `n = 0` (since `a ^ 0 = 1`) or if `0 < a`, and is nonnegative if `n` is even (squares
are nonnegative) or if `0 ≤ a`. -/
@[positivity]
meta def positivity_pow : expr → tactic strictness
| e@`(%%a ^ %%n) := do
  typ ← infer_type n,
  (do
    unify typ `(ℕ),
    if n = `(0) then
      positive <$> mk_app ``pow_zero_pos [a]
    else
      do -- even powers are nonnegative
      -- Note this is automatically strengthened to `0 < a ^ n` when `a ≠ 0` thanks to the `orelse'`
        match n with -- TODO: Decision procedure for parity
        | `(bit0 %% n) := nonnegative <$> mk_app ``pow_bit0_nonneg [a, n]
        | _ := do
                  e' ← pp e,
                  fail (e' ++ "is not an even power so positivity can't prove it's nonnegative")
        end ≤|≥
      do -- `a ^ n` is positive if `a` is, and nonnegative if `a` is
        strictness_a ← core a,
        match strictness_a with
        | positive p := positive <$> mk_app ``pow_pos [p, n]
        | nonnegative p := nonnegative <$> mk_app `pow_nonneg [p, n]
        | nonzero p := nonzero <$> to_expr ``(pow_ne_zero %%n %%p)
        end) <|>
  (do
    unify typ `(ℤ),
    if n = `(0 : ℤ) then
      positive <$> mk_app ``zpow_zero_pos [a]
    else
      do -- even powers are nonnegative
    -- Note this is automatically strengthened to `0 < a ^ n` when `a ≠ 0` thanks to the `orelse'`
        match n with -- TODO: Decision procedure for parity
        | `(bit0 %%n) := nonnegative <$> mk_app ``zpow_bit0_nonneg [a, n]
        | _ := do
                  e' ← pp e,
                  fail (e' ++ "is not an even power so positivity can't prove it's nonnegative")
            end ≤|≥
      do -- `a ^ n` is positive if `a` is, and nonnegative if `a` is
        strictness_a ← core a,
        match strictness_a with
        | positive p := positive <$> mk_app ``zpow_pos_of_pos [p, n]
        | nonnegative p := nonnegative <$> mk_app ``zpow_nonneg [p, n]
        | nonzero p := nonzero <$> to_expr ``(zpow_ne_zero %%n %%p)
        end)
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a ^ n`"

/-- Extension for the `positivity` tactic: raising a positive number in a canonically ordered
semiring gives a positive number. -/
@[positivity]
meta def positivity_canon_pow : expr → tactic strictness
| `(%%r ^ %%n) := do
    typ_n ← infer_type n,
    unify typ_n `(ℕ),
    positive p ← core r,
    positive <$> mk_app ``canonically_ordered_comm_semiring.pow_pos [p, n]
    -- The nonzero never happens because of `tactic.positivity_canon`
| e := pp e >>= fail ∘ format.bracket "The expression `"
    "` is not of the form `a ^ n` for `a` in a `canonically_ordered_comm_semiring` and `n : ℕ`"

private alias abs_pos ↔ _ abs_pos_of_ne_zero

/-- Extension for the `positivity` tactic: an absolute value is nonnegative, and is strictly
positive if its input is nonzero. -/
@[positivity]
meta def positivity_abs : expr → tactic strictness
| `(|%%a|) := do
  (do -- if can prove `0 < a` or `a ≠ 0`, report positivity
    strict_a ← core a,
    match strict_a with
    | positive p := positive <$> mk_app ``abs_pos_of_pos [p]
    | nonzero p := positive <$> mk_app ``abs_pos_of_ne_zero [p]
    | _ := failed
    end) <|>
  nonnegative <$> mk_app ``abs_nonneg [a] -- else report nonnegativity
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `|a|`"

private lemma int_nat_abs_pos {n : ℤ} (hn : 0 < n) : 0 < n.nat_abs :=
int.nat_abs_pos_of_ne_zero hn.ne'

/-- Extension for the `positivity` tactic: `int.nat_abs` is positive when its input is.

Since the output type of `int.nat_abs` is `ℕ`, the nonnegative case is handled by the default
`positivity` tactic.
-/
@[positivity]
meta def positivity_nat_abs : expr → tactic strictness
| `(int.nat_abs %%a) := do
    strict_a ← core a,
    match strict_a with
    | positive p := positive <$> mk_app ``int_nat_abs_pos [p]
    | nonzero p := positive <$> mk_app ``int.nat_abs_pos_of_ne_zero [p]
    | _ := failed
    end
| _ := failed

private lemma nat_cast_pos [ordered_semiring α] [nontrivial α] {n : ℕ} : 0 < n → 0 < (n : α) :=
nat.cast_pos.2

private lemma int_coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := n.cast_nonneg
private lemma int_coe_nat_pos {n : ℕ} : 0 < n → 0 < (n : ℤ) := nat.cast_pos.2

private lemma int_cast_ne_zero [add_group_with_one α] [char_zero α] {n : ℤ} : n ≠ 0 → (n : α) ≠ 0 :=
int.cast_ne_zero.2
private lemma int_cast_nonneg [ordered_ring α] {n : ℤ} (hn : 0 ≤ n) : 0 ≤ (n : α) :=
by { rw ←int.cast_zero, exact int.cast_mono hn }
private lemma int_cast_pos [ordered_ring α] [nontrivial α] {n : ℤ} : 0 < n → 0 < (n : α) :=
int.cast_pos.2

private lemma rat_cast_ne_zero [division_ring α] [char_zero α] {q : ℚ} : q ≠ 0 → (q : α) ≠ 0 :=
rat.cast_ne_zero.2
private lemma rat_cast_nonneg [linear_ordered_field α] {q : ℚ} : 0 ≤ q → 0 ≤ (q : α) :=
rat.cast_nonneg.2
private lemma rat_cast_pos [linear_ordered_field α] {q : ℚ} : 0 < q → 0 < (q : α) := rat.cast_pos.2

/-- Extension for the `positivity` tactic: casts from `ℕ`, `ℤ`, `ℚ`. -/
@[positivity]
meta def positivity_coe : expr → tactic strictness
| `(@coe _ %%typ %%inst %%a) := do
  -- TODO: Using `match` here might turn out too strict since we really want the instance to *unify*
  -- with one of the instances below rather than being equal on the nose.
  -- If this turns out to indeed be a problem, we should figure out the right way to pattern match
  -- up to defeq rather than equality of expressions.
  -- See also "Reflexive tactics for algebra, revisited" by Kazuhiko Sakaguchi at ITP 2022.
  match inst with
  | `(@coe_to_lift _ _ %%inst) := do
    strictness_a ← core a,
    match inst, strictness_a with -- `mk_mapp` is necessary in some places. Why?
    | `(nat.cast_coe), positive p := positive <$> mk_mapp ``nat_cast_pos [typ, none, none, none, p]
    | `(nat.cast_coe), _ := nonnegative <$> mk_mapp ``nat.cast_nonneg [typ, none, a]
    | `(int.cast_coe), positive p := positive <$> mk_mapp ``int_cast_pos [typ, none, none, none, p]
    | `(int.cast_coe), nonnegative p := nonnegative <$>
                                          mk_mapp ``int_cast_nonneg [typ, none, none, p]
    | `(int.cast_coe), nonzero p := nonzero <$>
                                          mk_mapp ``int_cast_ne_zero [typ, none, none, none, p]
    | `(rat.cast_coe), positive p := positive <$> mk_mapp ``rat_cast_pos [typ, none, none, p]
    | `(rat.cast_coe), nonnegative p := nonnegative <$>
                                          mk_mapp ``rat_cast_nonneg [typ, none, none, p]
    | `(rat.cast_coe), nonzero p := nonzero <$>
                                          mk_mapp ``rat_cast_ne_zero [typ, none, none, none, p]
    | `(@coe_base _ _ int.has_coe), positive p := positive <$> mk_app ``int_coe_nat_pos [p]
    | `(@coe_base _ _ int.has_coe), _ := nonnegative <$> mk_app ``int_coe_nat_nonneg [a]
    | _, _ := failed
    end
  | _  := failed
  end
| _ := failed

/-- Extension for the `positivity` tactic: `nat.succ` is always positive. -/
@[positivity]
meta def positivity_succ : expr → tactic strictness
| `(nat.succ %%a) := positive <$> mk_app `nat.succ_pos [a]
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `nat.succ n`"

/-- Extension for the `positivity` tactic: `nat.factorial` is always positive. -/
@[positivity]
meta def positivity_factorial : expr → tactic strictness
| `(nat.factorial %%a) := positive <$> mk_app ``nat.factorial_pos [a]
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `n!`"

/-- Extension for the `positivity` tactic: `nat.asc_factorial` is always positive. -/
@[positivity]
meta def positivity_asc_factorial : expr → tactic strictness
| `(nat.asc_factorial %%a %%b) := positive <$> mk_app ``nat.asc_factorial_pos [a, b]
| e := pp e >>= fail ∘ format.bracket "The expression `"
         "` isn't of the form `nat.asc_factorial n k`"

/-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
@[positivity]
meta def positivity_map : expr → tactic strictness
| (expr.app `(⇑%%f) `(%%a)) := nonnegative <$> mk_app ``map_nonneg [f, a]
| _ := failed

end tactic
