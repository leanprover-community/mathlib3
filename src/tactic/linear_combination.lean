/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg
-/

import tactic.ring

/-!

# linear_combination Tactic
In this file, the `linear_combination` tactic is created.  This tactic, which
works over `ring`s, attempts to simplify the target by creating a linear combination
of a list of equalities and subtracting it from the target.  This file also includes a
definition for `linear_combination_config`.  A `linear_combination_config`
object can be passed into the tactic, allowing the user to specify a
normalization tactic.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace linear_combo
open tactic

/-! ### Lemmas -/

lemma left_mul_both_sides {α} [h : has_mul α] {x y : α} (z : α) (h1 : x = y) :
  z * x = z * y :=
congr_arg (has_mul.mul z) h1

lemma sum_two_equations {α} [h : has_add α] {x1 y1 x2 y2 : α} (h1 : x1 = y1)
  (h2: x2 = y2) : x1 + x2 = y1 + y2 :=
congr (congr_arg has_add.add h1) h2

lemma left_minus_right {α} [h : add_group α] {x y : α} (h1 : x = y) :
  x - y = 0 :=
sub_eq_zero.mpr h1

lemma all_on_left_equiv {α} [h : add_group α] (x y : α) :
  (x = y) = (x - y = 0) :=
propext (⟨left_minus_right, sub_eq_zero.mp⟩)

lemma replace_eq_expr {α} [h : has_zero α] {x y : α} (h1 : x = 0) (h2 : y = x) :
  y = 0 :=
by rwa h2

lemma eq_zero_of_sub_eq_zero {α} [add_group α] {x y : α} (h : y = 0) (h2 : x - y = 0) : x = 0 :=
by rwa [h, sub_zero] at h2

/-! ### Configuration -/


/--
A configuration object for `linear_combination`.

`normalize` describes whether or not the normalization step should be used.

`normalization_tactic` describes the tactic used for normalization when
checking if the weighted sum is equivalent to the goal (when `normalize` is `tt`).
-/
meta structure linear_combination_config : Type :=
(normalize : bool := tt)
(normalization_tactic : tactic unit := `[ring_nf SOP])


/-! ### Part 1: Multiplying Equations by Constants and Adding Them Together -/


/--
Given that `lhs = rhs`, this tactic returns an `expr` proving that
  `coeff * lhs = coeff * rhs`.

* Input:
  * `h_equality` : an `expr`, whose type should be an equality between terms of
      type `α`, where there is an instance of `has_mul α`
  * `coeff` : a `pexpr`, which should be a value of type `α`

* Output: an `expr`, which proves that the result of multiplying both sides
    of `h_equality` by the `coeff` holds
-/
meta def mul_equality_expr (h_equality : expr) (coeff : pexpr) : tactic expr :=
do
  `(%%lhs = %%rhs) ← infer_type h_equality,
  -- Mark the coefficient as having the same type as the sides of `h_equality` -
  --   this is necessary in order to use the left_mul_both_sides lemma
  left_type ← infer_type lhs,
  coeff_expr ← to_expr ``(%%coeff : %%left_type),
  mk_app ``left_mul_both_sides [coeff_expr, h_equality]

/--
Given two hypotheses that `a = b` and `c = d`, this tactic returns an `expr` proving
  that `a + c = b + d`.

* Input:
  * `h_equality1` : an `expr`, whose type should be an equality between terms of
      type `α`, where there is an instance of `has_add α`
  * `h_equality2` : an `expr`, whose type should be an equality between terms of
      type `α`

* Output: an `expr`, which proves that the result of adding the two
    equalities holds
-/
meta def sum_equalities (h_equality1 h_equality2 : expr) : tactic expr :=
mk_app ``sum_two_equations [h_equality1, h_equality2]

/--
Given that `a = b` and `c = d`, along with a coefficient, this tactic returns an
  `expr` proving that `a + coeff * c = b + coeff * d`.

* Input:
  * `h_equality1` : an `expr`, whose type should be an equality between terms of
      type `α`, where there are instances of `has_add α` and `has_mul α`
  * `h_equality2` : an `expr`, whose type should be an equality between terms of
      type `α`
  * `coeff_for_eq2` : a `pexpr`, which should be a value of type `α`

* Output: an `expr`, which proves that the result of adding the first
  equality to the result of multiplying `coeff_for_eq2` by the second equality
  holds
-/
meta def sum_two_hyps_one_mul_helper (h_equality1 h_equality2 : expr)
  (coeff_for_eq2 : pexpr) : tactic expr :=
mul_equality_expr h_equality2 coeff_for_eq2 >>= sum_equalities h_equality1

/--
Given that `l_sum1 = r_sum1`, `l_h1 = r_h1`, ..., `l_hn = r_hn`, and given
  coefficients `c_1`, ..., `c_n`, this tactic returns an `expr` proving that
    `l_sum1 + (c_1 * l_h1) + ... + (c_n * l_hn)`
  `= r_sum1 + (c_1 * r_h1) + ... + (c_n * r_hn)`

* Input:
  * `expected_tp`: the type of the terms being compared in the target equality
  * an `option (tactic expr)` : `none`, if there is no sum to add to yet, or
      `some` containing the base summation equation
  * a `list name` : a list of names, referring to equalities in the local context
  * a `list pexpr` : a list of coefficients to be multiplied with the
      corresponding equalities in the list of names

* Output: an `expr`, which proves that the weighted sum of the given
    equalities added to the base equation holds
-/
meta def make_sum_of_hyps_helper (expected_tp : expr) :
  option (tactic expr) → list expr → list pexpr → tactic expr
| none [] []                                                             :=
  to_expr ``(rfl : (0 : %%expected_tp) = 0)
| (some tactic_hcombo) [] []                                             :=
  do tactic_hcombo
| none (h_equality :: h_eqs_names) (coeff :: coeffs)                 :=
 do
    -- This is the first equality, and we do not have anything to add to it
    -- h_equality ← get_local h_equality_nam,
    `(@eq %%eqtp _ _) ← infer_type h_equality |
      fail!"{h_equality} is expected to be a proof of an equality",
    is_def_eq eqtp expected_tp <|>
      fail!("{h_equality} is an equality between terms of type {eqtp}, but is expected to be" ++
        " between terms of type {expected_tp}"),
    make_sum_of_hyps_helper
      (some (mul_equality_expr h_equality coeff))
      h_eqs_names
      coeffs
| (some tactic_hcombo) (h_equality :: h_eqs_names) (coeff :: coeffs) :=
  do
    -- h_equality ← get_local h_equality_nam,
    hcombo ← tactic_hcombo,
    -- We want to add this weighted equality to the current equality in
    --   the hypothesis
    make_sum_of_hyps_helper
      (some (sum_two_hyps_one_mul_helper hcombo h_equality coeff))
      h_eqs_names
      coeffs
| _ _ _                                                                  :=
  do fail ("The length of the input list of equalities should be the " ++
    "same as the length of the input list of coefficients")

/--
Given a list of names referencing equalities and a list of pexprs representing
  coefficients, this tactic proves that a weighted sum of the equalities
  (where each equation is multiplied by the corresponding coefficient) holds.

* Input:
  * `expected_tp`: the type of the terms being compared in the target equality
  * `h_eqs_names` : a list of names, referring to equalities in the local
      context
  * `coeffs` : a list of coefficients to be multiplied with the corresponding
      equalities in the list of names

* Output: an `expr`, which proves that the weighted sum of the equalities
    holds
-/
meta def make_sum_of_hyps (expected_tp : expr) (h_eqs_names : list expr) (coeffs : list pexpr) :
  tactic expr :=
make_sum_of_hyps_helper expected_tp none h_eqs_names coeffs

/-! ### Part 2: Simplifying -/


/--
This tactic proves that the result of moving all the terms in an equality to
  the left side of the equals sign by subtracting the right side of the
  equation from the left side holds.  In other words, given `lhs = rhs`,
  this tactic proves that `lhs - rhs = 0`.

* Input:
  * `h_equality` : an `expr`, whose type should be an equality between terms of
      type `α`, where there is an instance of `add_group α`

* Output: an `expr`, which proves that `lhs - rhs = 0`, where `lhs` and `rhs` are
   the left and right sides of `h_equality` respectively
-/
meta def move_to_left_side (h_equality : expr) : tactic expr :=
mk_app ``left_minus_right [h_equality]

/--
This tactic replaces the target with the result of moving all the terms in the
  target to the left side of the equals sign by subtracting the right side of
  the equation from the left side.  In other words, when the target is
  lhs = rhs, this tactic proves that `lhs - rhs = 0` and replaces the target
  with this new equality.
Note: The target must be an equality when this tactic is called, and the
  equality must have some type `α` on each side, where there is an instance of
  `add_group α`.

* Input: N/A

* Output: N/A
-/
meta def move_target_to_left_side : tactic unit :=
do
  -- Move all the terms in the target equality to the left side
  target ← target,
  (targ_lhs, targ_rhs) ← match_eq target,
  target_left_eq ← to_expr ``(%%targ_lhs - %%targ_rhs = 0),
  mk_app ``all_on_left_equiv [targ_lhs, targ_rhs] >>= replace_target target_left_eq


/-! ### Part 3: Matching the Linear Combination to the Target -/


/--
This tactic changes the goal to be that the lefthand side of the target minus the
  lefthand side of the given expression is equal to 0.  For example,
  if `hsum_on_left` is `5*x - 5*y = 0`, and the target is `-5*y + 5*x = 0`, this
  tactic will change the target to be `-5*y + 5*x - (5*x - 5*y) = 0`.

This tactic only should be used when the target's type is an equality whose
  right side is 0.

* Input:
  * `hsum_on_left` : expr, whose type should be an equality with 0 on the right
      side of the equals sign

* Output: N/A
-/
meta def set_goal_to_hleft_sub_tleft (hsum_on_left : expr) : tactic unit :=
do to_expr ``(eq_zero_of_sub_eq_zero %%hsum_on_left) >>= apply, skip

/--
This tactic attempts to prove the goal by normalizing the target if the
`normalize` field of the given configuration is true.

* Input:
  * `config` : a `linear_combination_config`, which determines the tactic used
      for normalization if normalization is done

* Output: N/A
-/
meta def normalize_if_desired (config : linear_combination_config) :
  tactic unit :=
when config.normalize config.normalization_tactic

/-! ### Part 4: Completed Tactic -/


/--
This is a tactic that attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  (If the `normalize` field of the
  configuration is set to ff, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.)

Note: The left and right sides of all the equalities should have the same
  ring type, and the coefficients should also have this type.  There must be
  instances of `has_mul` and `add_group` for this type.  Also note that the
  target must involve at least one variable.

* Input:
  * `h_eqs_names` : a list of names, referring to equations in the local
      context
  * `coeffs` : a list of coefficients to be multiplied with the corresponding
    equations in the list of names
  * `config` : a `linear_combination_config`, which determines the tactic used
      for normalization; by default, this value is the standard configuration
      for a `linear_combination_config`

* Output: N/A
-/
meta def linear_combination (h_eqs_names : list pexpr) (coeffs : list pexpr)
  (config : linear_combination_config := {}) : tactic unit :=
do
  `(@eq %%ext _ _) ← target | fail "linear_combination can only be used to prove equality goals",
  h_eqs ← h_eqs_names.mmap to_expr,
  hsum ← make_sum_of_hyps ext h_eqs coeffs,
  hsum_on_left ← move_to_left_side hsum,
  move_target_to_left_side,
  set_goal_to_hleft_sub_tleft hsum_on_left,
  normalize_if_desired config

/-- `mk_mul [p₀, p₁, ..., pₙ]` produces the pexpr `p₀ * p₁ * ... * pₙ`. -/
meta def mk_mul : list pexpr → pexpr
| [] := ``(1)
| [e] := e
| (e::es) := ``(%%e * %%(mk_mul es))

/--
`as_linear_combo neg ms e` is used to parse the argument to `linear_combination`.
This argument is a sequence of literals `x`, `-x`, or `c*x` combined with `+` or `-`,
given by the pexpr `e`.
The `neg` and `ms` arguments are used recursively; called at the top level, its usage should be
`as_linear_combo ff [] e`.
-/
meta def as_linear_combo : bool → list pexpr → pexpr → list (pexpr × pexpr)
| neg ms e :=
  let (head, args) := pexpr.get_app_fn_args e in
  match head.get_frozen_name, args with
  | ``has_add.add, [e1, e2] := as_linear_combo neg ms e1 ++ as_linear_combo neg ms e2
  | ``has_sub.sub, [e1, e2] := as_linear_combo neg ms e1 ++ as_linear_combo (bnot neg) ms e2
  | ``has_mul.mul, [e1, e2] := as_linear_combo neg (e1::ms) e2
  | ``has_div.div, [e1, e2] := as_linear_combo neg (``((%%e2)⁻¹)::ms) e1
  | ``has_neg.neg, [e1] := as_linear_combo (bnot neg) ms e1
  | _, _ := let m := mk_mul ms in [(e, if neg then ``(-%%m) else m)]
  end

section interactive_mode
setup_tactic_parser

/--
`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `has_mul` and `add_group` for this type.

* Input:
  * `input` : the linear combination of proofs of equalities, given as a sum/difference
      of coefficients multiplied by expressions. The coefficients may be arbitrary
      pre-expressions; if a coefficient is an application of `+` or `-` it should be
      surrounded by parentheses. The expressions can be arbitrary proof terms proving
      equalities. Most commonly they are hypothesis names `h1, h2, ...`.

      If a coefficient is omitted, it is taken to be `1`.
  * `config` : a `linear_combination_config`, which determines the tactic used
      for normalization; by default, this value is the standard configuration
      for a linear_combination_config.  In the standard configuration,
      `normalize` is set to tt (meaning this tactic is set to use
      normalization), and `normalization_tactic` is set to  `ring_nf SOP`.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
begin
 linear_combination -2*h2,
 /- Goal: x * y + x * 2 - 1 = 0 -/
end

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 :=
by linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
by linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) :
  2*x = -6 :=
begin
  linear_combination 2*h1 with {normalize := ff},
  simp,
  norm_cast
end

constants (qc : ℚ) (hqc : qc = 2*qc)

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by linear_combination 3 * h a b + hqc
```
-/
meta def _root_.tactic.interactive.linear_combination
  (input : parse (as_linear_combo ff [] <$> texpr)?)
  (_ : parse (tk "with")?)
  (config : linear_combination_config := {})
  : tactic unit :=
let (h_eqs_names, coeffs) := list.unzip (input.get_or_else []) in
linear_combination h_eqs_names coeffs config

add_tactic_doc
{ name := "linear_combination",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.linear_combination],
  tags := ["arithmetic"] }

end interactive_mode
end linear_combo
