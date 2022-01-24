/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg
-/

import tactic.ring

/-!

# linear_combination Tactic

In this file, the `linear_combination` tactic is created.  This tactic attempts
to prove the target by creating and applying a linear combination of a list of
equalities.  This file also includes a definition for
`linear_combination_config`.  A `linear_combination_config` object can be 
passed into the tactic, allowing the user to specify a normalization tactic.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, it uses a normalization tactic to see if the weighted sum is equal
to the target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace linear_combination

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


/-! ### Configuration -/


/-- 
A configuration object for `linear_combination`. 

`normalize` describes whether or not the normalization step should be used.

`normalization_tactic` describes the tactic used for normalization when
checking if the weighted sum is equivalent to the goal (when `normalize` is tt).
-/
meta structure linear_combination_config : Type :=
(normalize : bool := tt)
(normalization_tactic : tactic unit := `[ring1])


/-! ### Part 1: Multiplying Equations by Constants and Adding Them Together -/


/--
Given that lhs = rhs, this tactic returns an expr stating that
  coeff * lhs = coeff * rhs.

* Input:
  * `heq` : an expr, which should be an equality with some type α on each side,
      where `has_mul α` is true
  * `coeff` : a pexpr, which should be a value of type α

* Output: a tactic expr that is the result of multiplying both sides of `heq` by
    the `coeff`
-/
meta def mul_equality_expr (heq : expr) (coeff : pexpr) : tactic expr :=
do
  `(%%lhs = %%rhs) ← tactic.infer_type heq,
  -- Explicitly mark the coefficient as having the same type as the sides of
  --   heq - this is necessary in order to use the left_mul_both_sides lemma
  left_type ← tactic.infer_type lhs,
  coeff_expr ← tactic.to_expr ``(%%coeff : %%left_type),
  tactic.mk_app ``left_mul_both_sides [coeff_expr, heq]
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'has_mul' condition in order to multiply the " ++
    "equalities by the given factors.")

/--
Given two hypotheses stating that a = b and c = d, this tactic returns an
  expr stating that a + c = b + d.

* Input:
  * `heq1` : an expr, which should be an equality with some type α on each side,
      where `has_add α` is true
  * `heq2` : an expr, which should be an equality with type α on each side

* Output: a tactic expr that is the result of adding the two equalities
-/
meta def sum_equalities (heq1 heq2 : expr) : tactic expr :=
do
  tactic.mk_app ``sum_two_equations [heq1, heq2]
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'has_add' condition in order to add the " ++
    "equalities together.")

/--
Given that a = b and c = d, along with a coefficient, this tactic returns an
  expr stating that a + coeff * c = b + coeff * d.

* Input:
  * `heq1` : an expr, which should be an equality with some type α on each side,
    where `has_add α` and `has_mul α` are true
  * `heq2` : an expr, which should be an equality with type α on each side
  * `coeff_for_eq2` : a pexpr, which should be a value of type α
    
* Output: a tactic expr that is the result of adding the first equality to the
  result of multiplying `coeff_for_eq2` by the second equality
-/
meta def sum_two_hyps_one_mul_helper (heq1 heq2 : expr) (coeff_for_eq2 : pexpr) :
  tactic expr :=
do
  -- Multiply the second equation by the coefficient
  hmul2 ← mul_equality_expr heq2 coeff_for_eq2,
  -- Add the first equation and the newly computed equation together
  sum_equalities heq1 hmul2

/--
This tactic builds on the given summed equation by multiplying each equation in
  the given list by its associated coefficient and summing the equations
  together

* Input:
  * an option (tactic expr) : `none`, if there is no sum to add to yet, or
      `some` containing the base summation equation
  * a list name : a list of names, referring to equations in the local context
  * a list pexpr : a list of coefficients to be multiplied with the
      corresponding equations in the list of names
  
* Output: a tactic expr expressing the weighted sum of the given equations
    added to the base equation
-/
meta def make_sum_of_hyps_helper :
  option (tactic expr) → list name → list pexpr → tactic expr
| none [] []                                               :=
  do tactic.fail "There are no hypotheses to add"
| (some tactic_hcombo) [] []                               :=
  do tactic_hcombo
| none (heq_nam :: heqs) (coeff :: coeffs)                 :=
 do
    -- This is the first equation, and we do not have anything to add to it
    heq ← tactic.get_local heq_nam,
    let eq1_times_coeff1 := mul_equality_expr heq coeff,
    make_sum_of_hyps_helper (some eq1_times_coeff1) heqs coeffs
| (some tactic_hcombo) (heq_nam :: heqs) (coeff :: coeffs) :=
  do
    heq ← tactic.get_local heq_nam,
    hcombo ← tactic_hcombo,
    -- We want to add this weighted equation to
    --   the current equation in the hypothesis
    let hcombo_updated := sum_two_hyps_one_mul_helper hcombo heq coeff,
    make_sum_of_hyps_helper (some hcombo_updated) heqs coeffs
| _ _ _                                             :=
  do tactic.fail ("The length of the input list of equalities should be the " ++
    "same as the length of the input list of coefficients")

/--
Given a list of names referencing equalities and a list of pexprs representing
  coefficients, this tactic creates a weighted sum of the equalities, where each
  equation is multiplied by the corresponding coefficient.

* Input:
  * `heqs` : a list of names, referring to equations in the local context
  * `coeffs` : a list of coefficients to be multiplied with the corresponding
      equations in the list of names
  
* Output: a `tactic expr` that is the weighted sum of the equations
-/
meta def make_sum_of_hyps (heqs : list name) (coeffs : list pexpr) :
  tactic expr :=
make_sum_of_hyps_helper none heqs coeffs


/-! ### Part 2: Simplifying -/


/--
This tactic moves all the terms in an equality to the left side of the equals
  sign by subtracting the right side of the equation from the left side.  In
  other words, given lhs = rhs, this tactic returns lhs - rhs = 0.

* Input:
  * `heq` : an expr, which should be an equality with some type α on each side,
      where `add_group α` is true
  
* Output: tactic expr that is lhs - rhs = 0, where lhs and rhs are the left and 
  right sides of heq respectively
-/
meta def move_to_left_side (heq : expr) : tactic expr :=
do
  tactic.mk_app ``left_minus_right [heq]
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'add_group' condition in order to match the linear " ++
    "combination to the target.")

/--
Moves all the terms in the target to the left side of the equals sign by
  subtracting the right side of the equation from the left side.  In other
  words, given a target of lhs = rhs, this tactic returns lhs - rhs = 0.
Note: The target must be an equality when this tactic is called, and the
  equality must have some type α on each side, where `add_group α` is true.

* Input: N/A
  
* Output: tactic unit
-/
meta def move_target_to_left_side : tactic unit :=
do
  -- Move all the terms in the target equality to the left side
  target ← tactic.target,
  (targ_lhs, targ_rhs) ← tactic.match_eq target,
  target_left_eq ← tactic.to_expr ``(%%targ_lhs - %%targ_rhs = 0),
  do {
    can_replace_proof ← tactic.mk_app ``all_on_left_equiv [targ_lhs, targ_rhs],
    tactic.replace_target target_left_eq can_replace_proof
  }
  <|> tactic.fail ("The type of the left and right sides of the goal " ++
    "must fulfill the 'add_group' condition in order to match the linear " ++
    "combination to the target.")



/-! ### Part 3: Matching the Linear Combination to the Target -/


/--
This tactic changes the goal to be that the lefthand side of the target is
  equal to the lefthand side of the given expression.  For example,
  if `hsum_on_left` is 5*x - 5*y = 0, and the target is -5*y + 5*x = 0, this
  tactic will change the target to be -5*y + 5*x = 5*x - 5*y.

This tactic only should be used when the target is an equality whose right side
  is 0.

* Input:
  * `hsum_on_left` : expr, which should be an equality whose right side is 0
  
* Output: tactic unit
-/
meta def set_goal_to_hleft_eq_tleft (hsum_on_left : expr) : tactic unit :=
do
  { change_goal ← tactic.to_expr ``(replace_eq_expr %%hsum_on_left),
    tactic.apply change_goal,
    pure () }
  <|> tactic.fail ("The type of the left and right sides of each equality " ++
    "must fulfill the 'has_zero' condition.")

/--
This tactic attempts to prove the goal by normalizing the target if the
`normalize` field of the given configuration is true.

* Input:
  * `config` : a linear_combination_config, which determines the tactic used
      for normalization if normalization is done

* Outout: tactic unit
-/
meta def prove_equal_if_desired (config : linear_combination_config) :
  tactic unit :=
when config.normalize config.normalization_tactic

/-! ### Part 4: Completed Tactic -/


/--
This is a tactic that attempts to prove the target by creating and applying a
  linear combination of a list of equalities.  (If the `normalize` field of the
  configuration is set to ff, then the tactic will simply set the user up to 
  prove their target using the linear combination instead of attempting to
  finish the proof.)

Note: The left and right sides of all the equations should have the same
  ring type, and the coefficients should also have this type.  This type must
  have the has_mul and add_group properties.  Also note that the target must
  involve at least one variable.

* Input:
  * `heqs` : a list of names, referring to equations in the local context
  * `coeffs` : a list of coefficients to be multiplied with the corresponding
    equations in the list of names
  * `config` : a linear_combination_config, which determines the tactic used
      for normalization; by default, this value is the standard configuration
      for a linear_combination_config
  
* Output: tactic unit
-/
meta def linear_combination (heqs : list name) (coeffs : list pexpr)
  (config : linear_combination_config := {}) : tactic unit :=
do
  hsum ← make_sum_of_hyps heqs coeffs,
  hsum_on_left ← move_to_left_side hsum,
  move_target_to_left_side,
  set_goal_to_hleft_eq_tleft hsum_on_left,
  prove_equal_if_desired config


section interactive_mode
setup_tactic_parser

/--
A parser that matches a pair in parentheses, where the first item in the pair
is an identifier and the second item in the pair is a pexpr.

* Input: None

* Output: a lean.parser (name × pexpr)
-/
meta def parse_name_pexpr_pair : lean.parser (name × pexpr) :=
do 
  tk "(",
  id ← ident,
  tk ",",
  coeff ← parser.pexpr 0,
  tk ")",
  pure (id, coeff)

/--
`linear_combination` attempts to prove the target by creating and applying a
  linear combination of a list of equalities.  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to ff, then the tactic will simply set the user up to
  prove their target using the linear combination instead of attempting to
  finish the proof.

Note: The left and right sides of all the equations should have the same
  type, and the coefficients should also have this type.  This type must
  have the has_mul and add_group properties.  Also note that the target must
  involve at least one variable.

* Input:
  * `heqs` : a list of identifiers, referring to equations in the local context
  * `coeffs` : a list of coefficients to be multiplied with the corresponding
      equations in the list of names

  * `input` : a sequence of name and pexpr pairs, which represents the pairs
      of hypotheses and their corresponding coefficients
  * `config` : a linear_combination_config, which determines the tactic used
      for normalization; by default, this value is the standard configuration
      for a linear_combination_config
  
* Output: tactic unit

Example Usage:
  Given that `h1` and `h2` are equalities in the local context,
  `linear_combination (h1, 2) (h2, -3)`
  will attempt to solve the goal by computing `2 * h1 + -3 * h2`
  and matching that to the goal.
-/
add_tactic_doc
{ name := "linear_combination",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.linear_combination],
  tags := [] }

meta def _root_.tactic.interactive.linear_combination
  (input : parse parse_name_pexpr_pair*)
  (config : linear_combination_config := {}) : tactic unit :=
let (heqs, coeffs) := list.unzip input in
linear_combination heqs coeffs config



end interactive_mode 

end linear_combination