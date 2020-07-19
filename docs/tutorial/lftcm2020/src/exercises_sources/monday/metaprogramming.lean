import tactic

open tactic

/-!

This file contains three tactic-programming exercises of increasing difficulty.

They were (hastily) written to follow the metaprogramming tutorial at
Lean for the Curious Mathematician 2020.

If you're looking for more (better) exercises, we strongly recommend the
exercises by Blanchette et al
for the course Logical Verification at the Vrije Universiteit Amsterdam,
and the corresponding chapter of the course notes:

https://github.com/blanchette/logical_verification_2020/blob/master/lean/love07_metaprogramming_exercise_sheet.lean
https://github.com/blanchette/logical_verification_2020/raw/master/hitchhikers_guide.pdf



## Exercise 1

Write a `contradiction` tactic.
The tactic should look through the hypotheses in the local context
trying to find two that contradict each other,
i.e. proving `P` and `¬ P` for some proposition `P`.
It should use this contradiction to close the goal.

Bonus: handle `P → false` as well as `¬ P`.

This exercise is to practice manipulating the hypotheses and goal.

Note: this exists as `tactic.interactive.contradiction`.

-/

meta def tactic.interactive.contr : tactic unit := sorry

example (P Q R : Prop) (hp : P) (hq : Q) (hr : ¬ R) (hnq : ¬ Q) : false :=
by contr


example (P Q R : Prop) (hnq : ¬ Q) (hp : P) (hq : Q) (hr : ¬ R) : 0 = 1 :=
by contr


example (P Q R : Prop) (hp : P) (hq : Q) (hr : ¬ R) (hnq : Q → false) : false :=
by contr



/-!

## Exercise 2

Write a tactic that proves a given `nat`-valued declaration is nonnegative.
The tactic should take the name of a declaration whose return type is `ℕ`
(presumably with some arguments), e.g. `nat.add : ℕ → ℕ → ℕ`
or `list.length : Π α : Type, list α → ℕ`.
It should add a new declaration to the environment which proves all applications
of this function are nonnegative,
e.g. `nat.add_nonneg : ∀ m n : ℕ, 0 ≤ nat.add m n`.

Bonus: create reasonable names for these declarations, and/or take an optional argument
for the new name.

This tactic is not useful by itself, but it's a good way to practice
querying and modifying an environment and working under binders.
It is not a tactic to be used during a proof, but rather as a command.


Hints:
* For looking at declarations in the environment, you will need the `declaration` type,
  as well as the tactics `get_decl` and `add_decl`.
* You will have to manipulate an expression under binders.
  The tactics `mk_local_pis` and `pis`, or their lambda equivalents, will be helpful here.
* `mk_mapp` is a variant of `mk_app` that lets you provide implicit arguments.
-/


meta def add_nonneg_proof (n : name) : tactic unit := sorry

run_cmd add_nonneg_proof `nat.add
run_cmd add_nonneg_proof `list.length

#check nat.add_nonneg
#check list.length_nonneg


/-!

## Exercise 3 (challenge!)

The mathlib tactic `cancel_denoms` is intended to get rid of division by numerals
in expressions where this makes sense. For example,

-/

example (q : ℚ) (h : q / 3 > 0) : q > 0 :=
begin
  cancel_denoms at h, exact h
end

/-!

But it is not complete. In particular, it doesn't like nested division
or other operators in denominators. These all fail:

-/

example (q : ℚ) (h : q / (3 / 4) > 0) : false :=
begin
  cancel_denoms at h,
end

example (p q : ℚ) (h : q / 2 / 3 < q) : false :=
begin
  cancel_denoms at h,
end

example (p q : ℚ) (h : q / 2 < 3 / (4*q)) : false :=
begin
  cancel_denoms at h,
end

-- this one succeeds but doesn't do what it should
example (p q : ℚ) (h : q / (2*3) < q) : false :=
begin
  cancel_denoms at h,
end

/-!

Look at the code in `src/tactic/cancel_denoms.lean` and try to fix it.
See if you can solve any or all of these failing test cases.

If you succeed, a pull request to mathlib is strongly encouraged!

-/
