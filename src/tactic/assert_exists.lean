/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import tactic.core

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## Future work
We should have a linter that collects all `assert_not_exists` and `assert_no_instance` commands,
and checks that they are eventually satisfied when importing all of mathlib.
This will protect against typos.
-/

section
setup_tactic_parser
open tactic

/--
`assert_exists n` is a user command that asserts that a declaration named `n` exists
in the current import scope.

Be careful to use names (e.g. `rat`) rather than notations (e.g. `ℚ`).
-/
@[user_command]
meta def assert_exists (_ : parse $ tk "assert_exists")  : lean.parser unit :=
do decl ← ident,
   d ← get_decl decl,
   return ()

/--
`assert_not_exists n` is a user command that asserts that a declaration named `n` *does not exist*
in the current import scope.

Be careful to use names (e.g. `rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.
-/
@[user_command]
meta def assert_not_exists (_ : parse $ tk "assert_not_exists")  : lean.parser unit :=
do decl ← ident,
   success_if_fail (get_decl decl) <|>
   fail format!"Declaration {decl} is not allowed to exist in this file."

/--
`assert_instance e` is a user command that asserts that an instance `e` is available
in the current import scope.

Example usage:
```
assert_instance semiring ℕ
```
-/
@[user_command]
meta def assert_instance (_ : parse $ tk "assert_instance")  : lean.parser unit :=
do q ← texpr,
   e ← i_to_expr q,
   mk_instance e,
   return ()

/--
`assert_no_instance e` is a user command that asserts that an instance `e` *is not available*
in the current import scope.

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_no_instance` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_no_instance` statement without careful discussion ahead of time.

Example usage:
```
assert_no_instance linear_ordered_field ℚ
```
-/
@[user_command]
meta def assert_no_instance (_ : parse $ tk "assert_no_instance")  : lean.parser unit :=
do q ← texpr,
   e ← i_to_expr q,
   i ← try_core (mk_instance e),
   match i with
   | none := skip -- TODO: record for the linter
   | some i := 
    (fail!"Instance `{i} : {e}` is not allowed to be found in this file." : tactic unit)
   end

end
