/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import tactic.core
import tactic.lint.basic

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## Implementation notes

This file provides two linters that verify that things we assert do not _yet_ exist do _eventually_
exist. This works by creating declarations of the form:

* ``assert_not_exists._checked.<uniq> : name := `foo`` for `assert_not_exists foo`
* `assert_no_instance._checked.<uniq> := t` for `assert_instance t`

These declarations are then picked up by the linter and analyzed accordingly.
The `_` in the `_checked` prefix should hide them from doc-gen.
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
do
  decl ← ident,
  ff ← succeeds (get_decl decl) |
  fail format!"Declaration {decl} is not allowed to exist in this file.",
  n ← tactic.mk_fresh_name,
  let marker := (`assert_not_exists._checked).append (decl.append n),
  add_decl
    (declaration.defn marker [] `(name) `(decl) default tt),
  pure ()

/-- A linter for checking that the declarations marked `assert_not_exists` eventually exist. -/
meta def assert_not_exists.linter : linter :=
{ test := λ d, (do
    let n := d.to_name,
    tt ← pure ((`assert_not_exists._checked).is_prefix_of n) | pure none,
    declaration.defn _ _ `(name) val _ _ ← pure d,
    n ← tactic.eval_expr name val,
    tt ← succeeds (get_decl n) | pure (some (format!"`{n}` does not ever exist").to_string),
    pure none),
  auto_decls := tt,
  no_errors_found := "All `assert_not_exists` declarations eventually exist.",
  errors_found :=
    "The following declarations used in `assert_not_exists` never exist; perhaps there is a typo.",
  is_fast := tt }

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
do
  q ← texpr,
  e ← i_to_expr q,
  i ← try_core (mk_instance e),
  match i with
  | none := do
      n ← tactic.mk_fresh_name,
      e_str ← to_string <$> pp e,
      let marker := ((`assert_no_instance._checked).mk_string e_str).append n,
      et ← infer_type e,
      tt ← succeeds (get_decl marker) |
      add_decl
          (declaration.defn marker [] et e default tt),
      pure ()
  | some i :=
   (fail!"Instance `{i} : {e}` is not allowed to be found in this file." : tactic unit)
  end

/-- A linter for checking that the declarations marked `assert_no_instance` eventually exist. -/
meta def assert_no_instance.linter : linter :=
{ test := λ d, (do
    let n := d.to_name,
    tt ← pure ((`assert_no_instance._checked).is_prefix_of n) | pure none,
    declaration.defn _ _ _ val _ _ ← pure d,
    tt ← succeeds (tactic.mk_instance val)
      | (some ∘ format.to_string) <$> pformat!"No instance of `{val}`",
    pure none),
  auto_decls := tt,
  no_errors_found := "All `assert_no_instance` instances eventually exist.",
  errors_found :=
    "The following typeclass instances used in `assert_no_instance` never exist; perhaps they " ++
    "are missing?",
  is_fast := ff }

end
