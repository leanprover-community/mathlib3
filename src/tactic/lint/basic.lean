/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import tactic.core

/-!
# Basic linter types and attributes

This file defines the basic types and attributes used by the linting
framework.  A linter essentially consists of a function
`declaration → tactic (option string)`, this function together with some
metadata is stored in the `linter` structure. We define two attributes:

 * `@[linter]` applies to a declaration of type `linter` and adds it to the default linter set.

 * `@[nolint linter_name]` omits the tagged declaration from being checked by
   the linter with name `linter_name`.
-/

open tactic
setup_tactic_parser

-- Manual constant subexpression elimination for performance.
private meta def linter_ns := `linter
private meta def nolint_infix := `_nolint

/--
Computes the declaration name used to store the nolint attribute data.

Retrieving the parameters for user attributes is *extremely* slow.
Hence we store the parameters of the nolint attribute as declarations
in the environment.  E.g. for `@[nolint foo] def bar := _` we add the
following declaration:

```lean
meta def bar._nolint.foo : unit := ()
```
-/
private meta def mk_nolint_decl_name (decl : name) (linter : name) : name :=
(decl ++ nolint_infix) ++ linter

/-- Defines the user attribute `nolint` for skipping `#lint` -/
@[user_attribute]
meta def nolint_attr : user_attribute _ (list name) :=
{ name := "nolint",
  descr := "Do not report this declaration in any of the tests of `#lint`",
  after_set := some $ λ n _ _, (do
    ls@(_::_) ← nolint_attr.get_param n
      | fail "you need to specify at least one linter to disable",
    ls.mmap' $ λ l, do
      get_decl (linter_ns ++ l) <|> fail ("unknown linter: " ++ to_string l),
      try $ add_decl $ declaration.defn (mk_nolint_decl_name n l) []
        `(unit) `(unit.star) (default _) ff),
  parser := ident* }

add_tactic_doc
{ name                     := "nolint",
  category                 := doc_category.attr,
  decl_names               := [`nolint_attr],
  tags                     := ["linting"] }

/-- `should_be_linted linter decl` returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
meta def should_be_linted (linter : name) (decl : name) : tactic bool := do
e ← get_env,
pure $ ¬ e.contains (mk_nolint_decl_name decl linter)

/--
A linting test for the `#lint` command.

`test` defines a test to perform on every declaration. It should never fail. Returning `none`
signifies a passing test. Returning `some msg` reports a failing test with error `msg`.

`no_errors_found` is the message printed when all tests are negative, and `errors_found` is printed
when at least one test is positive.

If `is_fast` is false, this test will be omitted from `#lint-`.

If `auto_decls` is true, this test will also be executed on automatically generated declarations.
-/
meta structure linter :=
(test : declaration → tactic (option string))
(no_errors_found : string)
(errors_found : string)
(is_fast : bool := tt)
(auto_decls : bool := ff)

/-- Takes a list of names that resolve to declarations of type `linter`,
and produces a list of linters. -/
meta def get_linters (l : list name) : tactic (list (name × linter)) :=
l.mmap (λ n, prod.mk n.last <$> (mk_const n >>= eval_expr linter)
  <|> fail format!"invalid linter: {n}")

/-- Defines the user attribute `linter` for adding a linter to the default set.
Linters should be defined in the `linter` namespace.
A linter `linter.my_new_linter` is referred to as `my_new_linter` (without the `linter` namespace)
when used in `#lint`.
-/
@[user_attribute]
meta def linter_attr : user_attribute unit unit :=
{ name := "linter",
  descr := "Use this declaration as a linting test in #lint",
  after_set := some $ λ nm _ _,
                mk_const nm >>= infer_type >>= unify `(linter) }

add_tactic_doc
{ name                     := "linter",
  category                 := doc_category.attr,
  decl_names               := [`linter_attr],
  tags                     := ["linting"] }
