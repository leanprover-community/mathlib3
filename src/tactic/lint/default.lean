/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import tactic.lint.frontend
import tactic.lint.simp
import tactic.lint.type_classes
import tactic.lint.misc

open tactic

add_tactic_doc
{ name                     := "linting commands",
  category                 := doc_category.cmd,
  decl_names               := [`lint_cmd, `lint_mathlib_cmd, `lint_all_cmd, `list_linters],
  tags                     := ["linting"],
  description              :=
"User commands to spot common mistakes in the code

* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

The following linters are run by default:
1. `unused_arguments` checks for unused arguments in declarations.
2. `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma.
3. `dup_namespce` checks whether a namespace is duplicated in the name of a declaration.
4. `ge_or_gt` checks whether ≥/> is used in the declaration.
5. `instance_priority` checks that instances that always apply have priority below default.
6. `doc_blame` checks for missing doc strings on definitions and constants.
7.  `has_inhabited_instance` checks whether every type has an associated `inhabited` instance.
8.  `impossible_instance` checks for instances that can never fire.
9.  `incorrect_type_class_argument` checks for arguments in [square brackets] that are not classes.
10. `dangerous_instance` checks for instances that generate type-class problems with metavariables.
11. `fails_quickly` tests that type-class inference ends (relatively) quickly when applied to
    variables.
12. `has_coe_variable` tests that there are no instances of type `has_coe α t` for a variable `α`.
13. `inhabited_nonempty` checks for `inhabited` instance arguments that should be changed to
    `nonempty`.
14. `simp_nf` checks that the left-hand side of simp lemmas is in simp-normal form.
15. `simp_var_head` checks that there are no variables as head symbol of left-hand sides of
    simp lemmas.
16. `simp_comm` checks that no commutativity lemmas (such as `add_comm`) are marked simp.
17. `decidable_classical` checks for `decidable` hypotheses that are used in the proof of a
    proposition but not in the statement, and could be removed using `classical`.
    Theorems in the `decidable` namespace are exempt.
18. `has_coe_to_fun` checks that every type that coerces to a function has a direct
    `has_coe_to_fun` instance.
19. `check_type` checks that the statement of a declaration is well-typed.
20. `check_univs` checks that that there are no bad `max u v` universe levels.

Another linter, `doc_blame_thm`, checks for missing doc strings on lemmas and theorems.
This is not run by default.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint_mathlib+`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks." }

/-- The default linters used in mathlib CI. -/
meta def mathlib_linters : list name := by do
ls ← get_checks tt [] ff,
let ls := ls.map (λ ⟨n, _⟩, `linter ++ n),
exact (reflect ls)
