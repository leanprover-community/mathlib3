/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.core
/-!
# lint command
This file defines the following user commands to spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

Five linters are run by default:
1. `unused_arguments` checks for unused arguments in declarations
2. `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma
3. `dup_namespce` checks whether a namespace is duplicated in the name of a declaration
4. `illegal_constant` checks whether ≥/> is used in the declaration
5. `doc_blame` checks for missing doc strings on definitions and constants.

A sixth linter, `doc_blame_thm`, checks for missing doc strings on lemmas and theorems.
This is not run by default.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `-` to any command (e.g. `#lint_mathlib-`) to omit the slow tests (4).

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

## Tags
sanity check, lint, cleanup, command, tactic
-/

universe variable u
open expr tactic native

reserve notation `#lint`
reserve notation `#lint_mathlib`
reserve notation `#lint_all`
reserve notation `#list_linters`

run_cmd tactic.skip -- apparently doc strings can't come directly after `reserve notation`

/-- Defines the user attribute `nolint` for skipping `#lint` -/
@[user_attribute]
meta def nolint_attr : user_attribute :=
{ name := "nolint",
  descr := "Do not report this declaration in any of the tests of `#lint`" }

attribute [nolint] imp_intro
  classical.dec classical.dec_pred classical.dec_rel classical.dec_eq

/--
A linting test for the `#lint` command.

`test` defines a test to perform on every declaration. It should never fail. Returning `none`
signifies a passing test. Returning `some msg` reports a failing test with error `msg`.

`no_errors_found` is the message printed when all tests are negative, and `errors_found` is printed
when at least one test is positive.

If `is_fast` is false, this test will be omitted from `#lint-`.
-/
meta structure linter :=
(test : declaration → tactic (option string))
(no_errors_found : string)
(errors_found : string)
(is_fast : bool := tt)

/-- Takes a list of names that resolve to declarations of type `linter`,
and produces a list of linters. -/
meta def get_linters (l : list name) : tactic (list linter) :=
l.mmap (λ n, mk_const n >>= eval_expr linter <|> fail format!"invalid linter: {n}")

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

setup_tactic_parser
universe variable v

/-- Find all declarations in `l` where tac returns `some x` and list them. -/
meta def fold_over_with_cond {α} (l : list declaration) (tac : declaration → tactic (option α)) :
  tactic (list (declaration × α)) :=
l.mmap_filter $ λ d, option.map (λ x, (d, x)) <$> tac d

/-- Find all declarations in `l` where tac returns `some x` and sort the resulting list by file name. -/
meta def fold_over_with_cond_sorted {α} (l : list declaration)
  (tac : declaration → tactic (option α)) : tactic (list (string × list (declaration × α))) := do
  e ← get_env,
  ds ← fold_over_with_cond l tac,
  let ds₂ := rb_lmap.of_list (ds.map (λ x, ((e.decl_olean x.1.to_name).iget, x))),
  return $ ds₂.to_list

/-- Make the output of `fold_over_with_cond` printable, in the following form:
      #print <name> <open multiline comment> <elt of α> <close multiline comment> -/
meta def print_decls {α} [has_to_format α] (ds : list (declaration × α)) : format :=
ds.foldl
  (λ f x, f ++ "\n" ++ to_fmt "#print " ++ to_fmt x.1.to_name ++ " /- " ++ to_fmt x.2 ++ " -/")
  format.nil

/-- Make the output of `fold_over_with_cond_sorted` printable, with the file path + name inserted.-/
meta def print_decls_sorted {α} [has_to_format α] (ds : list (string × list (declaration × α))) :
  format :=
ds.foldl
  (λ f x, f ++ "\n\n" ++ to_fmt "-- " ++ to_fmt x.1 ++ print_decls x.2)
  format.nil

/-- Same as `print_decls_sorted`, but removing the first `n` characters from the string.
  Useful for omitting the mathlib directory from the output. -/
meta def print_decls_sorted_mathlib {α} [has_to_format α] (n : ℕ)
  (ds : list (string × list (declaration × α))) : format :=
ds.foldl
  (λ f x, f ++ "\n\n" ++ to_fmt "-- " ++ to_fmt (x.1.popn n) ++ print_decls x.2)
  format.nil

/-- Auxilliary definition for `check_unused_arguments` -/
meta def check_unused_arguments_aux : list ℕ → ℕ → ℕ → expr → list ℕ | l n n_max e :=
if n > n_max then l else
if ¬ is_lambda e ∧ ¬ is_pi e then l else
  let b := e.binding_body in
  let l' := if b.has_var_idx 0 then l else n :: l in check_unused_arguments_aux l' (n+1) n_max b

/-- Check which arguments of a declaration are not used.
  Prints a list of natural numbers corresponding to which arguments are not used (e.g.
    this outputs [1, 4] if the first and fourth arguments are unused).
  Checks both the type and the value of `d` for whether the argument is used
  (in rare cases an argument is used in the type but not in the value).
  We return [] if the declaration was automatically generated.
  We print arguments that are larger than the arity of the type of the declaration
  (without unfolding definitions). -/
meta def check_unused_arguments (d : declaration) : option (list ℕ) :=
let l := check_unused_arguments_aux [] 1 d.type.pi_arity d.value in
if l = [] then none else
let l2 := check_unused_arguments_aux [] 1 d.type.pi_arity d.type in
(l.filter $ λ n, n ∈ l2).reverse

/-- Check for unused arguments, and print them with their position, variable name, type and whether
  the argument is a duplicate.
  See also `check_unused_arguments`.
  This tactic additionally filters out all unused arguments of type `parse _` -/
meta def unused_arguments (d : declaration) : tactic (option string) := do
  let ns := check_unused_arguments d,
  if ¬ ns.is_some then return none else do
  let ns := ns.iget,
  (ds, _) ← get_pi_binders d.type,
  let ns := ns.map (λ n, (n, (ds.nth $ n - 1).iget)),
  let ns := ns.filter (λ x, x.2.type.get_app_fn ≠ const `interactive.parse []),
  if ns = [] then return none else do
  ds' ← ds.mmap pp,
  ns ← ns.mmap (λ ⟨n, b⟩, (λ s, to_fmt "argument " ++ to_fmt n ++ ": " ++ s ++
    (if ds.countp (λ b', b.type = b'.type) ≥ 2 then " (duplicate)" else "")) <$> pp b),
  return $ some $ ns.to_string_aux tt

/-- A linter object for checking for unused arguments. This is in the default linter set. -/
@[linter] meta def linter.unused_arguments : linter :=
{ test := unused_arguments,
  no_errors_found := "No unused arguments",
  errors_found := "UNUSED ARGUMENTS" }

/-- Checks whether the correct declaration constructor (definition or theorem) by comparing it
  to its sort. Instances will not be printed -/
meta def incorrect_def_lemma (d : declaration) : tactic (option string) := do
  e ← get_env,
  expr.sort n ← infer_type d.type,
  let is_def : Prop := d.is_definition,
  if d.is_constant ∨ d.is_axiom ∨ (is_def ↔ (n ≠ level.zero))
    then return none
    else is_instance d.to_name >>= λ b, return $
    if b then none
    else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
    else "is a lemma/theorem, should be a def"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[linter] meta def linter.def_lemma : linter :=
{ test := incorrect_def_lemma,
  no_errors_found := "All declarations correctly marked as def/lemma",
  errors_found := "INCORRECT DEF/LEMMA" }

/-- Checks whether a declaration has a namespace twice consecutively in its name -/
meta def dup_namespace (d : declaration) : tactic (option string) :=
is_instance d.to_name >>= λ is_inst,
return $ let nm := d.to_name.components in if nm.chain' (≠) ∨ is_inst then none
  else let s := (nm.find $ λ n, nm.count n ≥ 2).iget.to_string in
  some $ "The namespace `" ++ s ++ "` is duplicated in the name"

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[linter] meta def linter.dup_namespace : linter :=
{ test := dup_namespace,
  no_errors_found := "No declarations have a duplicate namespace",
  errors_found := "DUPLICATED NAMESPACES IN NAME" }

/-- Checks whether a `>`/`≥` is used in the statement of `d`. -/
-- TODO: the commented out code also checks for classicality in statements, but needs fixing
-- TODO: this probably needs to also check whether the argument is a variable or @eq <var> _ _
-- meta def illegal_constants_in_statement (d : declaration) : tactic (option string) :=
-- return $ if d.type.contains_constant (λ n, (n.get_prefix = `classical ∧
--   n.last ∈ ["prop_decidable", "dec", "dec_rel", "dec_eq"]) ∨ n ∈ [`gt, `ge])
-- then
--   let illegal1 := [`classical.prop_decidable, `classical.dec, `classical.dec_rel, `classical.dec_eq],
--       illegal2 := [`gt, `ge],
--       occur1 := illegal1.filter (λ n, d.type.contains_constant (eq n)),
--       occur2 := illegal2.filter (λ n, d.type.contains_constant (eq n)) in
--   some $ sformat!"the type contains the following declarations: {occur1 ++ occur2}." ++
--     (if occur1 = [] then "" else " Add decidability type-class arguments instead.") ++
--     (if occur2 = [] then "" else " Use ≤/< instead.")
-- else none
meta def illegal_constants_in_statement (d : declaration) : tactic (option string) :=
return $ let illegal := [`gt, `ge] in if d.type.contains_constant (λ n, n ∈ illegal)
  then some "the type contains ≥/>. Use ≤/< instead."
  else none

/-- A linter for checking whether illegal constants (≥, >) appear in a declaration's type. -/
@[linter] meta def linter.illegal_constants : linter :=
{ test := illegal_constants_in_statement,
  no_errors_found := "No illegal constants in declarations",
  errors_found := "ILLEGAL CONSTANTS IN DECLARATIONS",
  is_fast := ff }

/-- Reports definitions and constants that are missing doc strings -/
meta def doc_blame_report_defn : declaration → tactic (option string)
| (declaration.defn n _ _ _ _ _) := doc_string n >> return none <|> return "def missing doc string"
| (declaration.cnst n _ _ _) := doc_string n >> return none <|> return "constant missing doc string"
| _ := return none

/-- Reports definitions and constants that are missing doc strings -/
meta def doc_blame_report_thm : declaration → tactic (option string)
| (declaration.thm n _ _ _) := doc_string n >> return none <|> return "theorem missing doc string"
| _ := return none

/-- A linter for checking definition doc strings -/
@[linter] meta def linter.doc_blame : linter :=
{ test := λ d, mcond (bnot <$> has_attribute' `instance d.to_name) (doc_blame_report_defn d) (return none),
  no_errors_found := "No definitions are missing documentation.",
  errors_found := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS" }

/-- A linter for checking theorem doc strings. This is not in the default linter set. -/
meta def linter.doc_blame_thm : linter :=
{ test := doc_blame_report_thm,
  no_errors_found := "No theorems are missing documentation.",
  errors_found := "THEOREMS ARE MISSING DOCUMENTATION STRINGS",
  is_fast := ff }

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it filters the linter list to only use fast tests. -/
meta def get_checks (slow : bool) (extra : list name) (use_only : bool) :
  tactic (list linter) :=
do linter_list ← if use_only then return extra else list.append extra <$> attribute.get_instances `linter,
   linter_list ← get_linters linter_list.erase_dup,
   return $ if slow then linter_list else linter_list.filter (λ l, l.is_fast)

/-- The common denominator of `#lint[|mathlib|all]`.
  The different commands have different configurations for `l`, `printer` and `where_desc`.
  If `slow` is false, doesn't do the checks that take a lot of time.
  By setting `checks` you can customize which checks are performed. -/
meta def lint_aux (l : list declaration)
  (printer : (declaration → tactic (option string)) → tactic format)
  (where_desc : string) (slow : bool) (checks : list linter) : tactic format := do
  let s : format := "/- Note: This command is still in development. -/\n",
  let s := s ++ format!"/- Checking {l.length} declarations {where_desc} -/\n\n",
  s ← checks.mfoldl (λ s ⟨tac, ok_string, warning_string, _⟩, show tactic format, from do
    f ← printer tac,
    return $ s ++ if f.is_nil then format!"/- OK: {ok_string}. -/\n"
  else format!"/- {warning_string}: -/" ++ f ++ "\n\n") s,
  return $ if slow then s else s ++ "/- (slow tests skipped) -/\n"

/-- Return the message printed by `#lint`. -/
meta def lint (slow : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic format := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  l ← e.mfilter (λ d,
    if e.in_current_file' d.to_name ∧ ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  lint_aux l (λ t, print_decls <$> fold_over_with_cond l t)
    "in the current file" slow checks

/-- Return the message printed by `#lint_mathlib`. -/
meta def lint_mathlib (slow : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic format := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  ml ← get_mathlib_dir,
  /- note: we don't separate out some of these tests in `lint_aux` because that causes a
    performance hit. That is also the reason for the current formulation using if then else. -/
  l ← e.mfilter (λ d,
    if e.is_prefix_of_file ml d.to_name ∧ ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  let ml' := ml.length,
  lint_aux l (λ t, print_decls_sorted_mathlib ml' <$> fold_over_with_cond_sorted l t)
    "in mathlib (only in imported files)" slow checks

/-- Return the message printed by `#lint_all`. -/
meta def lint_all (slow : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic format := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  l ← e.mfilter (λ d, if ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  lint_aux l (λ t, print_decls_sorted <$> fold_over_with_cond_sorted l t)
    "in all imported files (including this one)" slow checks

/-- Parses an optional `only`, followed by a sequence of zero or more identifiers.
Prepends `linter.` to each of these identifiers. -/
private meta def parse_lint_additions : parser (bool × list name) :=
prod.mk <$> only_flag <*> (list.map (name.append `linter) <$> ident_*)

/-- The common denominator of `lint_cmd`, `lint_mathlib_cmd`, `lint_all_cmd` -/
private meta def lint_cmd_aux (scope : bool → list name → bool → tactic format) : parser unit :=
do b ← optional (tk "-"),
   (use_only, extra) ← parse_lint_additions,
   s ← scope b.is_none extra use_only,
   trace s

/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
  in that file. -/
@[user_command] meta def lint_cmd (_ : parse $ tk "#lint") : parser unit :=
lint_cmd_aux @lint

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes. -/
@[user_command] meta def lint_mathlib_cmd (_ : parse $ tk "#lint_mathlib") : parser unit :=
lint_cmd_aux @lint_mathlib

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes. -/
@[user_command] meta def lint_all_cmd (_ : parse $ tk "#lint_all") : parser unit :=
lint_cmd_aux @lint_all

/-- The command `#list_linters` prints a list of all available linters. -/
@[user_command] meta def list_linters (_ : parse $ tk "#list_linters") : parser unit :=
do env ← get_env,
let ns := env.decl_filter_map $ λ dcl,
    if (dcl.to_name.get_prefix = `linter) && (dcl.type = `(linter)) then some dcl.to_name else none,
   trace "Available linters:\n  linters marked with (*) are in the default lint set\n",
   ns.mmap' $ λ n, do
     b ← has_attribute' `linter n,
     trace $ n.pop_prefix.to_string ++ if b then " (*)" else ""

/-- Use `lint` as a hole command. Note: In a large file, there might be some delay between
  choosing the option and the information appearing -/
@[hole_command] meta def lint_hole_cmd : hole_command :=
{ name := "Lint",
  descr := "Lint: Find common mistakes in current file.",
  action := λ es, do s ← lint, return [(s.to_string,"")] }

-- set_option profiler true
-- run_cmd lint
-- run_cmd lint_mathlib
-- run_cmd lint_all
-- #lint
-- #lint only unused_arguments dup_namespace
-- #lint_mathlib
-- #lint_all
-- #lint-
-- #lint_mathlib-
-- #lint_all-
-- #list_linters
