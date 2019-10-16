/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
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

  Currently this will check for
  1. unused arguments in declarations,
  2. whether a declaration is incorrectly marked as a def/lemma,
  3. whether a namespace is duplicated in the name of a declaration
  4. whether ≥/> is used in the declaration

  You can append a `-` to any command (e.g. `#lint_mathlib-`) to omit the slow tests (4).

  You can customize the performed checks like this:
  ```
  meta def my_check (d : declaration) : tactic (option string) :=
  return $ if d.to_name = `foo then some "gotcha!" else none
  run_cmd lint tt [(my_check, "found nothing", "found something")] >>= trace
  ```

  ## Tags
  sanity check, lint, cleanup, command, tactic
-/

universe variable u
open expr tactic native

reserve notation `#lint`
reserve notation `#lint_mathlib`
reserve notation `#lint_all`

@[user_attribute]
meta def nolint_attr : user_attribute :=
{ name := "nolint",
  descr := "Do not report this declaration in any of the tests of `#lint`" }

attribute [nolint] imp_intro
  classical.dec classical.dec_pred classical.dec_rel classical.dec_eq

meta structure linter :=
(test : declaration → tactic (option string))
(no_errors_found : string)
(errors_found : string)
(is_fast : bool := tt)

meta def get_linters (l : list name) : tactic (list linter) :=
l.mmap (λ n, mk_const n >>= eval_expr linter)

@[user_attribute]
meta def linter_attr : user_attribute (list linter) unit :=
{ name := "linter",
  descr := "Use this declaration as a linting test in #lint",
  after_set := some $ λ nm _ _,
                mk_const nm >>= infer_type >>= unify `(linter),
  cache_cfg := ⟨get_linters, []⟩ }

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

/- Check for unused arguments, and print them with their position, variable name, type and whether
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

@[linter] meta def linter.unused_arguments : linter :=
{ test := unused_arguments,
  no_errors_found := "No unused arguments",
  errors_found := "UNUSED ARGUMENTS" }

/-- Checks whether the correct declaration constructor (definition of theorem) by comparing it
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

@[linter] meta def linter.incorrect_def_lemma : linter :=
{ test := incorrect_def_lemma,
  no_errors_found := "All declarations correctly marked as def/lemma",
  errors_found := "INCORRECT DEF/LEMMA" }

/-- Checks whether a declaration has a namespace twice consecutively in its name -/
meta def dup_namespace (d : declaration) : tactic (option string) :=
is_instance d.to_name >>= λ is_inst,
return $ let nm := d.to_name.components in if nm.chain' (≠) ∨ is_inst then none
  else let s := (nm.find $ λ n, nm.count n ≥ 2).iget.to_string in
  some $ "The namespace `" ++ s ++ "` is duplicated in the name"

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

@[linter] meta def linter.illegal_constants : linter :=
{ test := illegal_constants_in_statement,
  no_errors_found := "No illegal constants in declarations",
  errors_found := "ILLEGAL CONSTANTS IN DECLARATIONS",
  is_fast := ff }

meta def get_checks (slow : bool := tt) :
  tactic (list ((declaration → tactic (option string)) × string × string)) :=
do linter_list ← if slow then linter_attr.get_cache
                         else list.filter (λ ltr, ltr.is_fast) <$> linter_attr.get_cache,
   return $ linter_list.map $ λ ⟨f, s1, s2, _⟩, ⟨f, s1, s2⟩

/-- The common denominator of `#lint[|mathlib|all]`.
  The different commands have different configurations for `l`, `printer` and `where_desc`.
  If `slow` is false, doesn't do the checks that take a lot of time.
  By setting `checks` you can customize which checks are performed. -/
meta def lint_aux (l : list declaration)
  (printer : (declaration → tactic (option string)) → tactic format)
  (where_desc : string) (slow : bool)
  (checks : list ((declaration → tactic (option string)) × string × string)) : tactic format := do
  let s : format := "/- Note: This command is still in development. -/\n",
  let s := s ++ format!"/- Checking {l.length} declarations {where_desc} -/\n\n",
  s ← checks.mfoldl (λ s ⟨tac, ok_string, warning_string⟩, show tactic format, from do
    f ← printer tac,
    return $ s ++ if f.is_nil then format!"/- OK: {ok_string}. -/\n"
  else format!"/- {warning_string}: -/" ++ f ++ "\n\n") s,
  return $ if slow then s else s ++ "/- (slow tests skipped) -/\n"

/-- Return the message printed by `#lint`. -/
meta def lint (slow : bool := tt) : tactic format := do
  checks ← get_checks slow,
  e ← get_env,
  l ← e.mfilter (λ d,
    if e.in_current_file' d.to_name ∧ ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  lint_aux l (λ t, print_decls <$> fold_over_with_cond l t)
    "in the current file" slow checks

/-- Return the message printed by `#lint_mathlib`. -/
meta def lint_mathlib (slow : bool := tt) : tactic format := do
  checks ← get_checks slow,
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
meta def lint_all (slow : bool := tt) : tactic format := do
  checks ← get_checks slow,
  e ← get_env,
  l ← e.mfilter (λ d, if ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  lint_aux l (λ t, print_decls_sorted <$> fold_over_with_cond_sorted l t)
    "in all imported files (including this one)" slow checks

/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
  in that file. -/
@[user_command] meta def lint_cmd (_ : parse $ tk "#lint") : parser unit :=
do b ← optional (tk "-"), s ← lint b.is_none, trace s

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes. -/
@[user_command] meta def lint_mathlib_cmd (_ : parse $ tk "#lint_mathlib") :
  parser unit :=
do b ← optional (tk "-"), s ← lint_mathlib b.is_none, trace s

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes. -/
@[user_command] meta def lint_all_cmd (_ : parse $ tk "#lint_all") :
  parser unit :=
do b ← optional (tk "-"), s ← lint_all b.is_none, trace s

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
-- #lint_mathlib
-- #lint_all
-- #lint-
-- #lint_mathlib-
-- #lint_all-
