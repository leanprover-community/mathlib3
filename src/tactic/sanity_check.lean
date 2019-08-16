/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import tactic.core

/-!
# sanity_check command
 This file defines the `#sanity_check` and `#sanity_check_mathlib` commands, to spot common mistakes in the current file or in all of mathlib, respectively.

 Currently this will check for unused arguments in declarations and whether a declaration is incorrectly marked as a def/lemma.

 ## Tags
 sanity check, sanity_check, cleanup, command, tactic
-/

universe variable u
open expr tactic native

reserve notation `#sanity_check`
reserve notation `#sanity_check_mathlib`

setup_tactic_parser

/-- Find all (non-internal) declarations where tac returns `some x` and list them. -/
meta def fold_over_with_cond {α} (tac : declaration → tactic (option α)) :
  tactic (list (declaration × α)) :=
do e ← get_env,
   e.mfold [] $ λ d ds,
     if name.is_internal d.to_name then return ds else
     do o ← tac d,
     if h : o.is_some then return $ (d, option.get h)::ds else return ds

/-- Find all declarations where tac returns `some x` and sort the resulting list by file name. -/
meta def fold_over_with_cond_sorted {α} (tac : declaration → tactic (option α)) :
  tactic (list (string × list (declaration × α))) :=
do e ← get_env,
   ds ← fold_over_with_cond tac,
   let ds₂ := rb_lmap.of_list (ds.map (λ x, ((e.decl_olean x.1.to_name).get_or_else "", x))),
   return $ ds₂.to_list

/-- Make the output of `fold_over_with_cond` printable, in the following form:
      #print <name> -- <elt of α> -/
meta def print_decls {α} [has_to_format α] (ds : list (declaration × α)) : format :=
ds.foldl
  (λ f x, f ++ format.line ++ to_fmt "#print " ++ to_fmt x.1.to_name ++ " -- " ++ to_fmt x.2)
  format.nil

/-- Make the output of `fold_over_with_cond_sorted` printable, with the file path + name inserted.-/
meta def print_decls_sorted {α} [has_to_format α] (ds : list (string × list (declaration × α))) :
  format :=
ds.foldl
  (λ f x, f ++ format.line ++ format.line ++ to_fmt "-- " ++ to_fmt x.1 ++ print_decls x.2)
  format.nil

/- Print all (non-internal) declarations where tac return `some x`-/
meta def print_all_decls {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
print_decls_sorted <$> fold_over_with_cond_sorted tac

/- Print (non-internal) declarations in the current file where tac return `some x`-/
meta def print_decls_current_file {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
print_decls <$> fold_over_with_cond
  (λ d, d.in_current_file >>= λ b, if b then tac d else return none)

/- Print (non-internal) declarations in mathlib where tac return `some x` -/
meta def print_decls_mathlib {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
do ml ← get_mathlib_dir,
   f ← fold_over_with_cond_sorted
   (λ d, is_in_mathlib_aux ml d.to_name >>= λ b,
      if b then tac d else return none),
   return $ print_decls_sorted $ f.map (λ x, ⟨x.1.popn ml.length, x.2⟩)

/-- Auxilliary definition for `check_unused_arguments_aux` -/
meta def check_unused_arguments_aux : list ℕ → ℕ → ℕ → expr → list ℕ
:= λ l n n_max e,
if n > n_max then l else
if ¬is_lambda e then
  if e = const `true.intro [] ∨ e = const `trivial [] then [] else l -- don't return if the target is true
else
  let b := e.binding_body in
  let l' := if b.has_var_idx 0 then l else n :: l in check_unused_arguments_aux l' (n+1) n_max b

/-- Check which arguments of a declaration are not used.
  Prints a list of natural numbers corresponding to which arguments are not used (e.g.
    this outputs [1, 4] if the first and fourth arguments are unused).
  We return [] if the body of `e` is `true.intro` or `trivial`,
    to filter many automatically generated declarations.
  We don't print arguments that are larger than the arity of the type of the declaration. -/
meta def check_unused_arguments (d : declaration) : option (list ℕ) :=
let l := check_unused_arguments_aux [] 1 (d.type.pi_arity) d.value in
if l = [] then none else l.reverse

/-- Get all declarations with unused arguments -/
meta def get_all_unused_args : tactic unit :=
print_all_decls (return ∘ check_unused_arguments) >>= trace

/-- Get all declarations in mathlib with unused arguments -/
meta def get_all_unused_args_mathlib : tactic unit :=
print_decls_mathlib (return ∘ check_unused_arguments) >>= trace

/-- Get all declarations in current file with unused arguments. -/
meta def get_all_unused_args_current_file : tactic unit :=
print_decls_current_file (return ∘ check_unused_arguments) >>= trace

/-- Checks whether the correct declaration constructor (definition of theorem) by comparing it
  to its sort. This will automatically remove all instances and automatically generated
  definitions -/
meta def incorrect_def_lemma (d : declaration) : tactic (option string) :=
do
  e ← get_env,
  expr.sort n ← infer_type d.type,
  if d.is_constant ∨ d.is_axiom ∨ (e.is_projection d.to_name).is_some ∨
    (d.is_definition : bool) = (n ≠ level.zero : bool) ∨
    (d.to_name.last ∈ ["inj","inj_eq","sizeof_spec"] ∧
      e.is_constructor d.to_name.get_prefix) ∨
    (d.to_name.last ∈ ["dcases_on","drec_on","drec","cases_on","rec_on","binduction_on"] ∧
      e.is_inductive d.to_name.get_prefix)
    then return none
    else (option.is_some <$> try_core (has_attribute `instance d.to_name)) >>=
    λ b, return $ if b then none
    else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
    else "is a lemma/theorem, should be a def"

/-- Get all declarations in mathlib incorrectly marked as def/lemma -/
meta def incorrect_def_lemma_mathlib : tactic unit :=
print_decls_mathlib (return ∘ check_unused_arguments) >>= trace

/-- The command `#sanity_check` at the bottom of a file will warn you about some common mistakes
  in that file. -/
@[user_command] meta def sanity_check_cmd (_ : parse $ tk "#sanity_check") : parser unit :=
do
  trace "/- Note: This command is still in development. -/\n",
  f ← print_decls_current_file (return ∘ check_unused_arguments),
  if f.is_nil then trace "/- OK: No unused arguments in the current file. -/"
  else trace (to_fmt "/- Unused arguments in the current file: -/" ++ f ++ format.line),
  f ← print_decls_current_file incorrect_def_lemma,
  if f.is_nil then trace "/-OK: All declarations correctly marked as def/lemma -/"
  else trace (to_fmt "/- Declarations incorrectly marked as def/lemma: -/" ++ f ++ format.line),
  skip

/-- The command `#sanity_check_mathlib` checks all of mathlib for certain mistakes. -/
@[user_command] meta def sanity_check_mathlib_cmd (_ : parse $ tk "#sanity_check_mathlib") :
  parser unit :=
do
  trace "/- Note: This command is still in development. -/\n",
  f ← print_decls_mathlib (return ∘ check_unused_arguments),
  trace (to_fmt "/- UNUSED ARGUMENTS: -/" ++ f ++ format.line),
  f ← print_decls_mathlib incorrect_def_lemma,
  trace (to_fmt "/- INCORRECT DEF/LEMMA: -/" ++ f ++ format.line),
  skip

-- #sanity_check
-- #sanity_check_mathlib
