/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.lint.basic

/-!
# Various linters

This file defines several small linters:
  - `ge_or_gt` checks that `>` and `≥` do not occur in the statement of theorems.
  - `dup_namespace` checks that no declaration has a duplicated namespace such as `list.list.monad`.
  - `unused_arguments` checks that definitions and theorems do not have unused arguments.
  - `doc_blame` checks that every definition has a documentation string
  - `doc_blame_thm` checks that every theorem has a documentation string (not enabled by default)
  - `def_lemma` checks that a declaration is a lemma iff its type is a proposition.
-/

open tactic expr



/-!
## Linter against use of `>`/`≥`
-/

/-- Checks whether a `>`/`≥` is used in the statement of `d`.
Currently it checks only the conclusion of the declaration, to eliminate false positive from
binders such as `∀ ε > 0, ...` -/
private meta def ge_or_gt_in_statement (d : declaration) : tactic (option string) :=
return $ let illegal := [`gt, `ge] in if d.type.pi_codomain.contains_constant (λ n, n ∈ illegal)
  then some "the type contains ≥/>. Use ≤/< instead."
  else none

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

/-- A linter for checking whether illegal constants (≥, >) appear in a declaration's type. -/
@[linter] meta def linter.ge_or_gt : linter :=
{ test := ge_or_gt_in_statement,
  auto_decls := ff,
  no_errors_found := "Not using ≥/> in declarations",
  errors_found := "USING ≥/> IN DECLARATIONS",
  is_fast := ff }

/--
Currently, the linter forbids the use of `>` and `≥` in definitions and
statements, as they cause problems in rewrites. However, we still allow them in some contexts,
for instance when expressing properties of the operator (as in `cobounded (≥)`), or in quantifiers
such as `∀ ε > 0`. Such statements should be marked with the attribute `nolint` to avoid linter
failures.
-/
library_note "nolint_ge"

/-!
## Linter for duplicate namespaces
-/

/-- Checks whether a declaration has a namespace twice consecutively in its name -/
private meta def dup_namespace (d : declaration) : tactic (option string) :=
is_instance d.to_name >>= λ is_inst,
return $ let nm := d.to_name.components in if nm.chain' (≠) ∨ is_inst then none
  else let s := (nm.find $ λ n, nm.count n ≥ 2).iget.to_string in
  some $ "The namespace `" ++ s ++ "` is duplicated in the name"

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[linter] meta def linter.dup_namespace : linter :=
{ test := dup_namespace,
  auto_decls := ff,
  no_errors_found := "No declarations have a duplicate namespace",
  errors_found := "DUPLICATED NAMESPACES IN NAME" }



/-!
## Linter for unused arguments
-/

/-- Auxilliary definition for `check_unused_arguments` -/
private meta def check_unused_arguments_aux : list ℕ → ℕ → ℕ → expr → list ℕ | l n n_max e :=
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
This tactic additionally filters out all unused arguments of type `parse _`. -/
private meta def unused_arguments (d : declaration) : tactic (option string) := do
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
  auto_decls := ff,
  no_errors_found := "No unused arguments",
  errors_found := "UNUSED ARGUMENTS" }

attribute [nolint unused_arguments] imp_intro



/-!
## Linter for documentation strings
-/

/-- Reports definitions and constants that are missing doc strings -/
private meta def doc_blame_report_defn : declaration → tactic (option string)
| (declaration.defn n _ _ _ _ _) := doc_string n >> return none <|> return "def missing doc string"
| (declaration.cnst n _ _ _) := doc_string n >> return none <|> return "constant missing doc string"
| _ := return none

/-- Reports definitions and constants that are missing doc strings -/
private meta def doc_blame_report_thm : declaration → tactic (option string)
| (declaration.thm n _ _ _) := doc_string n >> return none <|> return "theorem missing doc string"
| _ := return none

/-- A linter for checking definition doc strings -/
@[linter] meta def linter.doc_blame : linter :=
{ test := λ d, mcond (bnot <$> has_attribute' `instance d.to_name)
    (doc_blame_report_defn d) (return none),
  auto_decls := ff,
  no_errors_found := "No definitions are missing documentation.",
  errors_found := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS" }

/-- A linter for checking theorem doc strings. This is not in the default linter set. -/
meta def linter.doc_blame_thm : linter :=
{ test := doc_blame_report_thm,
  auto_decls := ff,
  no_errors_found := "No theorems are missing documentation.",
  errors_found := "THEOREMS ARE MISSING DOCUMENTATION STRINGS",
  is_fast := ff }



/-!
## Linter for correct usage of `lemma`/`def`
-/

/--
Checks whether the correct declaration constructor (definition or theorem) by
comparing it to its sort. Instances will not be printed.

This test is not very quick: maybe we can speed-up testing that something is a proposition?
This takes almost all of the execution time.
-/
private meta def incorrect_def_lemma (d : declaration) : tactic (option string) :=
  if d.is_constant ∨ d.is_axiom
  then return none else do
    is_instance_d ← is_instance d.to_name,
    if is_instance_d then return none else do
      -- the following seems to be a little quicker than `is_prop d.type`.
      expr.sort n ← infer_type d.type, return $
      if d.is_theorem ↔ n = level.zero then none
      else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
      else "is a lemma/theorem, should be a def"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[linter] meta def linter.def_lemma : linter :=
{ test := incorrect_def_lemma,
  auto_decls := ff,
  no_errors_found := "All declarations correctly marked as def/lemma",
  errors_found := "INCORRECT DEF/LEMMA" }

attribute [nolint def_lemma] classical.dec classical.dec_pred classical.dec_rel classical.dec_eq
