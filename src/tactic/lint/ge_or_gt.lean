/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.lint.basic

/-!
# Linter against use of `>`/`≥`

This file defines the `ge_or_gt` linter, which checks that `>` and `≥` do not
occur in the statement of theorems.
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
