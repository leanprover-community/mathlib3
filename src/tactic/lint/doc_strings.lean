/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.lint.basic

/-!
# Linter for documentation strings

This file defines two linters, `doc_blame` and `doc_blame_thm`, that check
whether every definition (and theorem, resp.) has a documentation string.
Only the `doc_blame` linter is enabled by default.
-/

open tactic

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
  no_errors_found := "No definitions are missing documentation.",
  errors_found := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS" }

/-- A linter for checking theorem doc strings. This is not in the default linter set. -/
meta def linter.doc_blame_thm : linter :=
{ test := doc_blame_report_thm,
  no_errors_found := "No theorems are missing documentation.",
  errors_found := "THEOREMS ARE MISSING DOCUMENTATION STRINGS",
  is_fast := ff }
