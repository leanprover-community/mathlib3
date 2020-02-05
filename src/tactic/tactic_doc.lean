/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.library_note

@[derive [decidable_eq, has_reflect]]
inductive tactic_category
| core |  basic | other

structure tactic_doc_entry :=
(tactic_name : string)
(category : string)
(decl_names : list name)
(description : string)

@[user_attribute] meta def tactic_doc_entry_attr : user_attribute :=
{ name := `tactic_doc,
  descr := "description of a tactic" }

open lean lean.parser interactive interactive.types tactic

@[inline] meta def parse_string : parser string :=
do s ← parser.pexpr,
   of_tactic $ to_expr s >>= eval_expr string

/-- Creates a name to store `note_id`. -/
private meta def get_name_for (note_id : string) : name :=
`tactic_doc <.> ("_" ++ to_string note_id.hash)

meta def tactic.add_tactic_doc (tde : pexpr) : tactic unit :=
do tde_expr ← to_expr ``(%%tde : tactic_doc_entry),
   tde ← eval_expr tactic_doc_entry tde_expr,
   let decl_name := get_name_for tde.tactic_name,
   add_decl $ mk_definition decl_name [] `(tactic_doc_entry) tde_expr,
   tactic_doc_entry_attr.set decl_name () tt none

@[user_command] meta def add_tactic_doc_command (_ : parse $ tk "add_tactic_doc") : parser unit :=
do tde ← parser.pexpr,
   of_tactic $ tactic.add_tactic_doc tde.

add_tactic_doc
{ tactic_name := "linarith",
  category := "other",
  decl_names := [],
  description := "oops"  }

#exit

   category ← of_tactic $ to_expr category >>= eval_expr tactic_category,
   decl_names ← tk "associated_declarations:" >> many ident,
   description ← tk "description:" >> parse_string,
   skip.


add_tactic_doc "linarith"
  tactic_category: tactic_category.other
  associated_declarations: tactic.interactive.linarith
  description: "linear arithmetic "
