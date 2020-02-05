/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

/-!
# Documentation commands

We generate html documentation from mathlib. It is convenient to collect lists of tactics, commands,
notes, etc. To facilitate this, we declare these documentation entries in the library
using special commands.

* `library_note` adds a note describing a certain feature or design decision. These can be referenced
  in doc strings with the text `note [name of note]`.
* `add_tactic_doc` adds an entry documenting an interactive tactic, command, hole command, or
  attribute.

Since these commands are used in files imported by `tactic.core`, this file has no imports.

## Implementation details

`library_note note_id note_msg` creates a declaration `` `library_note.i `` for some `i`.
This declaration is a pair of strings `note_id` and `note_msg`, and it gets tagged with the
`library_note` attribute.

Similarly, `add_tactic_doc` creates a declaration `` `tactic_doc.i `` that stores the provided
information.
-/

/-- A rudimentary hash function on strings. -/
def string.hash (s : string) : ℕ :=
s.fold 1 (λ h c, (33*h + c.val) % unsigned_sz)

/-- `mk_hashed_name nspace id` hashes the string `id` to a value `i` and returns the name `nspace._i` -/
meta def string.mk_hashed_name (nspace : name) (id : string) : name :=
nspace <.> ("_" ++ to_string id.hash)

/-! ### The `library_note` command -/

/-- A user attribute `library_note` for tagging decls of type `string × string` for use in note output. -/
@[user_attribute] meta def library_note_attr : user_attribute :=
{ name := `library_note,
  descr := "Notes about library features to be included in documentation" }

open tactic

/-- If `note_name` and `note` are `pexpr`s representing strings,
`add_library_note note_name note` adds a declaration of type `string × string` and tags it with
the `library_note` attribute. -/
meta def tactic.add_library_note (note_name note : pexpr) : tactic unit :=
do note_name ← to_expr note_name,
   let decl_name := (to_string note_name).mk_hashed_name `library_note,
   body ← to_expr ``((%%note_name, %%note) : string × string),
   add_decl $ mk_definition decl_name [] `(string × string) body,
   library_note_attr.set decl_name () tt none

open lean lean.parser interactive
/-- A command to add library notes. Syntax:
```
library_note "note id" "note content"
``` -/
@[user_command] meta def library_note (_ : parse (tk "library_note")) : parser unit :=
do name ← parser.pexpr,
   note ← parser.pexpr,
   of_tactic $ tactic.add_library_note name note

/-- Collects all notes in the current environment. Returns a list of pairs `(note_id, note_content)` -/
meta def tactic.get_library_notes : tactic (list (string × string)) :=
attribute.get_instances `library_note >>= list.mmap (λ dcl, mk_const dcl >>= eval_expr (string × string))

/-! ### The `add_tactic_doc_entry` command -/

/-- The categories of tactic doc entry. -/
@[derive [decidable_eq, has_reflect]]
inductive doc_category
| tactic | cmd | hole_cmd | attr

/-- The information used to generate a tactic doc entry -/
structure tactic_doc_entry :=
(name : string)
(category : doc_category)
(decl_names : list _root_.name)
(tags : list string := [])
(description : string)

/-- A user attribute `tactic_doc` for tagging decls of type `tactic_doc_entry` for use in doc output -/
@[user_attribute] meta def tactic_doc_entry_attr : user_attribute :=
{ name := `tactic_doc,
  descr := "Information about a tactic to be included in documentation" }

/-- `add_tactic_doc tde` assumes `tde : pexpr` represents a term of type `tactic_doc_entry`.
It adds a declaration to the environment with `tde` as its body and tags it with the `tactic_doc` attribute.
If `tde.decl_names` has exactly one entry, and the referenced declaration is missing a doc string,
it adds `tde.description` as the doc string. -/
meta def tactic.add_tactic_doc (tde : pexpr) : tactic unit :=
do tde_expr ← to_expr ``(%%tde : tactic_doc_entry),
   tde ← eval_expr tactic_doc_entry tde_expr,
   let decl_name := tde.name.mk_hashed_name `tactic_doc,
   add_decl $ mk_definition decl_name [] `(tactic_doc_entry) tde_expr,
   tactic_doc_entry_attr.set decl_name () tt none,
   when (tde.decl_names.length = 1) $ do
     let tac_name := tde.decl_names.head,
     doc_string tac_name >> skip <|> add_doc_string tac_name tde.description <|> skip

@[user_command] meta def add_tactic_doc_command (_ : parse $ tk "add_tactic_doc") : parser unit :=
parser.pexpr >>= of_tactic ∘ tactic.add_tactic_doc .

add_tactic_doc
{ name := "library_note",
  category := doc_category.cmd,
  decl_names := [`library_note],
  tags := ["documentation"],
  description :=
"At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Syntax:
```
library_note \"note id\" \"note message\"
```

An example from `meta.expr`:

```
library_note \"open expressions\"
\"Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).\"
```

This note can be referenced near a usage of `pi_binders`:


```
-- See Note [open expressions]
/-- behavior of f -/
def f := pi_binders ...
```
" }

add_tactic_doc
{ name := "add_tactic_doc",
  category := doc_category.cmd,
  decl_names := [`add_tactic_doc_command],
  tags := ["documentation"],
  description :=
"A command used to add documentation for a tactic, command, hole command, or attribute.

Usage: after defining an interactive tactic, command, or attribute, add its documentation as follows.
```
add_tactic_doc
{ name := \"display name of the tactic\",
  category := cat,
  decl_names := [`dcl_1, dcl_2],
  tags := [\"tag_1\", \"tag_2\"],
  description := \"describe what the command does here\"
}
```

The argument to `add_tactic_doc` is a structure of type `tactic_doc_entry`.
* `name` refers to the display name of the tactic; it is used as the header of the doc entry.
* `cat` refers to the category of doc entry.
  Options: `doc_category.tactic`, `doc_category.cmd`, `doc_category.hole_cmd`, `doc_category.attr`
* `decl_names` is a list of the declarations associated with this doc. For instance,
  the entry for `linarith` would set ``decl_names := [`tactic.interactive.linarith]``.
  Some entries may cover multiple declarations.
  It is only necessary to list the interactive versions of tactics.
* `tags` is an optional list of strings used to categorize entries.
* `description` is the body of the entry.
  What you are reading now is the description of `add_tactic_doc`.

If only one related declaration is listed in `decl_names` and it does not have a doc string,
`description` will be automatically added as its doc string.

Note that providing a badly formed `tactic_doc_entry` to the command can result in strange error messages.
"  }
