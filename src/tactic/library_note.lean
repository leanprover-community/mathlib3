/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

/-!
# Library notes

At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

An example from `meta.expr`:

```
library_note "open expressions"
"Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x)."
```

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Since these notes are used in files imported by `tactic.core`, this file has no imports.

## Implementation details

`library_note note_id note_msg` creates a declaration `` `library_note.i `` for some `i`.
This declaration is a pair of strings `note_id` and `note_msg`, and it gets tagged with the
`library_note` attribute.
-/

/-- A rudimentary hash function on strings. -/
def string.hash (s : string) : ℕ :=
s.fold 1 (λ h c, (33*h + c.val) % unsigned_sz)

/-- A user attribute `library_note` for tagging decls of type `string × string` for use in note output. -/
@[user_attribute] meta def library_note_attr : user_attribute :=
{ name := `library_note,
  descr := "Notes about library features to be included in documentation" }

open tactic

/-- Creates a name to store `note_id`. -/
private meta def get_name_for (note_id : string) : name :=
`library_note <.> ("_" ++ to_string note_id.hash)

/-- If `note_name` and `note` are `pexpr`s representing strings,
`add_library_note note_name note` adds a declaration of type `string × string` and tags it with
the `library_note` attribute. -/
meta def tactic.add_library_note (note_name note : pexpr) : tactic unit :=
do note_name ← to_expr note_name,
   note ← to_expr note,
   let decl_name := get_name_for (to_string note_name),
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
