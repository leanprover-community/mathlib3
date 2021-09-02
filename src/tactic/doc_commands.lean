/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import tactic.fix_reflect_string

/-!
# Documentation commands

We generate html documentation from mathlib. It is convenient to collect lists of tactics, commands,
notes, etc. To facilitate this, we declare these documentation entries in the library
using special commands.

* `library_note` adds a note describing a certain feature or design decision. These can be
  referenced in doc strings with the text `note [name of note]`.
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

/-- `mk_hashed_name nspace id` hashes the string `id` to a value `i` and returns the name
`nspace._i` -/
meta def string.mk_hashed_name (nspace : name) (id : string) : name :=
nspace <.> ("_" ++ to_string id.hash)

open tactic

/--
`copy_doc_string fr to` copies the docstring from the declaration named `fr`
to each declaration named in the list `to`. -/
meta def tactic.copy_doc_string (fr : name) (to : list name) : tactic unit :=
do fr_ds ← doc_string fr,
   to.mmap' $ λ tgt, add_doc_string tgt fr_ds

open lean lean.parser interactive

/--
`copy_doc_string source → target_1 target_2 ... target_n` copies the doc string of the
declaration named `source` to each of `target_1`, `target_2`, ..., `target_n`.
 -/
@[user_command] meta def copy_doc_string_cmd
  (_ : parse (tk "copy_doc_string")) : parser unit :=
do fr ← parser.ident,
   tk "->",
   to ← parser.many parser.ident,
   expr.const fr _  ← resolve_name fr,
   to ← parser.of_tactic (to.mmap $ λ n, expr.const_name <$> resolve_name n),
   tactic.copy_doc_string fr to

/-! ### The `library_note` command -/

/-- A user attribute `library_note` for tagging decls of type `string × string` for use in note
output. -/
@[user_attribute] meta def library_note_attr : user_attribute :=
{ name := `library_note,
  descr := "Notes about library features to be included in documentation",
  parser := failed }

/--
`mk_reflected_definition name val` constructs a definition declaration by reflection.

Example: ``mk_reflected_definition `foo 17`` constructs the definition
declaration corresponding to `def foo : ℕ := 17`
-/
meta def mk_reflected_definition (decl_name : name) {type} [reflected type]
  (body : type) [reflected body] : declaration :=
mk_definition decl_name (reflect type).collect_univ_params (reflect type) (reflect body)

/-- If `note_name` and `note` are `pexpr`s representing strings,
`add_library_note note_name note` adds a declaration of type `string × string` and tags it with
the `library_note` attribute. -/
meta def tactic.add_library_note (note_name note : string) : tactic unit :=
do let decl_name := note_name.mk_hashed_name `library_note,
   add_decl $ mk_reflected_definition decl_name (note_name, note),
   library_note_attr.set decl_name () tt none

open tactic

/--
A command to add library notes. Syntax:
```
/--
note message
-/
library_note "note id"
```
-/
@[user_command] meta def library_note (mi : interactive.decl_meta_info)
  (_ : parse (tk "library_note")) : parser unit := do
note_name ← parser.pexpr,
note_name ← eval_pexpr string note_name,
some doc_string ← pure mi.doc_string | fail "library_note requires a doc string",
add_library_note note_name doc_string

/-- Collects all notes in the current environment.
Returns a list of pairs `(note_id, note_content)` -/
meta def tactic.get_library_notes : tactic (list (string × string)) :=
attribute.get_instances `library_note >>=
  list.mmap (λ dcl, mk_const dcl >>= eval_expr (string × string))

/-! ### The `add_tactic_doc_entry` command -/

/-- The categories of tactic doc entry. -/
@[derive [decidable_eq, has_reflect]]
inductive doc_category
| tactic | cmd | hole_cmd | attr

/-- Format a `doc_category` -/
meta def doc_category.to_string : doc_category → string
| doc_category.tactic := "tactic"
| doc_category.cmd := "command"
| doc_category.hole_cmd := "hole_command"
| doc_category.attr := "attribute"

meta instance : has_to_format doc_category := ⟨↑doc_category.to_string⟩

/-- The information used to generate a tactic doc entry -/
@[derive has_reflect]
structure tactic_doc_entry :=
(name : string)
(category : doc_category)
(decl_names : list _root_.name)
(tags : list string := [])
(description : string := "")
(inherit_description_from : option _root_.name := none)

/-- Turns a `tactic_doc_entry` into a JSON representation. -/
meta def tactic_doc_entry.to_json (d : tactic_doc_entry) : json :=
json.object [
  ("name", d.name),
  ("category", d.category.to_string),
  ("decl_names", d.decl_names.map (json.of_string ∘ to_string)),
  ("tags", d.tags.map json.of_string),
  ("description", d.description)
]

meta instance : has_to_string tactic_doc_entry :=
⟨json.unparse ∘ tactic_doc_entry.to_json⟩

/-- `update_description_from tde inh_id` replaces the `description` field of `tde` with the
    doc string of the declaration named `inh_id`. -/
meta def tactic_doc_entry.update_description_from (tde : tactic_doc_entry) (inh_id : name) :
  tactic tactic_doc_entry :=
do ds ← doc_string inh_id <|> fail (to_string inh_id ++ " has no doc string"),
   return { description := ds .. tde }

/--
`update_description tde` replaces the `description` field of `tde` with:

* the doc string of `tde.inherit_description_from`, if this field has a value
* the doc string of the entry in `tde.decl_names`, if this field has length 1

If neither of these conditions are met, it returns `tde`. -/
meta def tactic_doc_entry.update_description (tde : tactic_doc_entry) : tactic tactic_doc_entry :=
match tde.inherit_description_from, tde.decl_names with
| some inh_id, _ := tde.update_description_from inh_id
| none, [inh_id] := tde.update_description_from inh_id
| none, _ := return tde
end

/-- A user attribute `tactic_doc` for tagging decls of type `tactic_doc_entry`
for use in doc output -/
@[user_attribute] meta def tactic_doc_entry_attr : user_attribute :=
{ name := `tactic_doc,
  descr := "Information about a tactic to be included in documentation",
  parser := failed }

/-- Collects everything in the environment tagged with the attribute `tactic_doc`. -/
meta def tactic.get_tactic_doc_entries : tactic (list tactic_doc_entry) :=
attribute.get_instances `tactic_doc >>=
  list.mmap (λ dcl, mk_const dcl >>= eval_expr tactic_doc_entry)

/-- `add_tactic_doc tde` adds a declaration to the environment
with `tde` as its body and tags it with the `tactic_doc`
attribute. If `tde.decl_names` has exactly one entry `` `decl`` and
if `tde.description` is the empty string, `add_tactic_doc` uses the doc
string of `decl` as the description. -/
meta def tactic.add_tactic_doc (tde : tactic_doc_entry) : tactic unit :=
do when (tde.description = "" ∧ tde.inherit_description_from.is_none ∧ tde.decl_names.length ≠ 1) $
     fail "A tactic doc entry must either:
 1. have a description written as a doc-string for the `add_tactic_doc` invocation, or
 2. have a single declaration in the `decl_names` field, to inherit a description from, or
 3. explicitly indicate the declaration to inherit the description from using
    `inherit_description_from`.",
   tde ← if tde.description = "" then tde.update_description else return tde,
   let decl_name := (tde.name ++ tde.category.to_string).mk_hashed_name `tactic_doc,
   add_decl $ mk_definition decl_name [] `(tactic_doc_entry) (reflect tde),
   tactic_doc_entry_attr.set decl_name () tt none

/--
A command used to add documentation for a tactic, command, hole command, or attribute.

Usage: after defining an interactive tactic, command, or attribute,
add its documentation as follows.
```lean
/--
describe what the command does here
-/
add_tactic_doc
{ name := "display name of the tactic",
  category := cat,
  decl_names := [`dcl_1, `dcl_2],
  tags := ["tag_1", "tag_2"]
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
* The doc string is the body of the entry. It can be formatted with markdown.
  What you are reading now is the description of `add_tactic_doc`.

If only one related declaration is listed in `decl_names` and if this
invocation of `add_tactic_doc` does not have a doc string, the doc string of
that declaration will become the body of the tactic doc entry. If there are
multiple declarations, you can select the one to be used by passing a name to
the `inherit_description_from` field.

If you prefer a tactic to have a doc string that is different then the doc entry,
you should write the doc entry as a doc string for the `add_tactic_doc` invocation.

Note that providing a badly formed `tactic_doc_entry` to the command can result in strange error
messages.

-/
@[user_command] meta def add_tactic_doc_command (mi : interactive.decl_meta_info)
  (_ : parse $ tk "add_tactic_doc") : parser unit := do
pe ← parser.pexpr,
e ← eval_pexpr tactic_doc_entry pe,
let e : tactic_doc_entry := match mi.doc_string with
  | some desc := { description := desc, ..e }
  | none := e
  end,
tactic.add_tactic_doc e .

/--
At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Syntax:
```
/--
note message
-/
library_note "note id"
```

An example from `meta.expr`:

```
/--
Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).
-/
library_note "open expressions"
```

This note can be referenced near a usage of `pi_binders`:


```
-- See Note [open expressions]
/-- behavior of f -/
def f := pi_binders ...
```
-/
add_tactic_doc
{ name                     := "library_note",
  category                 := doc_category.cmd,
  decl_names               := [`library_note, `tactic.add_library_note],
  tags                     := ["documentation"],
  inherit_description_from := `library_note }

add_tactic_doc
{ name                     := "add_tactic_doc",
  category                 := doc_category.cmd,
  decl_names               := [`add_tactic_doc_command, `tactic.add_tactic_doc],
  tags                     := ["documentation"],
  inherit_description_from := `add_tactic_doc_command }

add_tactic_doc
{ name := "copy_doc_string",
  category := doc_category.cmd,
  decl_names := [`copy_doc_string_cmd, `tactic.copy_doc_string],
  tags := ["documentation"],
  inherit_description_from := `copy_doc_string_cmd }

-- add docs to core tactics

/--
The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
  (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
  f x = x :=
by cc
```

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.

The `cc` implementation in Lean does a few more tricks: for example it
derives `a=b` from `nat.succ a = nat.succ b`, and `nat.succ a !=
nat.zero` for any `a`.

* The starting reference point is Nelson, Oppen, [Fast decision procedures based on congruence
closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf),
Journal of the ACM (1980)

* The congruence lemmas for dependent type theory as used in Lean are described in
[Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf)
(de Moura, Selsam IJCAR 2016).
-/
add_tactic_doc
{ name := "cc (congruence closure)",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.cc],
  tags := ["core", "finishing"] }

/--
`conv {...}` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://leanprover-community.github.io/extras/conv.html> for more details.

Inside `conv` blocks, mathlib currently additionally provides
* `erw`,
* `ring`, `ring2` and `ring_exp`,
* `norm_num`,
* `norm_cast`,
* `apply_congr`, and
* `conv` (within another `conv`).

`apply_congr` applies congruence lemmas to step further inside expressions,
and sometimes gives between results than the automatically generated
congruence lemmas used by `congr`.

Using `conv` inside a `conv` block allows the user to return to the previous
state of the outer `conv` block after it is finished. Thus you can continue
editing an expression without having to start a new `conv` block and re-scoping
everything. For example:
```lean
example (a b c d : ℕ) (h₁ : b = c) (h₂ : a + c = a + d) : a + b = a + d :=
by conv {
  to_lhs,
  conv {
    congr, skip,
    rw h₁ },
  rw h₂,
}
```
Without `conv`, the above example would need to be proved using two successive
`conv` blocks, each beginning with `to_lhs`.

Also, as a shorthand, `conv_lhs` and `conv_rhs` are provided, so that
```lean
example : 0 + 0 = 0 :=
begin
  conv_lhs { simp }
end
```
just means
```lean
example : 0 + 0 = 0 :=
begin
  conv { to_lhs, simp }
end
```
and likewise for `to_rhs`.
-/
add_tactic_doc
{ name := "conv",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.conv],
  tags := ["core"] }

add_tactic_doc
{ name := "simp",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.simp],
  tags := ["core", "simplification"] }

/--
Accepts terms with the type `component tactic_state string` or `html empty` and
renders them interactively.
Requires a compatible version of the vscode extension to view the resulting widget.

### Example:

```lean
/-- A simple counter that can be incremented or decremented with some buttons. -/
meta def counter_widget {π α : Type} : component π α :=
component.ignore_props $ component.mk_simple int int 0 (λ _ x y, (x + y, none)) (λ _ s,
  h "div" [] [
    button "+" (1 : int),
    html.of_string $ to_string $ s,
    button "-" (-1)
  ]
)

#html counter_widget
```
-/
add_tactic_doc
{ name := "#html",
  category := doc_category.cmd,
  decl_names := [`show_widget_cmd],
  tags := ["core", "widgets"] }

/--
The `add_decl_doc` command is used to add a doc string to an existing declaration.

```lean
def foo := 5

/--
Doc string for foo.
-/
add_decl_doc foo
```
-/
@[user_command] meta def add_decl_doc_command (mi : interactive.decl_meta_info)
  (_ : parse $ tk "add_decl_doc") : parser unit := do
n ← parser.ident,
n ← resolve_constant n,
some doc ← pure mi.doc_string | fail "add_decl_doc requires a doc string",
add_doc_string n doc

add_tactic_doc
{ name := "add_decl_doc",
  category := doc_category.cmd,
  decl_names := [``add_decl_doc_command],
  tags := ["documentation"] }
