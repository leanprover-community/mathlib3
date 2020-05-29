/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import tactic.suggest tactic.find
/-!
## `protected` and `protect_proj` user attributes

`protected` is an attribute to protect a declaration
If a declaration `foo.bar` is marked protected, then it must be referred to
by its full name `foo.bar`, even when the `foo` namespace is open."

`protect_proj` attribute to protect the projections of a structure.
If a structure `foo` is marked with the `protect_proj` user attribute, then
all of the projections become protected.

`protect_proj without bar baz` will protect all projections except for bar and baz.
-/

namespace tactic
/-- Attribute to protect a declaration
    If a declaration `foo.bar` is marked protected, then it must be referred to
    by its full name `foo.bar`, even when the `foo` namespace is open.. -/
@[user_attribute] meta def protected_attr : user_attribute :=
{ name := "protected",
  descr := "Attribute to protect a declaration
    If a declaration `foo.bar` is marked protected, then it must be referred to
    by its full name `foo.bar`, even when the `foo` namespace is open.",
  after_set := some (λ n _ _, mk_protected n)  }

add_tactic_doc
{ name        := "protected",
  category    := doc_category.attr,
  decl_names  := [`tactic.protected_attr],
  tags        := ["user attribute"] }

/-- Tactic that is executed when a structure is marked with the `protect_proj` attribute -/
meta def protect_proj_tac (n : name) (l : list name) : tactic unit :=
do env ← get_env,
option.cases_on (env.structure_fields_full n)
  (fail "protect_proj failed: declaration is not a structure")
  (λ fields, fields.foldl
    (λ t field, cond (l.foldl (λ b m, bor b (m.is_suffix_of field)) ff)
      skip
      (t >> tactic.mk_protected field))
    skip)

/-- Attribute to protect the projections of a structure.
    If a structure `foo` is marked with the `protect_proj` user attribute, then
    all of the projections become protected, meaning they must always be referred to by
    their full name `foo.bar`, even when the `foo` namespace is open.

    `protect_proj without bar baz` will protect all projections except for bar and baz -/
@[user_attribute] meta def protect_proj_attr : user_attribute unit (list name) :=
{ name := "protect_proj",
  descr := "Attribute to protect the projections of a structure.
    If a structure `foo` is marked with the `protect_proj` user attribute, then
    all of the projections become protected, meaning they must always be referred to by
    their full name `foo.bar`, even when the `foo` namespace is open.

    `protect_proj without bar baz` will protect all projections except for bar and baz",
  after_set := some (λ n _ _, do l ← protect_proj_attr.get_param n,
    protect_proj_tac n l),
  parser := interactive.types.without_ident_list }

add_tactic_doc
{ name        := "protect_proj",
  category    := doc_category.attr,
  decl_names  := [`tactic.protect_proj_attr],
  tags        := ["user attribute", "structures"] }

end tactic
