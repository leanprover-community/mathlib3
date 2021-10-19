/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.core

open lean.parser

namespace tactic

section performance -- see Note [user attribute parameters]

local attribute [semireducible] reflected

local attribute [instance, priority 9000]
private meta def reflect_name_list : has_reflect (list name) | ns :=
`(id %%(expr.mk_app `(Prop) $ ns.map (flip expr.const [])) : list name)

private meta def parse_name_list (e : expr) : list name :=
e.app_arg.get_app_args.map expr.const_name

/-- The `ancestor` attributes is used to record the names of structures which appear in the
extends clause of a `structure` or `class` declared with `old_structure_cmd` set to true.

As an example:
```
set_option old_structure_cmd true

structure base_one := (one : ℕ)

structure base_two (α : Type*) := (two : ℕ)

@[ancestor base_one base_two]
structure bar extends base_one, base_two α
```

The list of ancestors should be in the order they appear in the `extends` clause, and should
contain only the names of the ancestor structures, without any arguments.
-/
@[user_attribute]
meta def ancestor_attr : user_attribute unit (list name) :=
{ name := `ancestor,
  descr := "ancestor of old structures",
  parser := many ident }

add_tactic_doc
{ name := "ancestor",
  category := doc_category.attr,
  decl_names := [`tactic.ancestor_attr],
  tags := ["transport", "environment"] }

end performance

/--
Returns the parents of a structure added via the `ancestor` attribute.

On failure, the empty list is returned.
-/
meta def get_tagged_ancestors (cl : name) : tactic (list name) :=
parse_name_list <$> ancestor_attr.get_param_untyped cl <|> pure []

/--
Returns the parents of a structure added via the `ancestor` attribute, as well as subobjects.

On failure, the empty list is returned.
-/
meta def get_ancestors (cl : name) : tactic (list name) :=
(++) <$> (prod.fst <$> subobject_names cl <|> pure [])
     <*> get_tagged_ancestors cl

/--
Returns the (transitive) ancestors of a structure added via the `ancestor`
attribute (or reachable via subobjects).

On failure, the empty list is returned.
-/
meta def find_ancestors : name → expr → tactic (list expr) | cl arg :=
do cs ← get_ancestors cl,
   r ← cs.mmap $ λ c, list.ret <$> (mk_app c [arg] >>= mk_instance) <|> find_ancestors c arg,
   return r.join

end tactic
