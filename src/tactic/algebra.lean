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

@[user_attribute]
private meta def ancestor_attr : user_attribute unit (list name) :=
{ name := `ancestor,
  descr := "ancestor of old structures",
  parser := many ident }

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
