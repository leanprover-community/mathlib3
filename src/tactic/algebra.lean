/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.core

open lean.parser

namespace tactic

@[user_attribute]
meta def ancestor_attr : user_attribute unit (list name) :=
{ name := `ancestor,
  descr := "ancestor of old structures",
  parser := many ident }

meta def get_ancestors (cl : name) : tactic (list name) :=
(++) <$> (prod.fst <$> subobject_names cl <|> pure [])
     <*> (user_attribute.get_param ancestor_attr cl <|> pure [])

meta def find_ancestors : name → expr → tactic (list expr) | cl arg :=
do cs ← get_ancestors cl,
   r ← cs.mmap $ λ c, list.ret <$> (mk_app c [arg] >>= mk_instance) <|> find_ancestors c arg,
   return r.join

end tactic
