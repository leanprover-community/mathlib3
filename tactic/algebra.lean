/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import tactic.basic

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

attribute [ancestor has_mul] semigroup
attribute [ancestor semigroup has_one] monoid
attribute [ancestor monoid has_inv] group
attribute [ancestor group has_comm] comm_group
attribute [ancestor has_add] add_semigroup
attribute [ancestor add_semigroup has_zero] add_monoid
attribute [ancestor add_monoid has_neg] add_group
attribute [ancestor add_group has_add_comm] add_comm_group

attribute [ancestor ring has_inv zero_ne_one_class] division_ring
attribute [ancestor division_ring comm_ring] field
attribute [ancestor field] discrete_field

attribute [ancestor has_mul has_add] distrib
attribute [ancestor has_mul has_zero] mul_zero_class
attribute [ancestor has_zero has_one] zero_ne_one_class
attribute [ancestor add_comm_monoid monoid distrib mul_zero_class] semiring
attribute [ancestor semiring comm_monoid] comm_semiring
attribute [ancestor add_comm_group monoid distrib] ring

attribute [ancestor ring comm_semigroup] comm_ring
attribute [ancestor has_mul has_zero] no_zero_divisors
attribute [ancestor comm_ring no_zero_divisors zero_ne_one_class] integral_domain
