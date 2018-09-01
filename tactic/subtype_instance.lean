/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Provides a `subtype_instance` tactic which builds instances for algebraic substructures
(sub-groups, sub-rings...).
-/

import data.string
import tactic.interactive tactic.algebra
import data.subtype data.set.basic
open tactic expr name list

section tactic

open tactic.interactive (get_current_field refine_struct)
open lean lean.parser
open interactive

/-- make names as in `is_add_subgroup` from `add_group` by global prefacing with `is_` 
    and prefacing the last underscore delimeted item with `sub` -/
def mk_substructure_name (x : string) : string :=
"is_" ++ string.map_tokens '_' (list.map_last $ (++) "sub") x

/-- makes the substructure axiom name from field name, by postfacing with `_mem`-/
def mk_mem_name : name -> name
| (mk_string n (mk_string n' p)) := mk_string (n ++ "_mem") (mk_string (mk_substructure_name n') p)
| n := n

meta def derive_field_subtype : tactic unit :=
do
  field ← get_current_field,
  b ← target >>= is_prop,
  if b then  do
    `[simp [subtype.ext], dsimp],
    intros,
    applyc field; assumption
  else do
    `(set %%α) ← find_local ``(set _) >>= infer_type,
    e ← mk_const field,
    expl_arity ← get_expl_arity $ e α,
    xs ← (iota expl_arity).mmap $ λ _, intro1,
    args ← xs.mmap $ λ x, mk_app `subtype.val [x],
    hyps ← xs.mmap $ λ x, mk_app `subtype.property [x],
    val ← mk_app field args,
    mem_field ← resolve_constant $ mk_mem_name field,
    val_mem ← mk_app mem_field hyps,
    `(coe_sort %%s) <- target >>= instantiate_mvars,
    tactic.refine ``(@subtype.mk _ %%s %%val %%val_mem)

/-- builds instances for algebraic substructures

Example:
```lean
variables {α : Type*} [monoid α] {s : set α}

class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance
````
-/
meta def subtype_instance :=
do t ← target,
   let cl := t.get_app_fn.const_name,
   src ← find_ancestors cl t.app_arg,
   let inst := pexpr.mk_structure_instance
       { struct := cl,
         field_values := [],
         field_names := [],
         sources := src.map to_pexpr },
   refine_struct inst ; derive_field_subtype

end tactic
