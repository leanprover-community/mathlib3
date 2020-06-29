/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Provides a `subtype_instance` tactic which builds instances for algebraic substructures
(sub-groups, sub-rings...).
-/
import data.string.basic
open tactic expr name list

namespace tactic

open tactic.interactive (get_current_field refine_struct)
open lean lean.parser
open interactive

/-- makes the substructure axiom name from field name, by postfacing with `_mem`-/
def mk_mem_name (sub : name) : name → name
| (mk_string n _) := mk_string (n ++ "_mem") sub
| n := n

meta def derive_field_subtype : tactic unit :=
do
  field ← get_current_field,
  b ← target >>= is_prop,
  if b then  do
    `[simp [subtype.ext_iff_val], dsimp [set.set_coe_eq_subtype]],
    intros,
    applyc field; assumption
  else do
    s ← find_local ``(set _),
    `(set %%α) ← infer_type s,
    e ← mk_const field,
    expl_arity ← get_expl_arity $ e α,
    xs ← (iota expl_arity).mmap $ λ _, intro1,
    args ← xs.mmap $ λ x, mk_app `subtype.val [x],
    hyps ← xs.mmap $ λ x, mk_app `subtype.property [x],
    val ← mk_app field args,
    subname ← local_context >>= list.mfirst (λ h, do
      (expr.const n _, args) ← get_app_fn_args <$> infer_type h,
      is_def_eq s args.ilast reducible,
      return n),
    mem_field ← resolve_constant $ mk_mem_name subname field,
    val_mem ← mk_app mem_field hyps,
    `(coe_sort %%s) <- target >>= instantiate_mvars,
    tactic.refine ``(@subtype.mk _ %%s %%val %%val_mem)

namespace interactive

/-- builds instances for algebraic substructures

Example:
```lean
variables {α : Type*} [monoid α] {s : set α}

class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance
```
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

add_tactic_doc
{ name := "subtype_instance",
  category := doc_category.tactic,
  decl_names := [``subtype_instance],
  tags := ["type class", "structures"] }

end interactive

end tactic
