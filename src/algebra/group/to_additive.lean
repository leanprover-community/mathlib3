/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov.
-/

import tactic.basic tactic.transport tactic.algebra

/-!
# Transport multiplicative to additive

This file defines an attribute `to_additive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from multiplicative theory to additive theory.

To use this attribute, just write

```
@[to_additive]
theorem mul_comm' {α} [comm_semigroup α] (x y : α) : x * y = y * x := comm_semigroup.mul_comm
```

This code will generate a theorem named `add_comm'`.  It is also
possible to manually specify the name of the new declaration, and
provide a documentation string.

The transport tries to do the right thing in most cases using several
heuristics described below.  However, in some cases it fails, and
requires manual intervention.

## Implementation notes
### Handling of hidden definitions

Before transporting the “main” declaration `src`, `to_additive` first
scans its type and value for names starting with `src`, and transports
them. This includes auxiliary definitions like `src._match_1`,
`src._proof_1`.

After transporting the “main” declaration, `to_additive` transports
its equational lemmas.

### Structure fields and constructors

If `src` is a structure, then `to_additive` automatically adds
structure fields to its mapping, and similarly for constructors of
inductive types.

For new structures this means that `to_additive` automatically handles
coercions, and for old structures it does the same, if ancestry
information is present in `@[ancestor]` attributes.

### Name generation

* If `@[to_additive]` is called without a `name` argument, then the
  new name is autogenerated.  First, it takes the longest prefix of
  the source name that is already known to `to_additive`, and replaces
  this prefix with its additive counterpart. Second, it takes the last
  part of the name (i.e., after the last dot), and replaces common
  name parts (“mul”, “one”, “inv”, “prod”) with their additive versions.

* If `@[to_additive]` is called with a `name` argument `new_name`
  /without a dot/, then `to_additive` updates the prefix as described
  above, then replaces the last part of the name with `new_name`.

* If `@[to_additive]` is called with a `name` argument
  `new_namespace.new_name` /with a dot/, then `to_additive` uses this
  new name as is.

As a safety check, in the first two cases `to_additive` double checks
that the new name differs from the original one.

### Missing features

* Automatically transport structures and other inductive types.

* Handle `protected` attribute. Currently all new definitions are public.

* For structures, automatically generate theorems like `group α ↔
  add_group (additive α)`.

* Mapping of prefixes that do not correspond to any definition, see
  `quotient_group`.

* Rewrite rules for the last part of the name that work in more
  cases. E.g., we can replace `monoid` with `add_monoid` etc.
-/

namespace to_additive
open tactic exceptional

@[user_attribute]
meta def aux_attr : user_attribute (name_map name) name :=
{ name      := `to_additive_aux,
  descr     := "Auxiliary attribute for `to_additive`. DON'T USE IT",
  cache_cfg := ⟨λ ns,
                ns.mfoldl
                  (λ dict n',
                   let n := match n' with
                            | name.mk_string s pre := if s = "_to_additive" then pre else n'
                            | _ := n'
                            end
                   in dict.insert n <$> aux_attr.get_param n')
                  mk_name_map, []⟩,
  parser    := lean.parser.ident }

meta def map_namespace (src tgt : name) : command :=
do decl ← get_decl `bool, -- random choice
   let n := src.mk_string "_to_additive",
   let decl := decl.update_name n,
   add_decl decl,
   aux_attr.set n tgt tt

@[derive has_reflect]
structure value_type := (tgt : name) (doc : option string)

meta def tokens_dict : native.rb_map string string :=
native.rb_map.of_list $
[("mul", "add"), ("one", "zero"), ("inv", "neg"), ("prod", "sum")]

meta def guess_name : string → string :=
string.map_tokens '_' $ list.map $
string.map_tokens ''' $ list.map $
λ s, (tokens_dict.find s).get_or_else s

meta def target_name (src tgt : name) (dict : name_map name) : tactic name :=
(if tgt.get_prefix ≠ name.anonymous -- `tgt` is a full name
 then pure tgt
 else match src with
      | (name.mk_string s pre) :=
        do let tgt_auto := guess_name s,
           guard (tgt.to_string ≠ tgt_auto)
             <|> trace ("`to_additive " ++ src.to_string ++ "`: remove `name` argument"),
           pure $ name.mk_string
                 (if tgt = name.anonymous then tgt_auto else tgt.to_string)
                 (pre.map_prefix dict.find)
      | _ := fail ("to_additive: can't transport " ++ src.to_string)
      end) >>=
(λ res,
  if res = src
  then fail ("to_additive: can't transport " ++ src.to_string ++ " to itself")
  else pure res)

meta def parser : lean.parser value_type :=
do
  tgt ← optional lean.parser.ident,
  e ← optional interactive.types.texpr,
  doc ← match e with
      | some pe := some <$> ((to_expr pe >>= eval_expr string) : tactic string)
      | none := pure none
      end,
  return ⟨tgt.get_or_else name.anonymous, doc⟩

private meta def proceed_fields_aux (src tgt : name) (prio : ℕ) (f : name → tactic (list string)) :
  command :=
do
  src_fields ← f src,
  tgt_fields ← f tgt,
  guard (src_fields.length = tgt_fields.length) <|>
    fail ("Failed to map fields of " ++ src.to_string),
  (src_fields.zip tgt_fields).mmap' $
    λ names, guard (names.fst = names.snd) <|>
      aux_attr.set (src.append names.fst) (tgt.append names.snd) tt prio

meta def proceed_fields (env : environment) (src tgt : name) (prio : ℕ) : command :=
let aux := proceed_fields_aux src tgt prio in
do 
aux (λ n, pure $ list.map name.to_string $ (env.structure_fields n).get_or_else []) >>
aux (λ n, (list.map (λ (x : name), "to_" ++ x.to_string) <$>
                            (ancestor_attr.get_param n <|> pure []))) >>
aux (λ n, (env.constructors_of n).mmap $
          λ cs, match cs with
                | (name.mk_string s pre) :=
                  (guard (pre = n) <|> fail "Bad constructor name") >>
                  pure s
                | _ := fail "Bad constructor name"
                end)

@[user_attribute]
protected meta def attr : user_attribute unit value_type :=
{ name      := `to_additive,
  descr     := "Transport multiplicative to additive",
  parser    := parser,
  after_set := some $ λ src prio persistent, do
    guard persistent <|> fail "`to_additive` can't be used as a local attribute",
    env ← get_env,
    val ← attr.get_param src,
    dict ← aux_attr.get_cache,
    tgt ← target_name src val.tgt dict,
    aux_attr.set src tgt tt,
    let dict := dict.insert src tgt,
    if env.contains tgt
    then proceed_fields env src tgt prio
    else do
      transport_with_prefix_dict dict src tgt
        [`reducible, `simp, `instance, `refl, `symm, `trans, `elab_as_eliminator],
      match val.doc with
      | some doc := add_doc_string tgt doc
      | none := skip
      end }
end to_additive

/- map operations -/
attribute [to_additive] has_mul has_one has_inv

/- map structures -/
attribute [to_additive add_semigroup] semigroup
attribute [to_additive add_comm_semigroup] comm_semigroup
attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup
attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup

attribute [to_additive add_monoid] monoid
attribute [to_additive add_comm_monoid] comm_monoid
attribute [to_additive add_group] group
attribute [to_additive add_comm_group] comm_group

/- map theorems -/
attribute [to_additive] mul_assoc
attribute [to_additive add_semigroup_to_is_eq_associative] semigroup_to_is_associative
attribute [to_additive] mul_comm
attribute [to_additive add_comm_semigroup_to_is_eq_commutative] comm_semigroup_to_is_commutative
attribute [to_additive] mul_left_comm
attribute [to_additive] mul_right_comm
attribute [to_additive] mul_left_cancel
attribute [to_additive] mul_right_cancel
attribute [to_additive] mul_left_cancel_iff
attribute [to_additive] mul_right_cancel_iff
attribute [to_additive] one_mul
attribute [to_additive] mul_one
attribute [to_additive] mul_left_inv
attribute [to_additive] inv_mul_self
attribute [to_additive] inv_mul_cancel_left
attribute [to_additive] inv_mul_cancel_right
attribute [to_additive] inv_eq_of_mul_eq_one
attribute [to_additive neg_zero] one_inv
attribute [to_additive] inv_inv
attribute [to_additive] mul_right_inv
attribute [to_additive] mul_inv_self
attribute [to_additive] inv_inj
attribute [to_additive] group.mul_left_cancel
attribute [to_additive] group.mul_right_cancel
attribute [to_additive to_left_cancel_add_semigroup] group.to_left_cancel_semigroup
attribute [to_additive to_right_cancel_add_semigroup] group.to_right_cancel_semigroup
attribute [to_additive] mul_inv_cancel_left
attribute [to_additive] mul_inv_cancel_right
attribute [to_additive neg_add_rev] mul_inv_rev
attribute [to_additive] eq_inv_of_eq_inv
attribute [to_additive] eq_inv_of_mul_eq_one
attribute [to_additive] eq_mul_inv_of_mul_eq
attribute [to_additive] eq_inv_mul_of_mul_eq
attribute [to_additive] inv_mul_eq_of_eq_mul
attribute [to_additive] mul_inv_eq_of_eq_mul
attribute [to_additive] eq_mul_of_mul_inv_eq
attribute [to_additive] eq_mul_of_inv_mul_eq
attribute [to_additive] mul_eq_of_eq_inv_mul
attribute [to_additive] mul_eq_of_eq_mul_inv
attribute [to_additive neg_add] mul_inv

