/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro.

Transport multiplicative to additive
-/

import tactic.basic data.option.defs

meta def name.map_prefix (f : name → option name) :  name → option name :=
λ n, f n <|> match n with
| name.anonymous := none
| name.mk_string s n' := name.mk_string s <$> n'.map_prefix
| name.mk_numeral d n' := name.mk_numeral d <$> n'.map_prefix
end

section transport
open tactic

meta def apply_replacement_fun (f : name → option name) (e : expr) : expr :=
e.replace $ λ e d,
match e with
| expr.const n ls := do
  new_n ← f n,
  return $ expr.const new_n ls
| _ := none
end

meta def copy_decl_using_fun (f : name → option name) (src : name) (tgt : name) : command :=
do decl     ← get_decl src,
   let decl := decl.update_name $ tgt,
   let decl := decl.update_type $ apply_replacement_fun f decl.type,
   let decl := decl.map_value $ apply_replacement_fun f,
   add_decl decl

meta def transport_with_fun (f : name → option name) (src : name) (tgt : name) : command :=
copy_decl_using_fun f src tgt
>> copy_attribute `reducible src tt tgt
>> copy_attribute `simp src tt tgt
>> copy_attribute `instance src tt tgt

meta def transport_with_prefix_dict (dict : name_map name) : name → name → command :=
transport_with_fun (name.map_prefix dict.find)

@[user_attribute]
meta def to_additive_attr : user_attribute (name_map name) name :=
{ name      := `to_additive,
  descr     := "Transport multiplicative to additive",
  cache_cfg :=
    ⟨λ ns, ns.mfoldl (λ dict n, dict.insert n <$> to_additive_attr.get_param n) mk_name_map, []⟩,
  parser    := lean.parser.ident,
  after_set := some $ λ src prio persistent, do
    env ← get_env,
    match (env.structure_fields src) with
    | some fields := do
      tgt ← to_additive_attr.get_param src,
      tgt_fields ← env.structure_fields tgt,
      guard (fields.length = tgt_fields.length) <|>
        fail ("Structures " ++ src.to_string ++ " and " ++ tgt.to_string ++
              " have different number of fields"),
      (fields.zip tgt_fields).mmap
        (λ names, to_additive_attr.set
          (src.append names.fst) (tgt.append names.snd) persistent prio),
      skip
    | none := do
      tgt ← to_additive_attr.get_param src,
      if env.contains tgt
      then skip
      else do
        decl ← env.get src,
        dict ← to_additive_attr.get_cache,
        decl.value.fold skip
          (λ e _ t,
            match e with
            | expr.const n _ :=
              match n.map_prefix (λ n', if n' = src then some tgt else none) with
              | some n' := t >> transport_with_prefix_dict dict n n'
              | none := t
              end
            | _ := t
            end),
        transport_with_prefix_dict dict src tgt
    end }
end transport

/- map operations -/
attribute [to_additive has_add] has_mul
attribute [to_additive has_zero] has_one
attribute [to_additive has_neg] has_inv

/- map structures -/
attribute [to_additive add_semigroup] semigroup
attribute [to_additive add_semigroup.to_has_add] semigroup.to_has_mul

attribute [to_additive add_comm_semigroup] comm_semigroup
attribute [to_additive add_comm_semigroup.to_add_semigroup] comm_semigroup.to_semigroup

attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup
attribute [to_additive add_left_cancel_semigroup.to_add_semigroup] left_cancel_semigroup.to_semigroup

attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup
attribute [to_additive add_right_cancel_semigroup.to_add_semigroup] right_cancel_semigroup.to_semigroup

attribute [to_additive add_monoid] monoid
attribute [to_additive add_monoid.to_has_zero] monoid.to_has_one
attribute [to_additive add_monoid.to_add_semigroup] monoid.to_semigroup

attribute [to_additive add_comm_monoid] comm_monoid
attribute [to_additive add_comm_monoid.mk] comm_monoid.mk
attribute [to_additive add_comm_monoid.to_add_monoid] comm_monoid.to_monoid
attribute [to_additive add_comm_monoid.to_add_comm_semigroup] comm_monoid.to_comm_semigroup

attribute [to_additive add_group] group
attribute [to_additive add_group.to_has_neg] group.to_has_inv
attribute [to_additive add_group.to_add_monoid] group.to_monoid

attribute [to_additive add_comm_group] comm_group
attribute [to_additive add_comm_group.to_add_group] comm_group.to_group
attribute [to_additive add_comm_group.to_add_comm_monoid] comm_group.to_comm_monoid

/- map theorems -/
attribute [to_additive add_assoc] mul_assoc
attribute [to_additive add_semigroup_to_is_eq_associative] semigroup_to_is_associative
attribute [to_additive add_comm] mul_comm
attribute [to_additive add_comm_semigroup_to_is_eq_commutative] comm_semigroup_to_is_commutative
attribute [to_additive add_left_comm] mul_left_comm
attribute [to_additive add_right_comm] mul_right_comm
attribute [to_additive add_left_cancel] mul_left_cancel
attribute [to_additive add_right_cancel] mul_right_cancel
attribute [to_additive add_left_cancel_iff] mul_left_cancel_iff
attribute [to_additive add_right_cancel_iff] mul_right_cancel_iff
attribute [to_additive zero_add] one_mul
attribute [to_additive add_zero] mul_one
attribute [to_additive add_left_neg] mul_left_inv
attribute [to_additive neg_add_self] inv_mul_self
attribute [to_additive neg_add_cancel_left] inv_mul_cancel_left
attribute [to_additive neg_add_cancel_right] inv_mul_cancel_right
attribute [to_additive neg_eq_of_add_eq_zero] inv_eq_of_mul_eq_one
attribute [to_additive neg_zero] one_inv
attribute [to_additive neg_neg] inv_inv
attribute [to_additive add_right_neg] mul_right_inv
attribute [to_additive add_neg_self] mul_inv_self
attribute [to_additive neg_inj] inv_inj
attribute [to_additive add_group.add_left_cancel] group.mul_left_cancel
attribute [to_additive add_group.add_right_cancel] group.mul_right_cancel
attribute [to_additive add_group.to_left_cancel_add_semigroup] group.to_left_cancel_semigroup
attribute [to_additive add_group.to_right_cancel_add_semigroup] group.to_right_cancel_semigroup
attribute [to_additive add_neg_cancel_left] mul_inv_cancel_left
attribute [to_additive add_neg_cancel_right] mul_inv_cancel_right
attribute [to_additive neg_add_rev] mul_inv_rev
attribute [to_additive eq_neg_of_eq_neg] eq_inv_of_eq_inv
attribute [to_additive eq_neg_of_add_eq_zero] eq_inv_of_mul_eq_one
attribute [to_additive eq_add_neg_of_add_eq] eq_mul_inv_of_mul_eq
attribute [to_additive eq_neg_add_of_add_eq] eq_inv_mul_of_mul_eq
attribute [to_additive neg_add_eq_of_eq_add] inv_mul_eq_of_eq_mul
attribute [to_additive add_neg_eq_of_eq_add] mul_inv_eq_of_eq_mul
attribute [to_additive eq_add_of_add_neg_eq] eq_mul_of_mul_inv_eq
attribute [to_additive eq_add_of_neg_add_eq] eq_mul_of_inv_mul_eq
attribute [to_additive add_eq_of_eq_neg_add] mul_eq_of_eq_inv_mul
attribute [to_additive add_eq_of_eq_add_neg] mul_eq_of_eq_mul_inv
attribute [to_additive neg_add] mul_inv

