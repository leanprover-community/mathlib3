/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import data.list.basic

run_cmd mk_simp_attr `omega 

attribute [omega]
  false_and
  and_false
  true_or
  or_true
  neg_zero
  zero_add
  add_zero
  zero_sub
  sub_zero
  sub_self
  zero_mul
  mul_zero
  list.map 
  list.length_map 
  list.forall_mem_nil

open lean
open lean.parser
open interactive
open tactic

meta def tactic.interactive.simp_omega 
  (use_iota_eqn : parse $ optional (tk "!")) 
  (hs : parse simp_arg_list) 
  (attr_names : parse types.with_ident_list)
  (locat : parse types.location) 
  (cfg : simp_config_ext := {}) : tactic unit :=
let cfg := if use_iota_eqn.is_none then cfg else {iota_eqn := tt, ..cfg} in
tactic.interactive.propagate_tags 
  (tactic.interactive.simp_core cfg.to_simp_config cfg.discharger tt hs [`omega] locat) 