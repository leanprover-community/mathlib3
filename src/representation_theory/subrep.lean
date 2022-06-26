/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.direct_sum

set_option old_structure_cmd true

structure subrep
  {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
  (ρ : representation k G V) extends submodule k V :=
(smulG_mem' : ∀ (g : G) {x : V}, x ∈ carrier → ρ g x ∈ carrier)

structure rep_hom
  {k G V V' : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V'] [module k V']
  (ρ : representation k G V) (ρ' : representation k G V') extends V →ₗ[k] V' :=
(smul_comm : ∀ (g : G) (x : V), ρ' g (to_fun x) = to_fun (ρ g x))
