/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import data.finset.pointwise
import group_theory.group_action.sub_mul_action
import group_theory.group_action.fixing_subgroup

import ..equivariant_map

open_locale pointwise

variables (G : Type*) [group G] {X : Type*} [mul_action G X]


open mul_action

/-- Action on the complement of an invariant subset -/
def sub_mul_action_of_compl (Y : sub_mul_action G X) : sub_mul_action G X := {
carrier := Yᶜ,
smul_mem' := λ g x,
  by simp only [set_like.mem_coe, set.mem_compl_iff, sub_mul_action.smul_mem_iff', imp_self] }

lemma sub_mul_action_of_compl_def (Y : sub_mul_action G X) :
  (sub_mul_action_of_compl G Y).carrier = Yᶜ := rfl

/-- Action of stabilizer of a point on the complement -/
def sub_mul_action_of_stabilizer (a : X) : sub_mul_action (stabilizer G a) X := {
carrier := { a }ᶜ,
smul_mem' := λ g x,
begin
  simp only [set.mem_compl_iff, set.mem_singleton_iff],
  rw not_imp_not,
  rw smul_eq_iff_eq_inv_smul,
  intro hgx, rw hgx,
  apply symm, rw ← smul_eq_iff_eq_inv_smul,
  conv_rhs { rw ← mem_stabilizer_iff.mp (set_like.coe_mem g) },
  refl,
end }

/-- The inclusion of the sub_mul_action of the stabilizer, as an equivariant map -/
def sub_mul_action_of_stabilizer.inclusion (a : X) :
  (sub_mul_action_of_stabilizer G a) →[stabilizer G a]  X := {
to_fun := λ x, id x,
map_smul' := λ g x, rfl}

lemma sub_mul_action_of_stabilizer_def (a : X) :
  (sub_mul_action_of_stabilizer G a).carrier = { a }ᶜ := rfl

lemma mem_sub_mul_action_of_stabilizer_iff (a : X) (x : X) :
  x ∈ sub_mul_action_of_stabilizer G a ↔ x ≠ a := iff.rfl

lemma sub_mul_action_of_stabilizer_neq (a : X) (x : ↥(sub_mul_action_of_stabilizer G a)) :
  ↑x ≠ a := x.prop

instance sub_mul_action_of_stabilizer_lift (a : X) :
  has_lift_t (sub_mul_action_of_stabilizer G a) X := coe_to_lift
