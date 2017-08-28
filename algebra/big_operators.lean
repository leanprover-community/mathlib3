/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Some big operators for lists and finite sets.
-/
import algebra.group data.list data.list.comb algebra.group_power data.set.finite data.finset
  data.list.perm

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace list
-- move to list.sum, needs to match exactly, otherwise transport fails
definition prod [has_mul α] [has_one α] : list α → α := list.foldl (*) 1

section monoid
variables [monoid α] {l l₁ l₂ : list α} {a : α}

@[simp] theorem prod_nil : ([] : list α).prod = 1 := rfl

@[simp] theorem prod_cons : (a::l).prod = a * l.prod :=
calc (a::l).prod = foldl (*) (a * 1) l : by simp [list.prod]
  ... = _ : foldl_assoc

@[simp] theorem prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
calc (l₁ ++ l₂).prod = foldl (*) (foldl (*) 1 l₁ * 1) l₂ : by simp [list.prod]
  ... = l₁.prod * l₂.prod : foldl_assoc

@[simp] theorem prod_join {l : list (list α)} : l.join.prod = (l.map list.prod).prod :=
by induction l; simp [list.join, *] at *

@[simp] theorem prod_replicate {n : ℕ} : (list.replicate n a).prod = a ^ n :=
begin
  induction n with n ih,
  { show [].prod = (1:α), refl },
  { show (a :: list.replicate n a).prod = a ^ (n+1), simp [pow_succ, ih] }
end

end monoid

section comm_monoid
open list
variable [comm_monoid α]

lemma prod_eq_of_perm {l₁ l₂ : list α} (h : perm l₁ l₂) : l₁.prod = l₂.prod :=
by induction h; repeat { simp [*] }

lemma prod_reverse {l : list α} : l.reverse.prod = l.prod :=
prod_eq_of_perm $ perm.perm_rev_simp l

end comm_monoid

end list

namespace finset
section prod_comm_monoid
open list
variables [comm_monoid β] (s : finset α) (f : α → β)

protected definition prod : β := s.fold (*) 1 f

variables {s f} {s₁ s₂ : finset α}

@[simp] lemma prod_empty : (∅:finset α).prod f = 1 := rfl

variable [decidable_eq α]

@[simp] lemma prod_to_finset_of_nodup {l : list α} (h : nodup l) :
  (to_finset_of_nodup l h).prod f = (l.map f).prod :=
fold_to_finset_of_nodup h

@[simp] lemma prod_insert {a : α} : a ∉ s → (insert a s).prod f = f a * s.prod f := fold_insert

@[simp] lemma prod_singleton {a : α} : ({a}:finset α).prod f = f a :=
eq.trans fold_singleton (by simp)

lemma prod_image [decidable_eq γ] {s : finset γ} {g : γ → α} :
  (∀x∈s, ∀y∈s, g x = g y → x = y) → (s.image g).prod f = s.prod (λx, f (g x)) :=
fold_image

lemma prod_union_inter : (s₁ ∪ s₂).prod f * (s₁ ∩ s₂).prod f = s₁.prod f * s₂.prod f :=
fold_union_inter

lemma prod_union (h : s₁ ∩ s₂ = ∅) : (s₁ ∪ s₂).prod f = s₁.prod f * s₂.prod f :=
by rw [←prod_union_inter, h]; simp

lemma prod_mul_distrib {g : α → β} : s.prod (λx, f x * g x) = s.prod f * s.prod g :=
eq.trans (by simp; refl) fold_op_distrib

end prod_comm_monoid
end finset

/- transport versions to additive -/
-- TODO: change transport_multiplicative_to_additive to use attribute
run_cmd transport_multiplicative_to_additive [
  /- map operations -/
  (`has_mul.mul, `has_add.add), (`has_one.one, `has_zero.zero), (`has_inv.inv, `has_neg.neg),
  (`has_mul, `has_add), (`has_one, `has_zero), (`has_inv, `has_neg),
  /- map constructors -/
  (`has_mul.mk, `has_add.mk), (`has_one, `has_zero.mk), (`has_inv, `has_neg.mk),
  /- map structures -/
  (`semigroup, `add_semigroup),
  (`monoid, `add_monoid),
  (`group, `add_group),
  (`comm_semigroup, `add_comm_semigroup),
  (`comm_monoid, `add_comm_monoid),
  (`comm_group, `add_comm_group),
  (`left_cancel_semigroup, `add_left_cancel_semigroup),
  (`right_cancel_semigroup, `add_right_cancel_semigroup),
  (`left_cancel_semigroup.mk, `add_left_cancel_semigroup.mk),
  (`right_cancel_semigroup.mk, `add_right_cancel_semigroup.mk),
  /- map instances -/
  (`semigroup.to_has_mul, `add_semigroup.to_has_add),
  (`semigroup_to_is_associative, `add_semigroup_to_is_associative),
  (`comm_semigroup_to_is_commutative, `add_comm_semigroup_to_is_commutative),
  (`monoid.to_has_one, `add_monoid.to_has_zero),
  (`group.to_has_inv, `add_group.to_has_neg),
  (`comm_semigroup.to_semigroup, `add_comm_semigroup.to_add_semigroup),
  (`monoid.to_semigroup, `add_monoid.to_add_semigroup),
  (`comm_monoid.to_monoid, `add_comm_monoid.to_add_monoid),
  (`comm_monoid.to_comm_semigroup, `add_comm_monoid.to_add_comm_semigroup),
  (`group.to_monoid, `add_group.to_add_monoid),
  (`comm_group.to_group, `add_comm_group.to_add_group),
  (`comm_group.to_comm_monoid, `add_comm_group.to_add_comm_monoid),
  (`left_cancel_semigroup.to_semigroup, `add_left_cancel_semigroup.to_add_semigroup),
  (`right_cancel_semigroup.to_semigroup, `add_right_cancel_semigroup.to_add_semigroup),
  /- map projections -/
  (`semigroup.mul_assoc, `add_semigroup.add_assoc),
  (`comm_semigroup.mul_comm, `add_comm_semigroup.add_comm),
  (`left_cancel_semigroup.mul_left_cancel, `add_left_cancel_semigroup.add_left_cancel),
  (`right_cancel_semigroup.mul_right_cancel, `add_right_cancel_semigroup.add_right_cancel),
  (`monoid.one_mul, `add_monoid.zero_add),
  (`monoid.mul_one, `add_monoid.add_zero),
  (`group.mul_left_inv, `add_group.add_left_neg),
  (`group.mul, `add_group.add),
  (`group.mul_assoc, `add_group.add_assoc),
  /- map lemmas -/
  (`mul_assoc, `add_assoc),
  (`mul_comm, `add_comm),
  (`mul_left_comm, `add_left_comm),
  (`mul_right_comm, `add_right_comm),
  (`one_mul, `zero_add),
  (`mul_one, `add_zero),
  (`mul_left_inv, `add_left_neg),
  (`mul_left_cancel, `add_left_cancel),
  (`mul_right_cancel, `add_right_cancel),
  (`mul_left_cancel_iff, `add_left_cancel_iff),
  (`mul_right_cancel_iff, `add_right_cancel_iff),
  (`inv_mul_cancel_left, `neg_add_cancel_left),
  (`inv_mul_cancel_right, `neg_add_cancel_right),
  (`eq_inv_mul_of_mul_eq, `eq_neg_add_of_add_eq),
  (`inv_eq_of_mul_eq_one, `neg_eq_of_add_eq_zero),
  (`inv_inv, `neg_neg),
  (`mul_right_inv, `add_right_neg),
  (`mul_inv_cancel_left, `add_neg_cancel_left),
  (`mul_inv_cancel_right, `add_neg_cancel_right),
  (`mul_inv_rev, `neg_add_rev),
  (`mul_inv, `neg_add),
  (`inv_inj, `neg_inj),
  (`group.mul_left_cancel, `add_group.add_left_cancel),
  (`group.mul_right_cancel, `add_group.add_right_cancel),
  (`group.to_left_cancel_semigroup, `add_group.to_left_cancel_add_semigroup),
  (`group.to_right_cancel_semigroup, `add_group.to_right_cancel_add_semigroup),
  (`eq_inv_of_eq_inv, `eq_neg_of_eq_neg),
  (`eq_inv_of_mul_eq_one, `eq_neg_of_add_eq_zero),
  (`eq_mul_inv_of_mul_eq, `eq_add_neg_of_add_eq),
  (`inv_mul_eq_of_eq_mul, `neg_add_eq_of_eq_add),
  (`mul_inv_eq_of_eq_mul, `add_neg_eq_of_eq_add),
  (`eq_mul_of_mul_inv_eq, `eq_add_of_add_neg_eq),
  (`eq_mul_of_inv_mul_eq, `eq_add_of_neg_add_eq),
  (`mul_eq_of_eq_inv_mul, `add_eq_of_eq_neg_add),
  (`mul_eq_of_eq_mul_inv, `add_eq_of_eq_add_neg),
  (`one_inv, `neg_zero),
  (`left_inverse_inv, `left_inverse_neg),
  (`inv_eq_inv_iff_eq, `neg_eq_neg_iff_eq),
  (`inv_eq_one_iff_eq_one, `neg_eq_zero_iff_eq_zero),
  (`eq_one_of_inv_eq_one, `eq_zero_of_neg_eq_zero),
  (`eq_inv_iff_eq_inv, `eq_neg_iff_eq_neg),
  (`eq_of_mul_inv_eq_one, `eq_of_add_neg_eq_zero),
  (`mul_eq_iff_eq_inv_mul, `add_eq_iff_eq_neg_add),
  (`mul_eq_iff_eq_mul_inv, `add_eq_iff_eq_add_neg),
  -- (`mul_eq_one_of_mul_eq_one, `add_eq_zero_of_add_eq_zero)   not needed for commutative groups
  -- (`muleq_one_iff_mul_eq_one, `add_eq_zero_iff_add_eq_zero)

  --NEW:
  (`list.prod, `list.sum),
  (`list.prod.equations._eqn_1, `list.sum.equations._eqn_1),
  (`list.prod_nil, `list.sum_nil),
  (`list.prod_cons, `list.sum_cons),
  (`list.prod_append, `list.sum_append),
  (`list.prod_join, `list.sum_join),
  (`list.prod_eq_of_perm, `list.sum_eq_of_perm),
  (`list.prod_reverse, `list.sum_reverse),
  (`finset.prod._proof_1, `finset.sum._proof_1),
  (`finset.prod._proof_2, `finset.sum._proof_2),
  (`finset.prod, `finset.sum),
  (`finset.prod.equations._eqn_1, `finset.sum.equations._eqn_1),
  (`finset.prod_empty, `finset.sum_empty),
  (`finset.prod_insert, `finset.sum_insert),
  (`finset.prod_singleton, `finset.sum_singleton),
  (`finset.prod_union_inter, `finset.sum_union_inter),
  (`finset.prod_union, `finset.sum_union),
  (`finset.prod_to_finset_of_nodup, `finset.sum_to_finset_of_nodup),
  (`finset.prod_image, `finset.sum_image),
  (`finset.prod_mul_distrib, `finset.sum_add_distrib)
  ]
