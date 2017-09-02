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

@[simp] lemma exists_false {α : Sort u} : ¬ (∃a:α, false) := assume ⟨a, h⟩, h

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
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

protected definition prod [comm_monoid β] (s : finset α) (f : α → β) : β := s.fold (*) 1 f

variables [decidable_eq α]

section comm_monoid
variables [comm_monoid β]

@[simp] lemma prod_empty {α : Type u} {f : α → β} : (∅:finset α).prod f = 1 := rfl

@[simp] lemma prod_to_finset_of_nodup {l : list α} (h : list.nodup l) :
  (to_finset_of_nodup l h).prod f = (l.map f).prod :=
fold_to_finset_of_nodup h

@[simp] lemma prod_insert : a ∉ s → (insert a s).prod f = f a * s.prod f := fold_insert

@[simp] lemma prod_singleton : ({a}:finset α).prod f = f a :=
eq.trans fold_singleton (by simp)

@[simp] lemma prod_image [decidable_eq γ] {s : finset γ} {g : γ → α} :
  (∀x∈s, ∀y∈s, g x = g y → x = y) → (s.image g).prod f = s.prod (λx, f (g x)) :=
fold_image

@[congr] lemma prod_congr : (∀x∈s, f x = g x) → s.prod f = s.prod g :=
fold_congr

lemma prod_union_inter : (s₁ ∪ s₂).prod f * (s₁ ∩ s₂).prod f = s₁.prod f * s₂.prod f :=
fold_union_inter

lemma prod_union (h : s₁ ∩ s₂ = ∅) : (s₁ ∪ s₂).prod f = s₁.prod f * s₂.prod f :=
by rw [←prod_union_inter, h]; simp

lemma prod_mul_distrib : s.prod (λx, f x * g x) = s.prod f * s.prod g :=
eq.trans (by simp; refl) fold_op_distrib

lemma prod_hom [comm_monoid γ] (g : β → γ)
  (h₁ : g 1 = 1) (h₂ : ∀x y, g (x * y) = g x * g y) : s.prod (λx, g (f x)) = g (s.prod f) :=
eq.trans (by rw [h₁]; refl) (fold_hom h₂)

@[simp] lemma prod_const_one : s.prod (λx, (1 : β)) = 1 :=
s.induction_on (by simp) (by simp {contextual:=tt})

end comm_monoid

section comm_group
variables [comm_group β]

@[simp] lemma prod_inv_distrib : s.prod (λx, (f x)⁻¹) = (s.prod f)⁻¹ :=
prod_hom has_inv.inv one_inv mul_inv

end comm_group

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
  (`finset.prod_congr, `finset.sum_congr),
  (`finset.prod_hom, `finset.sum_hom),
  (`finset.prod_const_one, `finset.sum_const_zero),
  (`finset.prod_mul_distrib, `finset.sum_add_distrib),
  (`finset.prod_inv_distrib, `finset.sum_neg_distrib)
  ]

namespace finset
variables [decidable_eq α] {s s₁ s₂ : finset α} {f g : α → β} {b : β} {a : α}

@[simp] lemma sum_sub_distrib [add_comm_group β] : s.sum (λx, f x - g x) = s.sum f - s.sum g :=
by simp [sum_add_distrib]

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid β]

lemma sum_le_sum : (∀x∈s, f x ≤ g x) → s.sum f ≤ s.sum g :=
s.induction_on (by simp; refl) $ assume a s ha ih h,
  have f a + s.sum f ≤ g a + s.sum g,
    from add_le_add (h _ mem_insert) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simp [*]

lemma zero_le_sum (h : ∀x∈s, 0 ≤ f x) : 0 ≤ s.sum f := le_trans (by simp) (sum_le_sum h)
lemma sum_le_zero (h : ∀x∈s, f x ≤ 0) : s.sum f ≤ 0 := le_trans (sum_le_sum h) (by simp)

end ordered_cancel_comm_monoid

section semiring
variables [semiring β]

lemma sum_mul : s.sum f * b = s.sum (λx, f x * b) :=
(sum_hom (λx, x * b) (zero_mul b) (assume a c, add_mul a c b)).symm

lemma mul_sum : b * s.sum f = s.sum (λx, b * f x) :=
(sum_hom (λx, b * x) (mul_zero b) (assume a c, mul_add b a c)).symm

end semiring

section comm_semiring
variables [comm_semiring β]

lemma prod_eq_zero (ha : a ∈ s) (h : f a = 0) : s.prod f = 0 :=
calc s.prod f = (insert a (erase a s)).prod f : by simp [ha, insert_erase]
  ... = 0 : by simp [h]
end comm_semiring

section integral_domain /- add integral_semi_domain to support nat and ennreal -/
variables [integral_domain β]

lemma prod_eq_zero_iff : s.prod f = 0 ↔ (∃a∈s, f a = 0) :=
s.induction_on (by simp)
begin
  intros a s,
  rw [bexists_def, bexists_def, exists_mem_insert_iff],
  simp [mul_eq_zero_iff_eq_zero_or_eq_zero] {contextual := tt}
end

end integral_domain

end finset
