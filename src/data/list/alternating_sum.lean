/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Chris Wong
-/
import algebra.group_power
import data.list.basic

variables {α : Type*}

namespace list

attribute [to_additive] alternating_prod

section
variables [has_one α] [has_mul α] [has_inv α]

@[simp, to_additive] lemma alternating_prod_nil : alternating_prod ([] : list α) = 1 := rfl
@[simp, to_additive] lemma alternating_prod_singleton (a : α) : alternating_prod [a] = a := rfl

@[to_additive] lemma alternating_prod_cons_cons' (a b : α) (l : list α) :
  alternating_prod (a :: b :: l) = a * b⁻¹ * alternating_prod l := rfl

end

@[to_additive] lemma alternating_prod_cons_cons [group α] (a b : α) (l : list α) :
  alternating_prod (a :: b :: l) = a / b * alternating_prod l :=
by rw [div_eq_mul_inv, alternating_prod_cons_cons']

variables [comm_group α]

@[to_additive] lemma alternating_prod_cons' :
  ∀ (a : α) (l : list α), alternating_prod (a :: l) = a * (alternating_prod l)⁻¹
| a [] := by rw [alternating_prod_nil, one_inv, mul_one, alternating_prod_singleton]
| a (b :: l) :=
by rw [alternating_prod_cons_cons', alternating_prod_cons' b l, mul_inv, inv_inv, mul_assoc]

@[simp, to_additive] lemma alternating_prod_cons (a : α) (l : list α) :
  alternating_prod (a :: l) = a / alternating_prod l :=
by rw [div_eq_mul_inv, alternating_prod_cons']

@[to_additive]
lemma alternating_prod_append :
  ∀ (l₁ l₂ : list α), alternating_prod (l₁ ++ l₂)
    = alternating_prod l₁ * alternating_prod l₂ ^ (-1 : ℤ) ^ length l₁
| [] l₂ := by simp
| (a :: l₁) l₂ := by simp_rw [cons_append, alternating_prod_cons, alternating_prod_append,
  length_cons, pow_succ, neg_mul, one_mul, zpow_neg, ←div_eq_mul_inv, div_div]

@[to_additive]
lemma alternating_prod_reverse :
  ∀ (l : list α), alternating_prod (reverse l) = alternating_prod l ^ (-1 : ℤ) ^ (length l + 1)
| [] := by simp only [alternating_prod_nil, one_zpow, reverse_nil]
| (a :: l) :=
begin
  simp_rw [reverse_cons, alternating_prod_append, alternating_prod_reverse,
    alternating_prod_singleton, alternating_prod_cons, length_reverse, length, pow_succ, neg_mul,
    one_mul, zpow_neg, inv_inv],
  rw [mul_comm, ←div_eq_mul_inv, div_zpow],
end

end list
