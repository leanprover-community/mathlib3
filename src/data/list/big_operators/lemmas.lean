/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import data.list.big_operators.basic
import algebra.group.opposite
import algebra.group_power.basic
import algebra.group_with_zero.commute
import algebra.group_with_zero.divisibility
import algebra.order.with_zero
import algebra.ring.basic
import algebra.ring.divisibility
import algebra.ring.commute
import data.int.units
import data.set.basic

/-! # Lemmas about `list.sum` and `list.prod` requiring extra algebra imports 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

open mul_opposite list

variables {ι α M N P M₀ G R : Type*}

namespace commute

lemma list_sum_right [non_unital_non_assoc_semiring R] (a : R) (l : list R)
  (h : ∀ b ∈ l, commute a b) :
  commute a l.sum :=
begin
  induction l with x xs ih,
  { exact commute.zero_right _, },
  { rw list.sum_cons,
    exact (h _ $ mem_cons_self _ _).add_right (ih $ λ j hj, h _ $ mem_cons_of_mem _ hj) }
end

lemma list_sum_left [non_unital_non_assoc_semiring R] (b : R) (l : list R)
  (h : ∀ a ∈ l, commute a b) :
  commute l.sum b :=
(commute.list_sum_right _ _ $ λ x hx, (h _ hx).symm).symm

end commute

namespace list

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod [monoid M] [preorder M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)]
  (l : list M) (n : M) (h : ∀ (x ∈ l), n ≤ x) :
  n ^ l.length ≤ l.prod :=
@prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive] lemma prod_eq_one_iff [canonically_ordered_monoid M] (l : list M) :
  l.prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
⟨all_one_of_le_one_le_of_prod_eq_one (λ _ _, one_le _),
  λ h, by rw [eq_replicate.2 ⟨rfl, h⟩, prod_replicate, one_pow]⟩

/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
lemma neg_one_mem_of_prod_eq_neg_one {l : list ℤ} (h : l.prod = -1) : (-1 : ℤ) ∈ l :=
begin
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h dec_trivial),
  exact or.resolve_left (int.is_unit_iff.mp (prod_is_unit_iff.mp
         (h.symm ▸ is_unit.neg is_unit_one : is_unit l.prod) x h₁)) h₂ ▸ h₁,
end

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
lemma length_le_sum_of_one_le (L : list ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum :=
begin
  induction L with j L IH h, { simp },
  rw [sum_cons, length, add_comm],
  exact add_le_add (h _ (set.mem_insert _ _)) (IH (λ i hi, h i (set.mem_union_right _ hi)))
end

lemma dvd_prod [comm_monoid M] {a} {l : list M} (ha : a ∈ l) : a ∣ l.prod :=
let ⟨s, t, h⟩ := mem_split ha in
by { rw [h, prod_append, prod_cons, mul_left_comm], exact dvd_mul_right _ _ }

lemma dvd_sum [semiring R] {a} {l : list R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum :=
begin
  induction l with x l ih,
  { exact dvd_zero _ },
  { rw [list.sum_cons],
    exact dvd_add (h _ (mem_cons_self _ _)) (ih (λ x hx, h x (mem_cons_of_mem _ hx))) }
end

section alternating
variables [comm_group α]

@[to_additive]
lemma alternating_prod_append : ∀ l₁ l₂ : list α,
  alternating_prod (l₁ ++ l₂) = alternating_prod l₁ * alternating_prod l₂ ^ (-1 : ℤ) ^ length l₁
| [] l₂ := by simp
| (a :: l₁) l₂ := by simp_rw [cons_append, alternating_prod_cons, alternating_prod_append,
  length_cons, pow_succ, neg_mul, one_mul, zpow_neg, ←div_eq_mul_inv, div_div]

@[to_additive]
lemma alternating_prod_reverse :
  ∀ l : list α, alternating_prod (reverse l) = alternating_prod l ^ (-1 : ℤ) ^ (length l + 1)
| [] := by simp only [alternating_prod_nil, one_zpow, reverse_nil]
| (a :: l) :=
begin
  simp_rw [reverse_cons, alternating_prod_append, alternating_prod_reverse,
    alternating_prod_singleton, alternating_prod_cons, length_reverse, length, pow_succ, neg_mul,
    one_mul, zpow_neg, inv_inv],
  rw [mul_comm, ←div_eq_mul_inv, div_zpow],
end

end alternating

lemma sum_map_mul_left [non_unital_non_assoc_semiring R] (L : list ι) (f : ι → R) (r : R) :
  (L.map (λ b, r * f b)).sum = r * (L.map f).sum :=
sum_map_hom L f $ add_monoid_hom.mul_left r

lemma sum_map_mul_right [non_unital_non_assoc_semiring R] (L : list ι) (f : ι → R) (r : R) :
  (L.map (λ b, f b * r)).sum = (L.map f).sum * r :=
sum_map_hom L f $ add_monoid_hom.mul_right r

end list

namespace mul_opposite

open list
variables [monoid M]

lemma op_list_prod : ∀ (l : list M), op (l.prod) = (l.map op).reverse.prod
| [] := rfl
| (x :: xs) := by rw [list.prod_cons, list.map_cons, list.reverse_cons', list.prod_concat, op_mul,
                      op_list_prod]

lemma _root_.mul_opposite.unop_list_prod (l : list Mᵐᵒᵖ) :
  (l.prod).unop = (l.map unop).reverse.prod :=
by rw [← op_inj, op_unop, mul_opposite.op_list_prod, map_reverse, map_map, reverse_reverse,
  op_comp_unop, map_id]

end mul_opposite

section monoid_hom

variables [monoid M] [monoid N]

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
lemma unop_map_list_prod {F : Type*} [monoid_hom_class F M Nᵐᵒᵖ] (f : F) (l : list M) :
  (f l.prod).unop = (l.map (mul_opposite.unop ∘ f)).reverse.prod :=
by rw [map_list_prod f l, mul_opposite.unop_list_prod, list.map_map]

namespace monoid_hom

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements.

Deprecated, use `_root_.unop_map_list_prod` instead. -/
protected lemma unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : list M) :
  (f l.prod).unop = (l.map (mul_opposite.unop ∘ f)).reverse.prod :=
unop_map_list_prod f l

end monoid_hom
end monoid_hom
