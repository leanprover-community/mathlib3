/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.succ_pred.basic
import data.set.lattice

/-!
# Intervals `Ixx (f x) (f (order.succ x))`

In this file we prove

* `monotone.bUnion_Ico_Ioc_map_succ`: if `α` is a linear archimedean succ order and `β` is a linear
  order, then for any monotone function `f` and `m n : α`, the union of intervals
  `set.Ioc (f i) (f (order.succ i))`, `m ≤ i < n`, is equal to `set.Ioc (f m) (f n)`;

* `monotone.pairwise_disjoint_on_Ioc_succ`: if `α` is a linear succ order, `β` is a preorder, and
  `f : α → β` is a monotone function, then the intervals `set.Ioc (f n) (f (order.succ n))` are
  pairwise disjoint.

Later this file should be extended with lemmas about other intervals and antitone functions.
-/

open set

variables {α β : Type*} [linear_order α]

namespace monotone

/-- If `α` is a linear archimedean succ order and `β` is a linear order, then for any monotone
function `f` and `m n : α`, the union of intervals `set.Ioc (f i) (f (order.succ i))`, `m ≤ i < n`,
is equal to `set.Ioc (f m) (f n)` -/
lemma bUnion_Ico_Ioc_map_succ [succ_order α] [is_succ_archimedean α]
  [linear_order β] {f : α → β} (hf : monotone f) (m n : α) :
  (⋃ i ∈ Ico m n, Ioc (f i) (f (order.succ i))) = Ioc (f m) (f n) :=
begin
  cases le_total n m with hnm hmn,
  { rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), bUnion_empty] },
  { refine succ.rec _ _ hmn,
    { simp only [Ioc_self, Ico_self, bUnion_empty] },
    { intros k hmk ihk,
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf $ order.le_succ _), union_comm, ← ihk],
      by_cases hk : is_max k,
      { rw [hk.succ_eq, Ioc_self, empty_union] },
      { rw [order.Ico_succ_right_eq_insert_of_not_is_max hmk hk, bUnion_insert] } } }
end

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ioc (f n) (f (order.succ n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioc_succ [succ_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ioc (f n) (f (order.succ n)))) :=
(pairwise_disjoint_on _).2 $ λ m n hmn x ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩, h₂.not_le $
  h₁.trans $ hf $ order.succ_le_of_lt hmn

end monotone
