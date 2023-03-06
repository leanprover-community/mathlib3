/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.pairwise
import order.succ_pred.basic

/-!
# Intervals `Ixx (f x) (f (order.succ x))`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove

* `monotone.bUnion_Ico_Ioc_map_succ`: if `α` is a linear archimedean succ order and `β` is a linear
  order, then for any monotone function `f` and `m n : α`, the union of intervals
  `set.Ioc (f i) (f (order.succ i))`, `m ≤ i < n`, is equal to `set.Ioc (f m) (f n)`;

* `monotone.pairwise_disjoint_on_Ioc_succ`: if `α` is a linear succ order, `β` is a preorder, and
  `f : α → β` is a monotone function, then the intervals `set.Ioc (f n) (f (order.succ n))` are
  pairwise disjoint.

For the latter lemma, we also prove various order dual versions.
-/

open set order

variables {α β : Type*} [linear_order α]

namespace monotone

/-- If `α` is a linear archimedean succ order and `β` is a linear order, then for any monotone
function `f` and `m n : α`, the union of intervals `set.Ioc (f i) (f (order.succ i))`, `m ≤ i < n`,
is equal to `set.Ioc (f m) (f n)` -/
lemma bUnion_Ico_Ioc_map_succ [succ_order α] [is_succ_archimedean α]
  [linear_order β] {f : α → β} (hf : monotone f) (m n : α) :
  (⋃ i ∈ Ico m n, Ioc (f i) (f (succ i))) = Ioc (f m) (f n) :=
begin
  cases le_total n m with hnm hmn,
  { rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), bUnion_empty] },
  { refine succ.rec _ _ hmn,
    { simp only [Ioc_self, Ico_self, bUnion_empty] },
    { intros k hmk ihk,
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf $ le_succ _), union_comm, ← ihk],
      by_cases hk : is_max k,
      { rw [hk.succ_eq, Ioc_self, empty_union] },
      { rw [Ico_succ_right_eq_insert_of_not_is_max hmk hk, bUnion_insert] } } }
end

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ioc (f n) (f (order.succ n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioc_succ [succ_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ioc (f n) (f (succ n)))) :=
(pairwise_disjoint_on _).2 $ λ m n hmn,
  disjoint_iff_inf_le.mpr $ λ x ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩, h₂.not_le $ h₁.trans $ hf $ succ_le_of_lt hmn

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ico (f n) (f (order.succ n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ico_succ [succ_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ico (f n) (f (succ n)))) :=
(pairwise_disjoint_on _).2 $ λ m n hmn,
  disjoint_iff_inf_le.mpr $ λ x ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩, h₁.not_le $ (hf $ succ_le_of_lt hmn).trans h₂

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ioo (f n) (f (order.succ n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioo_succ [succ_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ioo (f n) (f (succ n)))) :=
hf.pairwise_disjoint_on_Ico_succ.mono $ λ i j h, h.mono Ioo_subset_Ico_self Ioo_subset_Ico_self

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ioc (f order.pred n) (f n)` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioc_pred [pred_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ioc (f (pred n)) (f n))) :=
by simpa only [(∘), dual_Ico] using hf.dual.pairwise_disjoint_on_Ico_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ico (f order.pred n) (f n)` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ico_pred [pred_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ico (f (pred n)) (f n))) :=
by simpa only [(∘), dual_Ioc] using hf.dual.pairwise_disjoint_on_Ioc_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `set.Ioo (f order.pred n) (f n)` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioo_pred [pred_order α] [preorder β] {f : α → β} (hf : monotone f) :
  pairwise (disjoint on (λ n, Ioo (f (pred n)) (f n))) :=
by simpa only [(∘), dual_Ioo] using hf.dual.pairwise_disjoint_on_Ioo_succ

end monotone

namespace antitone

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `set.Ioc (f (order.succ n)) (f n)` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioc_succ [succ_order α] [preorder β] {f : α → β} (hf : antitone f) :
  pairwise (disjoint on (λ n, Ioc (f (succ n)) (f n))) :=
hf.dual_left.pairwise_disjoint_on_Ioc_pred

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `set.Ico (f (order.succ n)) (f n)` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ico_succ [succ_order α] [preorder β] {f : α → β} (hf : antitone f) :
  pairwise (disjoint on (λ n, Ico (f (succ n)) (f n))) :=
hf.dual_left.pairwise_disjoint_on_Ico_pred

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `set.Ioo (f (order.succ n)) (f n)` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioo_succ [succ_order α] [preorder β] {f : α → β} (hf : antitone f) :
  pairwise (disjoint on (λ n, Ioo (f (succ n)) (f n))) :=
hf.dual_left.pairwise_disjoint_on_Ioo_pred

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `set.Ioc (f n) (f (order.pred n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioc_pred [pred_order α] [preorder β] {f : α → β} (hf : antitone f) :
  pairwise (disjoint on (λ n, Ioc (f n) (f (pred n)))) :=
hf.dual_left.pairwise_disjoint_on_Ioc_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `set.Ico (f n) (f (order.pred n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ico_pred [pred_order α] [preorder β] {f : α → β} (hf : antitone f) :
  pairwise (disjoint on (λ n, Ico (f n) (f (pred n)))) :=
hf.dual_left.pairwise_disjoint_on_Ico_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `set.Ioo (f n) (f (order.pred n))` are pairwise disjoint. -/
lemma pairwise_disjoint_on_Ioo_pred [pred_order α] [preorder β] {f : α → β} (hf : antitone f) :
  pairwise (disjoint on (λ n, Ioo (f n) (f (pred n)))) :=
hf.dual_left.pairwise_disjoint_on_Ioo_succ

end antitone
