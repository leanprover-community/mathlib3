/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.erase_dup
import data.list.min_max

/-!
# The fold operation for a commutative associative operation over a multiset.
-/

namespace multiset
variables {α β : Type*}

/-! ### fold -/
section fold
variables (op : α → α → α) [hc : is_commutative α op] [ha : is_associative α op]
local notation a * b := op a b
include hc ha

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold : α → multiset α → α := foldr op (left_comm _ hc.comm ha.assoc)

theorem fold_eq_foldr (b : α) (s : multiset α) :
  fold op b s = foldr op (left_comm _ hc.comm ha.assoc) b s := rfl

@[simp] theorem coe_fold_r (b : α) (l : list α) : fold op b l = l.foldr op b := rfl

theorem coe_fold_l (b : α) (l : list α) : fold op b l = l.foldl op b :=
(coe_foldr_swap op _ b l).trans $ by simp [hc.comm]

theorem fold_eq_foldl (b : α) (s : multiset α) :
  fold op b s = foldl op (right_comm _ hc.comm ha.assoc) b s :=
quot.induction_on s $ λ l, coe_fold_l _ _ _

@[simp] theorem fold_zero (b : α) : (0 : multiset α).fold op b = b := rfl

@[simp] theorem fold_cons_left : ∀ (b a : α) (s : multiset α),
  (a ::ₘ s).fold op b = a * s.fold op b := foldr_cons _ _

theorem fold_cons_right (b a : α) (s : multiset α) : (a ::ₘ s).fold op b = s.fold op b * a :=
by simp [hc.comm]

theorem fold_cons'_right (b a : α) (s : multiset α) : (a ::ₘ s).fold op b = s.fold op (b * a) :=
by rw [fold_eq_foldl, foldl_cons, ← fold_eq_foldl]

theorem fold_cons'_left (b a : α) (s : multiset α) : (a ::ₘ s).fold op b = s.fold op (a * b) :=
by rw [fold_cons'_right, hc.comm]

theorem fold_add (b₁ b₂ : α) (s₁ s₂ : multiset α) :
  (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
multiset.induction_on s₂
  (by rw [add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
  (by simp {contextual := tt}; cc)

theorem fold_singleton (b a : α) : ({a} : multiset α).fold op b = a * b := foldr_singleton _ _ _ _

theorem fold_distrib {f g : β → α} (u₁ u₂ : α) (s : multiset β) :
  (s.map (λx, f x * g x)).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
multiset.induction_on s (by simp) (by simp {contextual := tt}; cc)

theorem fold_hom {op' : β → β → β} [is_commutative β op'] [is_associative β op']
  {m : α → β} (hm : ∀x y, m (op x y) = op' (m x) (m y)) (b : α) (s : multiset α) :
  (s.map m).fold op' (m b) = m (s.fold op b) :=
multiset.induction_on s (by simp) (by simp [hm] {contextual := tt})

theorem fold_union_inter [decidable_eq α] (s₁ s₂ : multiset α) (b₁ b₂ : α) :
  (s₁ ∪ s₂).fold op b₁ * (s₁ ∩ s₂).fold op b₂ = s₁.fold op b₁ * s₂.fold op b₂ :=
by rw [← fold_add op, union_add_inter, fold_add op]

@[simp] theorem fold_erase_dup_idem [decidable_eq α] [hi : is_idempotent α op] (s : multiset α)
  (b : α) :
  (erase_dup s).fold op b = s.fold op b :=
multiset.induction_on s (by simp) $ λ a s IH, begin
  by_cases a ∈ s; simp [IH, h],
  show fold op b s = op a (fold op b s),
  rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent],
end

end fold

section order

lemma max_le_of_forall_le {α : Type*} [canonically_linear_ordered_add_monoid α]
  (l : multiset α) (n : α) (h : ∀ (x ∈ l), x ≤ n) :
  l.fold max ⊥ ≤ n :=
begin
  induction l using quotient.induction_on,
  simpa using list.max_le_of_forall_le _ _ h
end

lemma max_nat_le_of_forall_le (l : multiset ℕ) (n : ℕ) (h : ∀ (x ∈ l), x ≤ n) :
  l.fold max 0 ≤ n :=
max_le_of_forall_le l n h

end order

open nat

theorem le_smul_erase_dup [decidable_eq α] (s : multiset α) :
  ∃ n : ℕ, s ≤ n • erase_dup s :=
⟨(s.map (λ a, count a s)).fold max 0, le_iff_count.2 $ λ a, begin
  rw count_nsmul, by_cases a ∈ s,
  { refine le_trans _ (nat.mul_le_mul_left _ $ count_pos.2 $ mem_erase_dup.2 h),
    have : count a s ≤ fold max 0 (map (λ a, count a s) (a ::ₘ erase s a));
    [simp [le_max_left], simpa [cons_erase h]] },
  { simp [count_eq_zero.2 h, nat.zero_le] }
end⟩

end multiset
