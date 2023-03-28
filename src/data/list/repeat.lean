/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.list.rotate
import data.list.big_operators.lemmas

/-!
# List Repeat

This file proves basic results about `list.repeat`, the list of an element repeated multiple times.
-/

namespace list

variables {α β : Type*} (x : α) (n : ℕ)

/-- Only `x` is a member of `list.repeat x n` (unless `n = 0` which has no members). -/
@[simp] lemma mem_repeat_iff (y : α) : y ∈ (list.repeat x n) ↔ 0 < n ∧ y = x :=
begin
  induction n with n hn,
  { rw [lt_self_iff_false, false_and, list.repeat, list.mem_nil_iff] },
  { simp [hn] }
end

lemma not_mem_repeat_zero (y : α) : y ∉ (repeat x 0) :=
by simp_rw [mem_repeat_iff, lt_self_iff_false, false_and, not_false_iff]

lemma mem_repeat_succ_iff (y : α) : y ∈ (repeat x n.succ) ↔ y = x :=
by simp_rw [mem_repeat_iff, nat.zero_lt_succ, true_and]

lemma eq_of_mem_repeat {x y : α} {n : ℕ} (hy : y ∈ (repeat x n)) : y = x :=
((mem_repeat_iff x n y).1 hy).2

lemma pos_of_mem_repeat {x y : α} {n : ℕ} (hy : y ∈ (repeat x n)) : 0 < n :=
((mem_repeat_iff x n y).1 hy).1

@[simp] lemma nth_le_repeat (m : ℕ) (hm : m < (repeat x n).length) :
  (repeat x n).nth_le m hm = x :=
eq_of_mem_repeat (mem_iff_nth_le.2 ⟨m, hm, rfl⟩)

@[simp] lemma nth_repeat (m : ℕ) : (repeat x n).nth m = if m < n then some x else none :=
begin
  split_ifs with h,
  { exact nth_eq_some.2 ⟨(length_repeat x n).symm ▸ h, nth_le_repeat x n m _⟩ },
  { exact nth_eq_none_iff.2 (le_of_not_lt $ (length_repeat x n).symm ▸ h) }
end

lemma nth_repeat_eq_none_iff (m : ℕ) : (repeat x n).nth m = none ↔ n ≤ m :=
by rw [nth_eq_none_iff, length_repeat]

lemma nth_repeat_eq_some_iff (m : ℕ) (y : α) :
  (repeat x n).nth m = some y ↔ m < n ∧ x = y :=
by simp only [ite_eq_iff, nth_repeat, and_false, or_false]

lemma find_repeat (p : α → Prop) [decidable_pred p] :
  (repeat x n).find p = if 0 < n ∧ p x then some x else none :=
begin
  split_ifs with hx,
  { cases n with n,
    { exact ((lt_self_iff_false 0).1 hx.1).elim },
    { exact find_cons_of_pos _ hx.2 } },
  { refine find_eq_none.2 (λ y hy, (eq_of_mem_repeat hy).symm ▸ _),
    simpa only [not_and_distrib, pos_of_mem_repeat hy, not_true, false_or] using hx }
end

@[simp] lemma find_repeat_eq_none_iff  (p : α → Prop) [decidable_pred p] :
  (repeat x n).find p = none ↔ n = 0 ∨ ¬ p x :=
by simp_rw [find_repeat, ite_eq_right_iff, imp_false, not_and_distrib, not_lt, le_zero_iff]

@[simp] lemma find_repeat_eq_some_iff (p : α → Prop) [decidable_pred p] (y : α) :
  (repeat x n).find p = some y ↔ 0 < n ∧ p x ∧ y = x :=
by simp_rw [find_repeat, ite_eq_iff, and_assoc, eq_comm, and_false, or_false]

@[simp] lemma all₂_repeat_iff (p : α → Prop) : (repeat x n).all₂ p ↔ n = 0 ∨ p x :=
by simp [all₂_iff_forall, lt_iff_not_le, or_iff_not_imp_left]

@[simp] lemma all_repeat (p : α → bool) :
  (repeat x n).all p = if n = 0 then tt else p x :=
begin
  induction n with n hn,
  { refl },
  { simp only [nat.succ_ne_zero, if_false, repeat, all, foldr_cons],
    by_cases hn' : n = 0,
    { rw [hn', repeat, foldr, band_tt] },
    { exact trans (congr_arg (λ y, p x && y) (hn.trans (if_neg hn'))) (band_self (p x)) } }
end

@[simp] lemma reverse_repeat : (repeat x n).reverse = repeat x n :=
begin
  refine ext_le (length_reverse _) (λ m hm hm', _),
  rw [nth_le_repeat, nth_le_reverse' _ m, nth_le_repeat],
  exact lt_of_le_of_lt tsub_le_self (tsub_lt_self (lt_of_le_of_lt zero_le' hm') zero_lt_one),
end

@[simp] lemma rotate_repeat (m : ℕ) : (repeat x n).rotate m = repeat x n :=
begin
  refine ext_le (length_rotate _ _) (λ m hm hm', _),
  rw [nth_le_repeat, nth_le_rotate, nth_le_repeat],
end

@[simp] lemma concat_self_repeat : (repeat x n).concat x = repeat x (n + 1) :=
by rw [concat_eq_reverse_cons, reverse_repeat, ← repeat, reverse_repeat]

@[simp] lemma map_repeat (f : α → β) : (repeat x n).map f = repeat (f x) n :=
begin
  induction n with n hn,
  { exact rfl },
  { exact (map_cons f x _).trans (congr_arg ((::) (f x)) hn) }
end

@[simp] lemma filter_repeat (p : α → Prop) [decidable_pred p] :
  (repeat x n).filter p = if p x then repeat x n else [] :=
begin
  induction n with n hn,
  { exact (if_t_t _ []).symm },
  { split_ifs with hp; simp [hp, hn] }
end

lemma repeat_add (m : ℕ) :
  repeat x (n + m) = repeat x n ++ repeat x m :=
begin
  induction n with n hn,
  { rw [repeat, zero_add, nil_append] },
  { rw [nat.succ_add, repeat, hn, ← cons_append, repeat] }
end

lemma repeat_sub (m : ℕ) :
  repeat x (n - m) = (repeat x n).drop m :=
begin
  refine ext_le _ (λ m hm hm', _),
  { simp_rw [length_drop, length_repeat] },
  { simp_rw [nth_le_drop', nth_le_repeat] }
end

end list
