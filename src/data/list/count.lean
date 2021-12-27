/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import data.list.big_operators

/-!
# Counting in lists

This file proves basic properties of `list.countp` and `list.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in [`data.list.defs`](./data/list/defs).
-/

open nat

variables {α β : Type*} {l l₁ l₂ : list α}

namespace list

section countp
variables (p : α → Prop) [decidable_pred p]

@[simp] lemma countp_nil : countp p [] = 0 := rfl

@[simp] lemma countp_cons_of_pos {a : α} (l) (pa : p a) : countp p (a::l) = countp p l + 1 :=
if_pos pa

@[simp] lemma countp_cons_of_neg {a : α} (l) (pa : ¬ p a) : countp p (a::l) = countp p l :=
if_neg pa

lemma length_eq_countp_add_countp (l) : length l = countp p l + countp (λ a, ¬p a) l :=
by induction l with x h ih; [refl, by_cases p x];
  [simp only [countp_cons_of_pos _ _ h, countp_cons_of_neg (λ a, ¬p a) _ (decidable.not_not.2 h),
    ih, length],
   simp only [countp_cons_of_pos (λ a, ¬p a) _ h, countp_cons_of_neg _ _ h, ih, length]]; ac_refl

lemma countp_eq_length_filter (l) : countp p l = length (filter p l) :=
by induction l with x l ih; [refl, by_cases (p x)];
  [simp only [filter_cons_of_pos _ h, countp, ih, if_pos h],
   simp only [countp_cons_of_neg _ _ h, ih, filter_cons_of_neg _ h]]; refl

lemma countp_le_length : countp p l ≤ l.length :=
by simpa only [countp_eq_length_filter] using length_le_of_sublist (filter_sublist _)

@[simp] lemma countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ :=
by simp only [countp_eq_length_filter, filter_append, length_append]

lemma countp_pos {l} : 0 < countp p l ↔ ∃ a ∈ l, p a :=
by simp only [countp_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]

lemma length_filter_lt_length_iff_exists (l) : length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x :=
by rw [length_eq_countp_add_countp p l, ← countp_pos, countp_eq_length_filter, lt_add_iff_pos_right]

lemma sublist.countp_le (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ :=
by simpa only [countp_eq_length_filter] using length_le_of_sublist (s.filter p)

@[simp] lemma countp_filter {q} [decidable_pred q] (l : list α) :
  countp p (filter q l) = countp (λ a, p a ∧ q a) l :=
by simp only [countp_eq_length_filter, filter_filter]

@[simp] lemma countp_true : l.countp (λ _, true) = l.length :=
by simp [countp_eq_length_filter]

@[simp] lemma countp_false : l.countp (λ _, false) = 0 :=
by simp [countp_eq_length_filter]

end countp

/-! ### count -/

section count
variables [decidable_eq α]

@[simp] lemma count_nil (a : α) : count a [] = 0 := rfl

lemma count_cons (a b : α) (l : list α) :
  count a (b :: l) = if a = b then succ (count a l) else count a l := rfl

lemma count_cons' (a b : α) (l : list α) :
  count a (b :: l) = count a l + (if a = b then 1 else 0) :=
begin rw count_cons, split_ifs; refl end

@[simp] lemma count_cons_self (a : α) (l : list α) : count a (a::l) = succ (count a l) := if_pos rfl

@[simp, priority 990]
lemma count_cons_of_ne {a b : α} (h : a ≠ b) (l : list α) : count a (b::l) = count a l := if_neg h

lemma count_tail : Π (l : list α) (a : α) (h : 0 < l.length),
  l.tail.count a = l.count a - ite (a = list.nth_le l 0 h) 1 0
| (_ :: _) a h := by { rw [count_cons], split_ifs; simp }

lemma count_le_length (a : α) (l : list α) : count a l ≤ l.length :=
countp_le_length _

lemma sublist.count_le (h : l₁ <+ l₂) (a : α) : count a l₁ ≤ count a l₂ := h.countp_le _

lemma count_le_count_cons (a b : α) (l : list α) : count a l ≤ count a (b :: l) :=
(sublist_cons _ _).count_le _

lemma count_singleton (a : α) : count a [a] = 1 := if_pos rfl

lemma count_singleton' (a b : α) : count a [b] = ite (a = b) 1 0 := rfl

@[simp] lemma count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
countp_append _

lemma count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
by simp [-add_comm]

lemma count_pos {a : α} {l : list α} : 0 < count a l ↔ a ∈ l :=
by simp only [count, countp_pos, exists_prop, exists_eq_right']

@[simp, priority 980]
lemma count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
decidable.by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

lemma not_mem_of_count_eq_zero {a : α} {l : list α} (h : count a l = 0) : a ∉ l :=
λ h', (count_pos.2 h').ne' h

@[simp] lemma count_repeat (a : α) (n : ℕ) : count a (repeat a n) = n :=
by rw [count, countp_eq_length_filter, filter_eq_self.2, length_repeat];
   exact λ b m, (eq_of_mem_repeat m).symm

lemma le_count_iff_repeat_sublist {a : α} {l : list α} {n : ℕ} :
  n ≤ count a l ↔ repeat a n <+ l :=
⟨λ h, ((repeat_sublist_repeat a).2 h).trans $
  have filter (eq a) l = repeat a (count a l), from eq_repeat.2
    ⟨by simp only [count, countp_eq_length_filter], λ b m, (of_mem_filter m).symm⟩,
  by rw ← this; apply filter_sublist,
 λ h, by simpa only [count_repeat] using h.count_le a⟩

lemma repeat_count_eq_of_count_eq_length  {a : α} {l : list α} (h : count a l = length l)  :
  repeat a (count a l) = l :=
eq_of_sublist_of_length_eq (le_count_iff_repeat_sublist.mp (le_refl (count a l)))
    (eq.trans (length_repeat a (count a l)) h)

@[simp] lemma count_filter {p} [decidable_pred p]
  {a} {l : list α} (h : p a) : count a (filter p l) = count a l :=
by simp only [count, countp_filter]; congr; exact
set.ext (λ b, and_iff_left_of_imp (λ e, e ▸ h))

lemma count_bind {α β} [decidable_eq β] (l : list α) (f : α → list β) (x : β)  :
  count x (l.bind f) = sum (map (count x ∘ f) l) :=
begin
  induction l with hd tl IH,
  { simp },
  { simpa }
end

@[simp] lemma count_map_map {α β} [decidable_eq α] [decidable_eq β] (l : list α) (f : α → β)
  (hf : function.injective f) (x : α) :
  count (f x) (map f l) = count x l :=
begin
  induction l with y l IH generalizing x,
  { simp },
  { rw map_cons,
    by_cases h : x = y,
    { simpa [h] using IH _ },
    { simpa [h, hf.ne h] using IH _ } }
end

@[simp] lemma count_erase_self (a : α) :
  ∀ (s : list α), count a (list.erase s a) = pred (count a s)
| [] := by simp
| (h :: t) :=
begin
  rw erase_cons,
  by_cases p : h = a,
  { rw [if_pos p, count_cons', if_pos p.symm], simp },
  { rw [if_neg p, count_cons', count_cons', if_neg (λ x : a = h, p x.symm), count_erase_self],
    simp }
end

@[simp] lemma count_erase_of_ne {a b : α} (ab : a ≠ b) :
  ∀ (s : list α), count a (list.erase s b) = count a s
| [] := by simp
| (x :: xs) :=
begin
  rw erase_cons,
  split_ifs with h,
  { rw [count_cons', h, if_neg ab], simp },
  { rw [count_cons', count_cons', count_erase_of_ne] }
end

end count

end list
