/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import data.list.big_operators.basic

/-!
# Counting in lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties of `list.countp` and `list.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in [`data.list.defs`](./defs).
-/

open nat

variables {α β : Type*} {l l₁ l₂ : list α}

namespace list

section countp
variables (p q : α → Prop) [decidable_pred p] [decidable_pred q]

@[simp] lemma countp_nil : countp p [] = 0 := rfl

@[simp] lemma countp_cons_of_pos {a : α} (l) (pa : p a) : countp p (a::l) = countp p l + 1 :=
if_pos pa

@[simp] lemma countp_cons_of_neg {a : α} (l) (pa : ¬ p a) : countp p (a::l) = countp p l :=
if_neg pa

lemma countp_cons (a : α) (l) : countp p (a :: l) = countp p l + ite (p a) 1 0 :=
by { by_cases h : p a; simp [h] }

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
by simpa only [countp_eq_length_filter] using length_filter_le _ _

@[simp] lemma countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ :=
by simp only [countp_eq_length_filter, filter_append, length_append]

lemma countp_join : ∀ l : list (list α), countp p l.join = (l.map (countp p)).sum
| [] := rfl
| (a :: l) := by rw [join, countp_append, map_cons, sum_cons, countp_join]

lemma countp_pos {l} : 0 < countp p l ↔ ∃ a ∈ l, p a :=
by simp only [countp_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]

@[simp] theorem countp_eq_zero {l} : countp p l = 0 ↔ ∀ a ∈ l, ¬ p a :=
by { rw [← not_iff_not, ← ne.def, ← pos_iff_ne_zero, countp_pos], simp }

@[simp] lemma countp_eq_length {l} : countp p l = l.length ↔ ∀ a ∈ l, p a :=
by rw [countp_eq_length_filter, filter_length_eq_length]

lemma length_filter_lt_length_iff_exists (l) : length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x :=
by rw [length_eq_countp_add_countp p l, ← countp_pos, countp_eq_length_filter, lt_add_iff_pos_right]

lemma sublist.countp_le (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ :=
by simpa only [countp_eq_length_filter] using length_le_of_sublist (s.filter p)

@[simp] lemma countp_filter (l : list α) : countp p (filter q l) = countp (λ a, p a ∧ q a) l :=
by simp only [countp_eq_length_filter, filter_filter]

@[simp] lemma countp_true : l.countp (λ _, true) = l.length := by simp

@[simp] lemma countp_false : l.countp (λ _, false) = 0 := by simp

@[simp] lemma countp_map (p : β → Prop) [decidable_pred p] (f : α → β) :
  ∀ l, countp p (map f l) = countp (p ∘ f) l
| [] := rfl
| (a::l) := by rw [map_cons, countp_cons, countp_cons, countp_map]

variables {p q}

lemma countp_mono_left (h : ∀ x ∈ l, p x → q x) : countp p l ≤ countp q l :=
begin
  induction l with a l ihl, { refl },
  rw [forall_mem_cons] at h, cases h with ha hl,
  rw [countp_cons, countp_cons],
  refine add_le_add (ihl hl) _,
  split_ifs; try { simp only [le_rfl, zero_le] },
  exact absurd (ha ‹_›) ‹_›
end

lemma countp_congr (h : ∀ x ∈ l, p x ↔ q x) : countp p l = countp q l :=
le_antisymm (countp_mono_left $ λ x hx, (h x hx).1) (countp_mono_left $ λ x hx, (h x hx).2)

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

@[simp] lemma count_cons_self (a : α) (l : list α) : count a (a::l) = count a l + 1 := if_pos rfl

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

lemma count_join (l : list (list α)) (a : α) : l.join.count a = (l.map (count a)).sum :=
countp_join _ _

lemma count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
by simp [-add_comm]

@[simp] lemma count_pos {a : α} {l : list α} : 0 < count a l ↔ a ∈ l :=
by simp only [count, countp_pos, exists_prop, exists_eq_right']

@[simp] lemma one_le_count_iff_mem {a : α} {l : list α} : 1 ≤ count a l ↔ a ∈ l :=
count_pos

@[simp, priority 980]
lemma count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
decidable.by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

lemma not_mem_of_count_eq_zero {a : α} {l : list α} (h : count a l = 0) : a ∉ l :=
λ h', (count_pos.2 h').ne' h

@[simp] lemma count_eq_zero {a : α} {l} : count a l = 0 ↔ a ∉ l :=
⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

@[simp] lemma count_eq_length {a : α} {l} : count a l = l.length ↔ ∀ b ∈ l, a = b :=
countp_eq_length _

@[simp] lemma count_replicate_self (a : α) (n : ℕ) : count a (replicate n a) = n :=
by rw [count, countp_eq_length_filter, filter_eq_self.2, length_replicate];
   exact λ b m, (eq_of_mem_replicate m).symm

lemma count_replicate (a b : α) (n : ℕ) : count a (replicate n b) = if a = b then n else 0 :=
begin
  split_ifs with h,
  exacts [h ▸ count_replicate_self _ _, count_eq_zero_of_not_mem $ mt eq_of_mem_replicate h]
end

theorem filter_eq (l : list α) (a : α) : l.filter (eq a) = replicate (count a l) a :=
by simp [eq_replicate, count, countp_eq_length_filter, @eq_comm _ _ a]

theorem filter_eq' (l : list α) (a : α) : l.filter (λ x, x = a) = replicate (count a l) a :=
by simp only [filter_eq, @eq_comm _ _ a]

lemma le_count_iff_replicate_sublist {a : α} {l : list α} {n : ℕ} :
  n ≤ count a l ↔ replicate n a <+ l :=
⟨λ h, ((replicate_sublist_replicate a).2 h).trans $ filter_eq l a ▸ filter_sublist _,
 λ h, by simpa only [count_replicate_self] using h.count_le a⟩

lemma replicate_count_eq_of_count_eq_length  {a : α} {l : list α} (h : count a l = length l)  :
  replicate (count a l) a = l :=
(le_count_iff_replicate_sublist.mp le_rfl).eq_of_length $ (length_replicate (count a l) a).trans h

@[simp] lemma count_filter {p} [decidable_pred p]
  {a} {l : list α} (h : p a) : count a (filter p l) = count a l :=
by simp only [count, countp_filter, show (λ b, a = b ∧ p b) = eq a, by { ext b, constructor; cc }]

lemma count_bind {α β} [decidable_eq β] (l : list α) (f : α → list β) (x : β)  :
  count x (l.bind f) = sum (map (count x ∘ f) l) :=
by rw [list.bind, count_join, map_map]

@[simp] lemma count_map_of_injective {α β} [decidable_eq α] [decidable_eq β]
  (l : list α) (f : α → β) (hf : function.injective f) (x : α) :
  count (f x) (map f l) = count x l :=
by simp only [count, countp_map, (∘), hf.eq_iff]

lemma count_le_count_map [decidable_eq β] (l : list α) (f : α → β) (x : α) :
  count x l ≤ count (f x) (map f l) :=
begin
  rw [count, count, countp_map],
  exact countp_mono_left (λ y hyl, congr_arg f),
end

lemma count_erase (a b : α) : ∀ l : list α, count a (l.erase b) = count a l - ite (a = b) 1 0
| [] := by simp
| (c :: l) :=
begin
  rw [erase_cons],
  by_cases hc : c = b,
  { rw [if_pos hc, hc, count_cons', nat.add_sub_cancel] },
  { rw [if_neg hc, count_cons', count_cons', count_erase],
    by_cases ha : a = b,
    { rw [← ha, eq_comm] at hc,
      rw [if_pos ha, if_neg hc, add_zero, add_zero] },
    { rw [if_neg ha, tsub_zero, tsub_zero] } }
end

@[simp] lemma count_erase_self (a : α) (l : list α) : count a (list.erase l a) = count a l - 1 :=
by rw [count_erase, if_pos rfl]

@[simp] lemma count_erase_of_ne {a b : α} (ab : a ≠ b) (l : list α) :
  count a (l.erase b) = count a l :=
by rw [count_erase, if_neg ab, tsub_zero]

@[to_additive]
lemma prod_map_eq_pow_single [monoid β] {l : list α} (a : α) (f : α → β)
  (hf : ∀ a' ≠ a, a' ∈ l → f a' = 1) : (l.map f).prod = (f a) ^ (l.count a) :=
begin
  induction l with a' as h generalizing a,
  { rw [map_nil, prod_nil, count_nil, pow_zero] },
  { specialize h a (λ a' ha' hfa', hf a' ha' (mem_cons_of_mem _ hfa')),
    rw [list.map_cons, list.prod_cons, count_cons, h],
    split_ifs with ha',
    { rw [ha', pow_succ] },
    { rw [hf a' (ne.symm ha') (list.mem_cons_self a' as), one_mul] } }
end

@[to_additive]
lemma prod_eq_pow_single [monoid α] {l : list α} (a : α)
  (h : ∀ a' ≠ a, a' ∈ l → a' = 1) : l.prod = a ^ (l.count a) :=
trans (by rw [map_id'']) (prod_map_eq_pow_single a id h)

end count

end list
