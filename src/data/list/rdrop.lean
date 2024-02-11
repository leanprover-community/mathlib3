/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.basic
import data.list.infix

/-!

# Dropping or taking from lists on the right

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Taking or removing element from the tail end of a list

## Main defintions

- `rdrop n`: drop `n : ℕ` elements from the tail
- `rtake n`: take `n : ℕ` elements from the tail
- `drop_while p`: remove all the elements that satisfy a decidable `p : α → Prop` from the tail of
  a list until hitting the first non-satisfying element
- `take_while p`: take all the elements that satisfy a decidable `p : α → Prop` from the tail of
  a list until hitting the first non-satisfying element

## Implementation detail

The two predicate-based methods operate by performing the regular "from-left" operation on
`list.reverse`, followed by another `list.reverse`, so they are not the most performant.
The other two rely on `list.length l` so they still traverse the list twice. One could construct
another function that takes a `L : ℕ` and use `L - n`. Under a proof condition that
`L = l.length`, the function would do the right thing.

-/

variables {α : Type*} (p : α → Prop) [decidable_pred p] (l : list α) (n : ℕ)

namespace list

/-- Drop `n` elements from the tail end of a list. -/
def rdrop : list α := l.take (l.length - n)

@[simp] lemma rdrop_nil : rdrop ([] : list α) n = [] := by simp [rdrop]
@[simp] lemma rdrop_zero : rdrop l 0 = l := by simp [rdrop]

lemma rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n) :=
begin
  rw rdrop,
  induction l using list.reverse_rec_on with xs x IH generalizing n,
  { simp },
  { cases n,
    { simp [take_append] },
    { simp [take_append_eq_append_take, IH] } }
end

@[simp] lemma rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n :=
by simp [rdrop_eq_reverse_drop_reverse]

/-- Take `n` elements from the tail end of a list. -/
def rtake : list α := l.drop (l.length - n)

@[simp] lemma rtake_nil : rtake ([] : list α) n = [] := by simp [rtake]
@[simp] lemma rtake_zero : rtake l 0 = [] := by simp [rtake]

lemma rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n) :=
begin
  rw rtake,
  induction l using list.reverse_rec_on with xs x IH generalizing n,
  { simp },
  { cases n,
    { simp },
    { simp [drop_append_eq_append_drop, IH] } }
end

@[simp] lemma rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x] :=
by simp [rtake_eq_reverse_take_reverse]

/-- Drop elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def rdrop_while : list α := reverse (l.reverse.drop_while p)

@[simp] lemma rdrop_while_nil : rdrop_while p ([] : list α) = [] :=
by simp [rdrop_while, drop_while]
lemma rdrop_while_concat (x : α) :
  rdrop_while p (l ++ [x]) = if p x then rdrop_while p l else l ++ [x] :=
begin
  simp only [rdrop_while, drop_while, reverse_append, reverse_singleton, singleton_append],
  split_ifs with h h;
  simp [h]
end
@[simp] lemma rdrop_while_concat_pos (x : α) (h : p x) :
  rdrop_while p (l ++ [x]) = rdrop_while p l :=
by rw [rdrop_while_concat, if_pos h]
@[simp] lemma rdrop_while_concat_neg (x : α) (h : ¬ p x) :
  rdrop_while p (l ++ [x]) = l ++ [x] :=
by rw [rdrop_while_concat, if_neg h]

lemma rdrop_while_singleton (x : α) :
  rdrop_while p [x] = if p x then [] else [x] :=
by rw [←nil_append [x], rdrop_while_concat, rdrop_while_nil]

lemma rdrop_while_last_not (hl : (l.rdrop_while p) ≠ []):
  ¬ p ((rdrop_while p l).last hl) :=
begin
  simp_rw rdrop_while,
  rw last_reverse,
  exact drop_while_nth_le_zero_not _ _ _
end

lemma rdrop_while_prefix : l.rdrop_while p <+: l :=
begin
  rw [←reverse_suffix, rdrop_while, reverse_reverse],
  exact drop_while_suffix _
end

variables {p} {l}

@[simp] lemma rdrop_while_eq_nil_iff : rdrop_while p l = [] ↔ ∀ x ∈ l, p x :=
by simp [rdrop_while]

-- it is in this file because it requires `list.infix`
@[simp] lemma drop_while_eq_self_iff :
  drop_while p l = l ↔ ∀ (hl : 0 < l.length), ¬ p (l.nth_le 0 hl) :=
begin
  induction l with hd tl IH,
  { simp },
  { rw drop_while,
    split_ifs,
    { simp only [h, length, nth_le, nat.succ_pos', not_true, forall_true_left, iff_false],
      intro H,
      refine (cons_ne_self hd tl) (sublist.antisymm _ (sublist_cons _ _)),
      rw ←H,
      exact (drop_while_suffix _).sublist },
    { simp [h] } }
end

@[simp] lemma rdrop_while_eq_self_iff : rdrop_while p l = l ↔ ∀ (hl : l ≠ []), ¬ p (l.last hl) :=
begin
  simp only [rdrop_while, reverse_eq_iff, length_reverse, ne.def, drop_while_eq_self_iff,
             last_eq_nth_le, ←length_eq_zero, pos_iff_ne_zero],
  refine forall_congr _,
  intro h,
  rw [nth_le_reverse'],
  { simp },
  { rw [←ne.def, ←pos_iff_ne_zero] at h,
    simp [tsub_lt_iff_right (nat.succ_le_of_lt h)] }
end

variables (p) (l)

lemma drop_while_idempotent : drop_while p (drop_while p l) = drop_while p l :=
drop_while_eq_self_iff.mpr (drop_while_nth_le_zero_not _ _)

lemma rdrop_while_idempotent : rdrop_while p (rdrop_while p l) = rdrop_while p l :=
rdrop_while_eq_self_iff.mpr (rdrop_while_last_not _ _)

/-- Take elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def rtake_while : list α := reverse (l.reverse.take_while p)

@[simp] lemma rtake_while_nil : rtake_while p ([] : list α) = [] :=
by simp [rtake_while, take_while]
lemma rtake_while_concat (x : α) :
  rtake_while p (l ++ [x]) = if p x then rtake_while p l ++ [x] else [] :=
begin
  simp only [rtake_while, take_while, reverse_append, reverse_singleton, singleton_append],
  split_ifs with h h;
  simp [h]
end
@[simp] lemma rtake_while_concat_pos (x : α) (h : p x) :
  rtake_while p (l ++ [x]) = rtake_while p l ++ [x] :=
by rw [rtake_while_concat, if_pos h]
@[simp] lemma rtake_while_concat_neg (x : α) (h : ¬ p x) :
  rtake_while p (l ++ [x]) = [] :=
by rw [rtake_while_concat, if_neg h]

lemma rtake_while_suffix : l.rtake_while p <:+ l :=
begin
  rw [←reverse_prefix, rtake_while, reverse_reverse],
  exact take_while_prefix _
end

variables {p} {l}

@[simp] lemma rtake_while_eq_self_iff : rtake_while p l = l ↔ ∀ x ∈ l, p x :=
by simp [rtake_while, reverse_eq_iff]

@[simp] lemma rtake_while_eq_nil_iff : rtake_while p l = [] ↔ ∀ (hl : l ≠ []), ¬ p (l.last hl) :=
begin
  induction l using list.reverse_rec_on;
  simp [rtake_while]
end

lemma mem_rtake_while_imp {x : α} (hx : x ∈ rtake_while p l) : p x :=
begin
  suffices : x ∈ take_while p l.reverse,
  { exact mem_take_while_imp this },
  rwa [←mem_reverse, ←rtake_while]
end

variables (p) (l)

lemma rtake_while_idempotent : rtake_while p (rtake_while p l) = rtake_while p l :=
rtake_while_eq_self_iff.mpr (λ _, mem_rtake_while_imp)

end list
