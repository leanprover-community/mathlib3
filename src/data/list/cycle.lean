/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.list.rotate
import tactic.slim_check

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `is_rotated`.

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

Based on this, we define the quotient of lists by the rotation relation, called `cycle`.
We define a permutation from a `s : cycle α` by lifting `form_perm` into the quotient.

-/

namespace list

variables {α : Type*} [decidable_eq α]

/--
Given an element `x : α` of `l : list α` such that `x ∈ l`, get the next
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.
-/
def next: Π (l : list α) (x : α) (h : x ∈ l), α
| []             _ h := by simpa using h
| [y]            _ _ := y
| (y :: z :: xs) x h := if hx : x = y then z else
  if x = (y :: z :: xs).last (cons_ne_nil _ _) then y
    else next (z :: xs) x (by simpa [hx] using h)

/--
Given an element `x : α` of `l : list α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.
-/
def prev : Π (l : list α) (x : α) (h : x ∈ l), α
| []             _ h := by simpa using h
| [y]            _ _ := y
| (y :: z :: xs) x h := if hx : x = y then (last (z :: xs) (cons_ne_nil _ _)) else
  if x = z then y else prev (z :: xs) x (by simpa [hx] using h)

variables (l : list α) (x : α) (h : x ∈ l)

@[simp] lemma next_singleton (x y : α) (h : x ∈ [y]) :
  next [y] x h = y := rfl

@[simp] lemma prev_singleton (x y : α) (h : x ∈ [y]) :
  prev [y] x h = y := rfl

lemma next_cons_cons_eq' (y z : α) (h : x ∈ (y :: z :: l)) (hx : x = y) :
  next (y :: z :: l) x h = z :=
by rw [next, dif_pos hx]

@[simp] lemma next_cons_cons_eq (z : α) (h : x ∈ (x :: z :: l)) :
  next (x :: z :: l) x h = z :=
next_cons_cons_eq' l x x z h rfl

lemma next_last_cons (y : α) (h : x ∈ (y :: l)) (hy : x ≠ y)
  (hx : x = last (y :: l) (cons_ne_nil _ _)) :
  next (y :: l) x h = y :=
begin
  cases l,
  { simp },
  { rw [next, dif_neg hy, if_pos hx] }
end

lemma next_ne_head_ne_last (y : α) (h : x ∈ (y :: l)) (hy : x ≠ y)
  (hx : x ≠ last (y :: l) (cons_ne_nil _ _)) :
  next (y :: l) x h = next l x (by simpa [hy] using h) :=
begin
  cases l,
  { simpa [hy] using h },
  { rw [next, dif_neg hy, if_neg hx] }
end

lemma prev_last_cons' (y : α) (h : x ∈ (y :: l)) (hx : x = y) :
  prev (y :: l) x h = last (y :: l) (cons_ne_nil _ _) :=
begin
  cases l;
  simp [prev, hx]
end

@[simp] lemma prev_last_cons (h : x ∈ (x :: l)) :
  prev (x :: l) x h = last (x :: l) (cons_ne_nil _ _) :=
prev_last_cons' l x x h rfl

lemma prev_cons_cons_eq' (y z : α) (h : x ∈ (y :: z :: l)) (hx : x = y) :
  prev (y :: z :: l) x h = last (z :: l) (cons_ne_nil _ _) :=
by rw [prev, dif_pos hx]

@[simp] lemma prev_cons_cons_eq (z : α) (h : x ∈ (x :: z :: l)) :
  prev (x :: z :: l) x h = last (z :: l) (cons_ne_nil _ _) :=
prev_cons_cons_eq' l x x z h rfl

lemma prev_cons_cons_of_ne' (y z : α) (h : x ∈ (y :: z :: l)) (hy : x ≠ y) (hz : x = z) :
  prev (y :: z :: l) x h = y :=
begin
  cases l,
  { simp [prev, hy, hz] },
  { rw [prev, dif_neg hy, if_pos hz] }
end

lemma prev_cons_cons_of_ne (y : α) (h : x ∈ (y :: x :: l)) (hy : x ≠ y) :
  prev (y :: x :: l) x h = y :=
prev_cons_cons_of_ne' _ _ _ _ _ hy rfl

lemma prev_ne_cons_cons (y z : α) (h : x ∈ (y :: z :: l)) (hy : x ≠ y) (hz : x ≠ z) :
  prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h) :=
begin
  cases l,
  { simpa [hy, hz] using h },
  { rw [prev, dif_neg hy, if_neg hz] }
end

include h

lemma next_mem : l.next x h ∈ l :=
begin
  cases l with hd tl,
  { simpa using h },
  induction tl with hd' tl hl generalizing hd,
  { simp },
  { by_cases hx : x = hd,
    { simp [hx] },
    { rw [next, dif_neg hx],
      split_ifs with hm,
      { exact mem_cons_self _ _ },
      { exact mem_cons_of_mem _ (hl _ _) } } }
end

lemma prev_mem : l.prev x h ∈ l :=
begin
  cases l with hd tl,
  { simpa using h },
  induction tl with hd' tl hl generalizing hd,
  { simp },
  { by_cases hx : x = hd,
    { simp only [hx, prev_cons_cons_eq],
      exact mem_cons_of_mem _ (last_mem _) },
    { rw [prev, dif_neg hx],
      split_ifs with hm,
      { exact mem_cons_self _ _ },
      { exact mem_cons_of_mem _ (hl _ _) } } }
end

lemma next_nth_le (l : list α) (h : nodup l) (n : ℕ) (hn : n < l.length) :
  next l (l.nth_le n hn) (nth_le_mem _ _ _) = l.nth_le ((n + 1) % l.length)
    (nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
begin
  cases l with x l,
  { simpa using hn },
  induction l with y l hl generalizing x n,
  { simp },
  { cases n,
    { simp },
    { have hn' : n.succ ≤ l.length.succ,
      { refine nat.succ_le_of_lt _,
        simpa [nat.succ_lt_succ_iff] using hn },
      have hx': (x :: y :: l).nth_le n.succ hn ≠ x,
      { intro H,
        suffices : n.succ = 0,
        { simpa },
        rw nodup_iff_nth_le_inj at h,
        refine h _ _ hn nat.succ_pos' _,
        simpa using H },
      rcases hn'.eq_or_lt with hn''|hn'',
      { rw [next_last_cons],
        { simp [hn''] },
        { exact hx' },
        { simp [last_eq_nth_le, hn''] } },
      { have : n < l.length := by simpa [nat.succ_lt_succ_iff] using hn'' ,
        rw [next_ne_head_ne_last _ _ _ _ hx'],
        { simp [nat.mod_eq_of_lt (nat.succ_lt_succ (nat.succ_lt_succ this)),
                hl _ _ (nodup_of_nodup_cons h), nat.mod_eq_of_lt (nat.succ_lt_succ this)] },
        { rw last_eq_nth_le,
          intro H,
          suffices : n.succ = l.length.succ,
          { exact absurd hn'' this.ge.not_lt },
          rw nodup_iff_nth_le_inj at h,
          refine h _ _ hn _ _,
          { simp },
          { simpa using H } } } } }
end

lemma prev_nth_le (l : list α) (h : nodup l) (n : ℕ) (hn : n < l.length) :
  prev l (l.nth_le n hn) (nth_le_mem _ _ _) = l.nth_le ((n + (l.length - 1)) % l.length)
    (nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
begin
  cases l with x l,
  { simpa using hn },
  induction l with y l hl generalizing n x,
  { simp },
  { rcases n with _|_|n,
    { simpa [last_eq_nth_le, nat.mod_eq_of_lt (nat.succ_lt_succ l.length.lt_succ_self)] },
    { simp only [mem_cons_iff, nodup_cons] at h,
      push_neg at h,
      simp [add_comm, prev_cons_cons_of_ne, h.left.left.symm] },
    { rw [prev_ne_cons_cons],
      { convert hl _ _ (nodup_of_nodup_cons h) _ using 1,
        have : ∀ k hk, (y :: l).nth_le k hk = (x :: y :: l).nth_le (k + 1) (nat.succ_lt_succ hk),
        { intros,
          simpa },
        rw [this],
        congr,
        simp only [nat.add_succ_sub_one, add_zero, length],
        simp only [length, nat.succ_lt_succ_iff] at hn,
        set k := l.length,
        rw [nat.succ_add, ←nat.add_succ, nat.add_mod_right, nat.succ_add, ←nat.add_succ _ k,
            nat.add_mod_right, nat.mod_eq_of_lt, nat.mod_eq_of_lt],
        { exact nat.lt_succ_of_lt hn },
        { exact nat.succ_lt_succ (nat.lt_succ_of_lt hn) } },
      { intro H,
        suffices : n.succ.succ = 0,
        { simpa },
        rw nodup_iff_nth_le_inj at h,
        refine h _ _ hn nat.succ_pos' _,
        simpa using H },
      { intro H,
        suffices : n.succ.succ = 1,
        { simpa },
        rw nodup_iff_nth_le_inj at h,
        refine h _ _ hn (nat.succ_lt_succ nat.succ_pos') _,
        simpa using H } } }
end

lemma pmap_next_eq_rotate_one (h : nodup l) :
  l.pmap l.next (λ _ h, h) = l.rotate 1 :=
begin
  apply list.ext_le,
  { simp },
  { intros,
    rw [nth_le_pmap, nth_le_rotate, next_nth_le _ h] }
end

lemma pmap_prev_eq_rotate_length_sub_one (h : nodup l) :
  l.pmap l.prev (λ _ h, h) = l.rotate (l.length - 1) :=
begin
  apply list.ext_le,
  { simp },
  { intros n hn hn',
    rw [nth_le_rotate, nth_le_pmap, prev_nth_le _ h] }
end

lemma prev_next (l : list α) (h : nodup l) (x : α) (hx : x ∈ l) :
  prev l (next l x hx) (next_mem _ _ _) = x :=
begin
  obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx,
  simp only [next_nth_le, prev_nth_le, h, nat.mod_add_mod],
  cases l with hd tl,
  { simp },
  { have : n < 1 + tl.length := by simpa [add_comm] using hn,
    simp [add_left_comm, add_comm, add_assoc, nat.mod_eq_of_lt this] }
end

lemma next_prev (l : list α) (h : nodup l) (x : α) (hx : x ∈ l) :
  next l (prev l x hx) (prev_mem _ _ _) = x :=
begin
  obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx,
  simp only [next_nth_le, prev_nth_le, h, nat.mod_add_mod],
  cases l with hd tl,
  { simp },
  { have : n < 1 + tl.length := by simpa [add_comm] using hn,
    simp [add_left_comm, add_comm, add_assoc, nat.mod_eq_of_lt this] }
end

lemma prev_reverse_eq_next (l : list α) (h : nodup l) (x : α) (hx : x ∈ l) :
  prev l.reverse x (mem_reverse.mpr hx) = next l x hx :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  have lpos : 0 < l.length := k.zero_le.trans_lt hk,
  have key : l.length - 1 - k < l.length :=
    (nat.sub_le _ _).trans_lt (nat.sub_lt_self lpos nat.succ_pos'),
  rw ←nth_le_pmap l.next (λ _ h, h) (by simpa using hk),
  simp_rw [←nth_le_reverse l k (key.trans_le (by simp)), pmap_next_eq_rotate_one _ h],
  rw ←nth_le_pmap l.reverse.prev (λ _ h, h),
  { simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
             length_reverse, nat.mod_eq_of_lt (nat.sub_lt_self lpos nat.succ_pos'),
             nat.sub_sub_self (nat.succ_le_of_lt lpos)],
    rw ←nth_le_reverse,
    { simp [nat.sub_sub_self (nat.le_pred_of_lt hk)] },
    { simpa using (nat.sub_le _ _).trans_lt (nat.sub_lt_self lpos nat.succ_pos') } },
  { simpa using (nat.sub_le _ _).trans_lt (nat.sub_lt_self lpos nat.succ_pos') }
end

lemma next_reverse_eq_prev (l : list α) (h : nodup l) (x : α) (hx : x ∈ l) :
  next l.reverse x (mem_reverse.mpr hx) = prev l x hx :=
begin
  convert (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm,
  exact (reverse_reverse l).symm
end

lemma is_rotated_next_eq {l l' : list α} (h : l ~r l') (hn : nodup l) {x : α} (hx : x ∈ l) :
  l.next x hx = l'.next x (h.mem_iff.mp hx) :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  obtain ⟨n, rfl⟩ := id h,
  rw [next_nth_le _ hn],
  simp_rw ←nth_le_rotate' _ n k,
  rw [next_nth_le _ (h.nodup_iff.mp hn), ←nth_le_rotate' _ n],
  simp [add_assoc]
end

lemma is_rotated_prev_eq {l l' : list α} (h : l ~r l') (hn : nodup l) {x : α} (hx : x ∈ l) :
  l.prev x hx = l'.prev x (h.mem_iff.mp hx) :=
begin
  rw [←next_reverse_eq_prev _ hn, ←next_reverse_eq_prev _ (h.nodup_iff.mp hn)],
  exact is_rotated_next_eq h.reverse (nodup_reverse.mpr hn) _
end

end list

open list

/--
`cycle α` is the quotient of `list α` by cyclic permutation.
Duplicates are allowed.
-/
def cycle (α : Type*) : Type* := quotient (is_rotated.setoid α)

namespace cycle

variables {α : Type*}

instance : has_coe (list α) (cycle α) := ⟨quot.mk _⟩

@[simp] lemma coe_eq_coe {l₁ l₂ : list α} : (l₁ : cycle α) = l₂ ↔ (l₁ ~r l₂) :=
@quotient.eq _ (is_rotated.setoid _) _ _

@[simp] lemma mk_eq_coe (l : list α) :
  quot.mk _ l = (l : cycle α) := rfl

instance : inhabited (cycle α) := ⟨(([] : list α) : cycle α)⟩

/--
For `x : α`, `s : cycle α`, `x ∈ s` indicates that `x` occurs at least once in `s`.
-/
def mem (a : α) (s : cycle α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.mem_iff)

instance : has_mem α (cycle α) := ⟨mem⟩

@[simp] lemma mem_coe_iff {a : α} {l : list α} :
  a ∈ (l : cycle α) ↔ a ∈ l := iff.rfl

instance [decidable_eq α] : decidable_eq (cycle α) :=
λ s₁ s₂, quotient.rec_on_subsingleton₂' s₁ s₂ (λ l₁ l₂,
  decidable_of_iff' _ quotient.eq')

instance [decidable_eq α] (x : α) (s : cycle α) : decidable (x ∈ s) :=
quotient.rec_on_subsingleton' s (λ l, list.decidable_mem x l)

/--
Reverse a `s : cycle α` by reversing the underlying `list`.
-/
def reverse (s : cycle α) : cycle α :=
quot.map reverse (λ l₁ l₂ (e : l₁ ~r l₂), e.reverse) s

lemma coe_reverse (l : list α) :
  (l.reverse : cycle α) = reverse l := rfl

@[simp] lemma mem_reverse_iff {a : α} {s : cycle α} :
  a ∈ s.reverse ↔ a ∈ s :=
quot.induction_on s (λ _, mem_reverse)

/--
The length of the `s : cycle α`, which is the number of elements, counting duplicates.
-/
def length (s : cycle α) : ℕ :=
quot.lift_on s length (λ l₁ l₂ (e : l₁ ~r l₂), e.perm.length_eq)

@[simp] lemma length_coe (l : list α) :
  length (l : cycle α) = l.length := rfl

@[simp] lemma length_reverse (s : cycle α) :
  s.reverse.length = s.length :=
quot.induction_on s length_reverse

/--
A `s : cycle α` that is at most one element.
-/
def subsingleton (s : cycle α) : Prop :=
s.length ≤ 1

lemma length_subsingleton_iff {s : cycle α} :
  subsingleton s ↔ length s ≤ 1 := iff.rfl

@[simp] lemma subsingleton_reverse_iff {s : cycle α} :
  s.reverse.subsingleton ↔ s.subsingleton :=
by simp [length_subsingleton_iff]

/--
A `s : cycle α` that is made up of at least two unique elements.
-/
def nontrivial (s : cycle α) : Prop := ∃ (x y : α) (h : x ≠ y), x ∈ s ∧ y ∈ s

@[simp] lemma nontrivial_reverse_iff {s : cycle α} :
  s.reverse.nontrivial ↔ s.nontrivial :=
by simp [nontrivial]

lemma length_nontrivial {s : cycle α} (h : nontrivial s) :
  2 ≤ length s :=
begin
  obtain ⟨x, y, hxy, hx, hy⟩ := h,
  induction s using quot.induction_on with l,
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩),
  { simpa using hx },
  { simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy,
    simpa [hx, hy] using hxy },
  { simp [bit0] }
end

/--
The `s : cycle α` contains no duplicates.
-/
def nodup (s : cycle α) : Prop :=
quot.lift_on s nodup (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.nodup_iff)

@[simp] lemma nodup_coe_iff {l : list α} :
  nodup (l : cycle α) ↔ l.nodup := iff.rfl

@[simp] lemma nodup_reverse_iff {s : cycle α} :
  s.reverse.nodup ↔ s.nodup :=
quot.induction_on s (λ _, nodup_reverse)

lemma subsingleton.nodup {s : cycle α} (h : subsingleton s) :
  nodup s :=
begin
  induction s using quot.induction_on with l,
  cases l with hd tl,
  { simp },
  { have : tl = [] := by simpa [subsingleton, length_eq_zero] using h,
    simp [this] }
end

instance [decidable_eq α] {s : cycle α} : decidable (nodup s) :=
quot.rec_on_subsingleton s (λ (l : list α), list.nodup_decidable l)

/-- Given a `s : cycle α` such that `nodup s`, retrieve the next element after `x ∈ s`. -/
def next [decidable_eq α] : Π (s : cycle α) (hs : nodup s) (x : α) (hx : x ∈ s), α :=
λ s, quot.hrec_on s (λ l hn x hx, next l x hx)
  (λ l₁ l₂ (h : l₁ ~r l₂),
  function.hfunext (propext h.nodup_iff) (λ h₁ h₂ he, function.hfunext rfl
    (λ x y hxy, function.hfunext (propext (by simpa [eq_of_heq hxy] using h.mem_iff))
    (λ hm hm' he', heq_of_eq (by simpa [eq_of_heq hxy] using is_rotated_next_eq h h₁ _)))))

/-- Given a `s : cycle α` such that `nodup s`, retrieve the previous element before `x ∈ s`. -/
def prev [decidable_eq α] : Π (s : cycle α) (hs : nodup s) (x : α) (hx : x ∈ s), α :=
λ s, quot.hrec_on s (λ l hn x hx, prev l x hx)
  (λ l₁ l₂ (h : l₁ ~r l₂),
  function.hfunext (propext h.nodup_iff) (λ h₁ h₂ he, function.hfunext rfl
    (λ x y hxy, function.hfunext (propext (by simpa [eq_of_heq hxy] using h.mem_iff))
    (λ hm hm' he', heq_of_eq (by simpa [eq_of_heq hxy] using is_rotated_prev_eq h h₁ _)))))

end cycle
