/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic

/-!
# Prefixes, subfixes, infixes

This file proves properties about
* `list.prefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `list.subfix`: `l₁` is a subfix of `l₂` if `l₂` ends with `l₁`.
* `list.infix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some subfix of `l₂`.
* `list.inits`: The list of prefixes of a list.
* `list.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `data.list.defs`.

## Notation

`l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
`l₁ <:+ l₂`: `l₁` is a subfix of `l₂`.
`l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

open nat

variables {α β : Type*}

namespace list
variables {l l₁ l₂ l₃ : list α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/

section fix

@[simp] lemma prefix_append (l₁ l₂ : list α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩
@[simp] lemma suffix_append (l₁ l₂ : list α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

lemma infix_append (l₁ l₂ l₃ : list α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

@[simp] lemma infix_append' (l₁ l₂ l₃ : list α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) :=
by rw ← list.append_assoc; apply infix_append

lemma is_prefix.is_infix : l₁ <+: l₂ → l₁ <:+: l₂ := λ ⟨t, h⟩, ⟨[], t, h⟩
lemma is_suffix.is_infix : l₁ <:+ l₂ → l₁ <:+: l₂ := λ ⟨t, h⟩, ⟨t, [], by rw [h, append_nil]⟩

lemma nil_prefix (l : list α) : [] <+: l := ⟨l, rfl⟩
lemma nil_suffix (l : list α) : [] <:+ l := ⟨l, append_nil _⟩
lemma nil_infix (l : list α) : [] <:+: l := (nil_prefix _).is_infix

@[refl] lemma prefix_refl (l : list α) : l <+: l := ⟨[], append_nil _⟩
@[refl] lemma suffix_refl (l : list α) : l <:+ l := ⟨[], rfl⟩
@[refl] lemma infix_refl (l : list α) : l <:+: l := (prefix_refl l).is_infix

lemma prefix_rfl : l <+: l := prefix_refl _
lemma suffix_rfl : l <:+ l := suffix_refl _
lemma infix_rfl : l <:+: l := infix_refl _

@[simp] lemma suffix_cons (a : α) : ∀ l, l <:+ a :: l := suffix_append [a]

lemma prefix_concat (a : α) (l) : l <+: concat l a := by simp

lemma infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := λ ⟨L₁, L₂, h⟩, ⟨a :: L₁, L₂, h ▸ rfl⟩
lemma infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a :=
λ ⟨L₁, L₂, h⟩, ⟨L₁, concat L₂ a, by simp_rw [←h, concat_eq_append, append_assoc]⟩

@[trans] lemma is_prefix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
| l ._ ._ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩ := ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

@[trans] lemma is_suffix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
| l ._ ._ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩ := ⟨l₂ ++ l₁, append_assoc _ _ _⟩

@[trans] lemma is_infix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
| l ._ ._ ⟨l₁, r₁, rfl⟩ ⟨l₂, r₂, rfl⟩ := ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩

protected lemma is_infix.sublist : l₁ <:+: l₂ → l₁ <+ l₂ :=
λ ⟨s, t, h⟩, by { rw [← h], exact (sublist_append_right _ _).trans (sublist_append_left _ _) }

protected lemma is_prefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ := h.is_infix.sublist
protected lemma is_suffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ := h.is_infix.sublist

@[simp] lemma reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
⟨λ ⟨r, e⟩, ⟨reverse r,
  by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
 λ ⟨r, e⟩, ⟨reverse r, by rw [← reverse_append, e]⟩⟩

@[simp] lemma reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ :=
by rw ← reverse_suffix; simp only [reverse_reverse]

alias reverse_prefix ↔ _ list.is_suffix.reverse
alias reverse_suffix ↔ _ list.is_prefix.reverse

lemma infix.length_le (h : l₁ <:+: l₂) : length l₁ ≤ length l₂ := length_le_of_sublist h.sublist

lemma eq_nil_of_infix_nil (h : l <:+: []) : l = [] := eq_nil_of_sublist_nil h.sublist

@[simp] lemma infix_nil_iff : l <:+: [] ↔ l = [] :=
⟨λ h, eq_nil_of_sublist_nil h.sublist, λ h, h ▸ infix_rfl⟩

alias infix_nil_iff ↔ list.eq_nil_of_infix_nil _

@[simp] lemma prefix_nil_iff : l <+: [] ↔ l = [] :=
⟨λ h, eq_nil_of_infix_nil h.is_infix, λ h, h ▸ prefix_rfl⟩

@[simp] lemma suffix_nil_iff : l <:+ [] ↔ l = [] :=
⟨λ h, eq_nil_of_infix_nil h.is_infix, λ h, h ▸ suffix_rfl⟩

alias prefix_nil_iff ↔ list.eq_nil_of_prefix_nil _
alias suffix_nil_iff ↔ list.eq_nil_of_suffix_nil _

lemma infix_iff_prefix_suffix (l₁ l₂ : list α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
⟨λ ⟨s, t, e⟩, ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc]; exact ⟨_, rfl⟩⟩,
  λ ⟨._, ⟨t, rfl⟩, s, e⟩, ⟨s, t, by rw append_assoc; exact e⟩⟩

lemma eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
eq_of_sublist_of_length_eq h.sublist

lemma eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
eq_of_sublist_of_length_eq h.sublist

lemma eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
eq_of_sublist_of_length_eq h.sublist

lemma prefix_of_prefix_length_le : ∀ {l₁ l₂ l₃ : list α},
  l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
| []      l₂ l₃ h₁ h₂ _ := nil_prefix _
| (a :: l₁) (b :: l₂) _ ⟨r₁, rfl⟩ ⟨r₂, e⟩ ll := begin
  injection e with _ e', subst b,
  rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩
    (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩,
  exact ⟨r₃, rfl⟩
end

lemma prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
(le_total (length l₁) (length l₂)).imp
  (prefix_of_prefix_length_le h₁ h₂)
  (prefix_of_prefix_length_le h₂ h₁)

lemma suffix_of_suffix_length_le (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) :
  l₁ <:+ l₂ :=
reverse_prefix.1 $ prefix_of_prefix_length_le
  (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])

lemma suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
(prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp
  reverse_prefix.1 reverse_prefix.1

lemma suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ :=
begin
  split,
  { rintro ⟨⟨hd, tl⟩, hl₃⟩,
    { exact or.inl hl₃ },
    { simp only [cons_append] at hl₃,
      exact or.inr ⟨_, hl₃.2⟩ } },
  { rintro (rfl | hl₁),
    { exact (a :: l₂).suffix_refl },
    { exact hl₁.trans (l₂.suffix_cons _) } }
end

lemma infix_of_mem_join : ∀ {L : list (list α)}, l ∈ L → l <:+: join L
| (_  :: L) (or.inl rfl) := infix_append [] _ _
| (l' :: L) (or.inr h)   := is_infix.trans (infix_of_mem_join h) $ (suffix_append _ _).is_infix

lemma prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
exists_congr $ λ r, by rw [append_assoc, append_right_inj]

lemma prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ := prefix_append_right_inj [a]

lemma take_prefix (n) (l : list α) : take n l <+: l := ⟨_, take_append_drop _ _⟩
lemma drop_suffix (n) (l : list α) : drop n l <:+ l := ⟨_, take_append_drop _ _⟩
lemma take_sublist (n) (l : list α) : take n l <+ l := (take_prefix n l).sublist
lemma drop_sublist (n) (l : list α) : drop n l <+ l := (drop_suffix n l).sublist
lemma take_subset (n) (l : list α) : take n l ⊆ l := (take_sublist n l).subset
lemma drop_subset (n) (l : list α) : drop n l ⊆ l := (drop_sublist n l).subset
lemma mem_of_mem_take (h : a ∈ l.take n) : a ∈ l := take_subset n l h
lemma mem_of_mem_drop (h : a ∈ l.drop n) : a ∈ l := drop_subset n l h

lemma init_prefix : ∀ (l : list α), l.init <+: l
| [] := ⟨nil, by rw [init, list.append_nil]⟩
| (a :: l) := ⟨_, init_append_last (cons_ne_nil a l)⟩

lemma tail_suffix (l : list α) : tail l <:+ l := by rw ← drop_one; apply drop_suffix

lemma init_sublist (l : list α) : l.init <+ l := (init_prefix l).sublist
lemma tail_sublist (l : list α) : l.tail <+ l := (tail_suffix l).sublist
lemma init_subset (l : list α) : l.init ⊆ l := (init_sublist l).subset
lemma tail_subset (l : list α) : tail l ⊆ l := (tail_sublist l).subset
lemma mem_of_mem_init (h : a ∈ l.init) : a ∈ l := init_subset l h
lemma mem_of_mem_tail (h : a ∈ l.tail) : a ∈ l := tail_subset l h

lemma prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
⟨by rintros ⟨r, rfl⟩; rw drop_left, λ e, ⟨_, e⟩⟩

lemma suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
⟨by rintros ⟨r, rfl⟩; simp only [length_append, add_tsub_cancel_right, take_left], λ e, ⟨_, e⟩⟩

lemma prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
⟨λ h, append_right_cancel $
  (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
 λ e, e.symm ▸ take_prefix _ _⟩

lemma suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
⟨λ h, append_left_cancel $
  (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
 λ e, e.symm ▸ drop_suffix _ _⟩

instance decidable_prefix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+: l₂)
| []      l₂ := is_true ⟨l₂, rfl⟩
| (a :: l₁) [] := is_false $ λ ⟨t, te⟩, list.no_confusion te
| (a :: l₁) (b :: l₂) :=
  if h : a = b then
    @decidable_of_iff _ _ (by rw [← h, prefix_cons_inj])
      (decidable_prefix l₁ l₂)
  else
    is_false $ λ ⟨t, te⟩, h $ by injection te

-- Alternatively, use mem_tails
instance decidable_suffix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+ l₂)
| []      l₂ := is_true ⟨l₂, append_nil _⟩
| (a :: l₁) [] := is_false $ mt (length_le_of_sublist ∘ is_suffix.sublist) dec_trivial
| l₁      l₂ := let len1 := length l₁, len2 := length l₂ in
  if hl : len1 ≤ len2 then
    decidable_of_iff' (l₁ = drop (len2-len1) l₂) suffix_iff_eq_drop
  else is_false $ λ h, hl $ length_le_of_sublist $ h.sublist

lemma prefix_take_le_iff {L : list (list (option α))} (hm : m < L.length) :
  L.take m <+: L.take n ↔ m ≤ n :=
begin
  simp only [prefix_iff_eq_take, length_take],
  induction m with m IH generalizing L n,
  { simp only [min_eq_left, eq_self_iff_true, nat.zero_le, take] },
  cases L with l ls,
  { exact (not_lt_bot hm).elim },
  cases n,
  { refine iff_of_false _ (zero_lt_succ _).not_le,
    rw [take_zero, take_nil],
    simp only [take],
      exact not_false },
  { simp only [length] at hm,
    specialize @IH ls n (nat.lt_of_succ_lt_succ hm),
    simp only [le_of_lt (nat.lt_of_succ_lt_succ hm), min_eq_left] at IH,
    simp only [le_of_lt hm, IH, true_and, min_eq_left, eq_self_iff_true, length, take],
    exact ⟨nat.succ_le_succ, nat.le_of_succ_le_succ⟩ }
end

lemma cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ :=
begin
  split,
  { rintro ⟨L, hL⟩,
    simp only [cons_append] at hL,
    exact ⟨hL.left, ⟨L, hL.right⟩⟩ },
  { rintro ⟨rfl, h⟩,
    rwa [prefix_cons_inj] }
end

lemma is_prefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f :=
begin
  induction l₁ with hd tl hl generalizing l₂,
  { simp only [nil_prefix, map_nil] },
  { cases l₂ with hd₂ tl₂,
    { simpa only using eq_nil_of_prefix_nil h },
    { rw cons_prefix_iff at h,
      simp only [h, prefix_cons_inj, hl, map] } }
end

lemma is_prefix.filter_map (h : l₁ <+: l₂) (f : α → option β) :
  l₁.filter_map f <+: l₂.filter_map f :=
begin
  induction l₁ with hd₁ tl₁ hl generalizing l₂,
  { simp only [nil_prefix, filter_map_nil] },
  { cases l₂ with hd₂ tl₂,
    { simpa only using eq_nil_of_prefix_nil h },
    { rw cons_prefix_iff at h,
      rw [←@singleton_append _ hd₁ _, ←@singleton_append _ hd₂ _, filter_map_append,
         filter_map_append, h.left, prefix_append_right_inj],
      exact hl h.right } }
end

lemma is_prefix.reduce_option {l₁ l₂ : list (option α)} (h : l₁ <+: l₂) :
  l₁.reduce_option <+: l₂.reduce_option :=
h.filter_map id

lemma is_prefix.filter (p : α → Prop) [decidable_pred p] ⦃l₁ l₂ : list α⦄ (h : l₁ <+: l₂) :
  l₁.filter p <+: l₂.filter p :=
begin
  obtain ⟨xs, rfl⟩ := h,
  rw filter_append,
  exact prefix_append _ _
end

lemma is_suffix.filter (p : α → Prop) [decidable_pred p] ⦃l₁ l₂ : list α⦄ (h : l₁ <:+ l₂) :
  l₁.filter p <:+ l₂.filter p :=
begin
  obtain ⟨xs, rfl⟩ := h,
  rw filter_append,
  exact suffix_append _ _
end

lemma is_infix.filter (p : α → Prop) [decidable_pred p] ⦃l₁ l₂ : list α⦄ (h : l₁ <:+: l₂) :
  l₁.filter p <:+: l₂.filter p :=
begin
  obtain ⟨xs, ys, rfl⟩ := h,
  rw [filter_append, filter_append],
  exact infix_append _ _ _
end

end fix

section inits_tails

@[simp] lemma mem_inits : ∀ (s t : list α), s ∈ inits t ↔ s <+: t
| s []     := suffices s = nil ↔ s <+: nil, by simpa only [inits, mem_singleton],
  ⟨λ h, h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
| s (a :: t) :=
  suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t, by simpa,
  ⟨λ o, match s, o with
  | ._, or.inl rfl := ⟨_, rfl⟩
  | s, or.inr ⟨r, hr, hs⟩ := let ⟨s, ht⟩ := (mem_inits _ _).1 hr in
    by rw [← hs, ← ht]; exact ⟨s, rfl⟩
  end, λ mi, match s, mi with
  | [], ⟨._, rfl⟩ := or.inl rfl
  | (b :: s), ⟨r, hr⟩ := list.no_confusion hr $ λ ba (st : s++r = t), or.inr $
    by rw ba; exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩
  end⟩

@[simp] lemma mem_tails : ∀ (s t : list α), s ∈ tails t ↔ s <:+ t
| s []     := by simp only [tails, mem_singleton];
  exact ⟨λ h, by rw h; exact suffix_refl [], eq_nil_of_suffix_nil⟩
| s (a :: t) := by simp only [tails, mem_cons_iff, mem_tails s t];
  exact show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t, from
  ⟨λ o, match s, t, o with
  | ._, t, or.inl rfl := suffix_rfl
  | s, ._, or.inr ⟨l, rfl⟩ := ⟨a :: l, rfl⟩
  end, λ e, match s, t, e with
  | ._, t, ⟨[], rfl⟩ := or.inl rfl
  | s, t, ⟨b :: l, he⟩ := list.no_confusion he (λ ab lt, or.inr ⟨l, lt⟩)
  end⟩

lemma inits_cons (a : α) (l : list α) : inits (a :: l) = [] :: l.inits.map (λ t, a :: t) := by simp
lemma tails_cons (a : α) (l : list α) : tails (a :: l) = (a :: l) :: l.tails := by simp

@[simp]
lemma inits_append : ∀ (s t : list α), inits (s ++ t) = s.inits ++ t.inits.tail.map (λ l, s ++ l)
| [] [] := by simp
| [] (a :: t) := by simp
| (a :: s) t := by simp [inits_append s t]

@[simp]
lemma tails_append : ∀ (s t : list α), tails (s ++ t) = s.tails.map (λ l, l ++ t) ++ t.tails.tail
| [] [] := by simp
| [] (a :: t) := by simp
| (a :: s) t := by simp [tails_append s t]

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
lemma inits_eq_tails : ∀ (l : list α), l.inits = (reverse $ map reverse $ tails $ reverse l)
| [] := by simp
| (a :: l) := by simp [inits_eq_tails l, map_eq_map_iff]

lemma tails_eq_inits : ∀ (l : list α), l.tails = (reverse $ map reverse $ inits $ reverse l)
| [] := by simp
| (a :: l) := by simp [tails_eq_inits l, append_left_inj]

lemma inits_reverse (l : list α) : inits (reverse l) = reverse (map reverse l.tails) :=
by { rw tails_eq_inits l, simp [reverse_involutive.comp_self] }

lemma tails_reverse (l : list α) : tails (reverse l) = reverse (map reverse l.inits) :=
by { rw inits_eq_tails l, simp [reverse_involutive.comp_self] }

lemma map_reverse_inits (l : list α) : map reverse l.inits = (reverse $ tails $ reverse l) :=
by { rw inits_eq_tails l, simp [reverse_involutive.comp_self] }

lemma map_reverse_tails (l : list α) : map reverse l.tails = (reverse $ inits $ reverse l) :=
by { rw tails_eq_inits l, simp [reverse_involutive.comp_self] }

@[simp] lemma length_tails (l : list α) : length (tails l) = length l + 1 :=
begin
  induction l with x l IH,
  { simp },
  { simpa using IH }
end

@[simp] lemma length_inits (l : list α) : length (inits l) = length l + 1 :=
by simp [inits_eq_tails]

@[simp] lemma nth_le_tails (l : list α) (n : ℕ) (hn : n < length (tails l)) :
  nth_le (tails l) n hn = l.drop n :=
begin
  induction l with x l IH generalizing n,
  { simp },
  { cases n,
    { simp },
    { simpa using IH n _ } }
end

@[simp] lemma nth_le_inits (l : list α) (n : ℕ) (hn : n < length (inits l)) :
  nth_le (inits l) n hn = l.take n :=
begin
  induction l with x l IH generalizing n,
  { simp },
  { cases n,
    { simp },
    { simpa using IH n _ } }
end

instance decidable_infix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+: l₂)
| []        l₂ := is_true ⟨[], l₂, rfl⟩
| (a :: l₁) [] := is_false $ λ ⟨s, t, te⟩, absurd te $ append_ne_nil_of_ne_nil_left _ _ $
                append_ne_nil_of_ne_nil_right _ _ $ λ h, list.no_confusion h
| l₁        l₂ := decidable_of_decidable_of_iff (list.decidable_bex (λ t, l₁ <+: t) (tails l₂)) $
  by refine (exists_congr (λ t, _)).trans (infix_iff_prefix_suffix _ _).symm;
     exact ⟨λ ⟨h1, h2⟩, ⟨h2, (mem_tails _ _).1 h1⟩, λ ⟨h2, h1⟩, ⟨(mem_tails _ _).2 h1, h2⟩⟩

end inits_tails

/-! ### insert -/

section insert
variable [decidable_eq α]

@[simp] lemma insert_nil (a : α) : insert a nil = [a] := rfl

lemma insert.def (a : α) (l : list α) : insert a l = if a ∈ l then l else a :: l := rfl

@[simp, priority 980]
lemma insert_of_mem (h : a ∈ l) : insert a l = l := by simp only [insert.def, if_pos h]

@[simp, priority 970]
lemma insert_of_not_mem (h : a ∉ l) : insert a l = a :: l :=
by simp only [insert.def, if_neg h]; split; refl

@[simp] lemma mem_insert_iff : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
begin
  by_cases h' : b ∈ l,
  { simp only [insert_of_mem h'],
    apply (or_iff_right_of_imp _).symm,
    exact λ e, e.symm ▸ h' },
  { simp only [insert_of_not_mem h', mem_cons_iff] }
end

@[simp] lemma suffix_insert (a : α) (l : list α) : l <:+ insert a l :=
by by_cases a ∈ l; [simp only [insert_of_mem h], simp only [insert_of_not_mem h, suffix_cons]]

lemma infix_insert (a : α) (l : list α) : l <:+: insert a l := (suffix_insert a l).is_infix
lemma sublist_insert (a : α) (l : list α) : l <+  l.insert a := (suffix_insert a l).sublist
lemma subset_insert (a : α) (l : list α) : l ⊆ l.insert a := (sublist_insert a l).subset

@[simp] lemma mem_insert_self (a : α) (l : list α) : a ∈  l.insert a :=
mem_insert_iff.2 $ or.inl rfl

lemma mem_insert_of_mem (h : a ∈ l) : a ∈ insert b l := mem_insert_iff.2 (or.inr h)

lemma eq_or_mem_of_mem_insert (h : a ∈ insert b l) : a = b ∨ a ∈ l := mem_insert_iff.1 h

@[simp] lemma length_insert_of_mem (h : a ∈ l) : (insert a l).length = l.length :=
congr_arg _ $ insert_of_mem h

@[simp] lemma length_insert_of_not_mem (h : a ∉ l) : (insert a l).length = l.length + 1 :=
congr_arg _ $ insert_of_not_mem h

end insert
end list
