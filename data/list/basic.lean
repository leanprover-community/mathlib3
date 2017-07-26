/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn

Basic properties of lists.
-/
import logic.basic data.nat.basic data.option
open function nat

namespace list
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

@[simp] theorem cons_ne_nil (a : α) (l : list α) : a::l ≠ [].

theorem head_eq_of_cons_eq {α : Type} {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

theorem tail_eq_of_cons_eq {α : Type} {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

theorem cons_inj {α : Type} {a : α} : injective (cons a) :=
assume l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

/- append -/

theorem append_ne_nil_of_ne_nil_left (s t : list α) : s ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

theorem append_ne_nil_of_ne_nil_right (s t : list α) : t ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

theorem append_foldl (f : α → β → α) (a : α) (s t : list β) : foldl f a (s ++ t) = foldl f (foldl f a s) t :=
by {revert a, induction s with b s H, exact λ_, rfl, intros, simp [foldl], rw H _}

theorem append_foldr (f : α → β → β) (a : β) (s t : list α) : foldr f a (s ++ t) = foldr f (foldr f a t) s :=
by {revert a, induction s with b s H, exact λ_, rfl, intros, simp [foldr], rw H _}

/- repeat take drop -/

def split_at : ℕ → list α → list α × list α
| 0        a         := ([], a)
| (succ n) []        := ([], [])
| (succ n) (x :: xs) := let (l, r) := split_at n xs in (x :: l, r)

@[simp] theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : list α), split_at n l = (take n l, drop n l)
| 0        a         := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := by simp [split_at, split_at_eq_take_drop n xs]

@[simp] theorem take_append_drop : ∀ (n : ℕ) (l : list α), take n l ++ drop n l = l
| 0        a         := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := by simp [take_append_drop n xs]

-- TODO(Leo): cleanup proof after arith dec proc
theorem append_inj : ∀ {s₁ s₂ t₁ t₂ : list α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
| []      []      t₁ t₂ h hl := ⟨rfl, h⟩
| (a::s₁) []      t₁ t₂ h hl := list.no_confusion $ eq_nil_of_length_eq_zero hl
| []      (b::s₂) t₁ t₂ h hl := list.no_confusion $ eq_nil_of_length_eq_zero hl.symm
| (a::s₁) (b::s₂) t₁ t₂ h hl := list.no_confusion h $ λab hap,
  let ⟨e1, e2⟩ := @append_inj s₁ s₂ t₁ t₂ hap (succ.inj hl) in
  by rw [ab, e1, e2]; exact ⟨rfl, rfl⟩

theorem append_inj_left {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
(append_inj h hl).left

theorem append_inj_right {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
(append_inj h hl).right

theorem append_right_inj {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
append_inj h $ @nat.add_right_cancel _ (length t₁) _ $
let hap := congr_arg length h in by simp at hap; rwa [← hl] at hap

/- concat -/

def concat : list α → α → list α
| []     a := [a]
| (b::l) a := b :: concat l a
attribute [simp] concat

@[simp] theorem concat_nil (a : α) : concat [] a = [a] := rfl

@[simp] theorem concat_cons (a b : α) (l : list α) :
  concat (a :: l) b  = a :: concat l b := rfl

@[simp] theorem concat_ne_nil (a : α) (l : list α) : concat l a ≠ [] :=
by induction l; intro h; contradiction

@[simp] theorem concat_append (a : α) (l₁ l₂ : list α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
by induction l₁ with b l₁ ih; [simp, simp [ih]]

@[simp] lemma concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
by induction l; simp [*, concat]

@[simp] lemma length_concat (a : α) (l : list α) : length (concat l a) = succ (length l) :=
by simp [succ_eq_add_one]

theorem append_concat (a : α) (l₁ l₂ : list α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a :=
by induction l₂ with b l₂ ih; simp

/- reverse -/

@[simp] theorem reverse_nil : reverse (@nil α) = [] :=
rfl

local attribute [simp] reverse_core

@[simp] theorem reverse_cons (a : α) (l : list α) : reverse (a::l) = concat (reverse l) a :=
have aux : ∀ l₁ l₂, reverse_core l₁ (concat l₂ a) = concat (reverse_core l₁ l₂) a,
  by intros l₁; induction l₁; intros; rsimp,
aux l nil

@[simp] theorem reverse_singleton (a : α) : reverse [a] = [a] :=
rfl

@[simp] theorem reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
by induction s; simp [*]

@[simp] theorem reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; simp [*]

theorem concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
by simp

@[simp] theorem length_reverse (l : list α) : length (reverse l) = length l :=
by induction l; simp [*]

@[simp] theorem map_reverse (f : α → β) (l : list α) : map f (reverse l) = reverse (map f l) :=
by induction l; simp [*]

/- last -/

@[simp] theorem last_cons {a : α} {l : list α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
by {induction l; intros, contradiction, simp [*], reflexivity}

@[simp] theorem last_append {a : α} (l : list α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
begin
  induction l with hd tl ih; rsimp,
  have haux : tl ++ [a] ≠ [],
    {apply append_ne_nil_of_ne_nil_right, contradiction},
  simp [*]
end

theorem last_concat {a : α} (l : list α) (h : concat l a ≠ []) : last (concat l a) h = a :=
by simp [*]

@[simp] theorem last_singleton (a : α) (h : [a] ≠ []) : last [a] h = a := rfl

@[simp] theorem last_cons_cons (a₁ a₂ : α) (l : list α) (h : a₁::a₂::l ≠ []) :
  last (a₁::a₂::l) h = last (a₂::l) (cons_ne_nil a₂ l) := rfl

theorem last_congr {l₁ l₂ : list α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ :=
by subst l₁

/- head and tail -/

@[simp] theorem head_cons [h : inhabited α] (a : α) (l : list α) : head (a::l) = a := rfl

@[simp] theorem tail_nil : tail (@nil α) = [] := rfl

@[simp] theorem tail_cons (a : α) (l : list α) : tail (a::l) = l := rfl

@[simp] theorem head_append [h : inhabited α] (t : list α) {s : list α} (h : s ≠ []) : head (s ++ t) = head s :=
by {induction s, contradiction, simp}

theorem cons_head_tail [h : inhabited α] {l : list α} (h : l ≠ []) : (head l)::(tail l) = l :=
by {induction l, contradiction, simp}

/- map -/

lemma map_concat (f : α → β) (a : α) (l : list α) : map f (concat l a) = concat (map f l) (f a) :=
by induction l; simp [*]

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : list α) : map f l = l :=
by induction l; simp [*]

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : list β) : foldl f a (map g l) = foldl (λx y, f x (g y)) a l :=
by revert a; induction l; intros; simp [*, foldl]

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : list β) : foldr f a (map g l) = foldr (f ∘ g) a l :=
by revert a; induction l; intros; simp [*, foldr]

theorem foldl_hom (f : α → β) (g : α → γ → α) (g' : β → γ → β) (a : α)
  (h : ∀a x, f (g a x) = g' (f a) x) (l : list γ) : f (foldl g a l) = foldl g' (f a) l :=
by revert a; induction l; intros; simp [*, foldl]

theorem foldr_hom (f : α → β) (g : γ → α → α) (g' : γ → β → β) (a : α)
  (h : ∀x a, f (g x a) = g' x (f a)) (l : list γ) : f (foldr g a l) = foldr g' (f a) l :=
by revert a; induction l; intros; simp [*, foldr]

/- filter_map -/

def filter_map (f : α → option β) : list α → list β
| []     := []
| (a::l) :=
  match f a with
  | none   := filter_map l
  | some b := b :: filter_map l
  end

/- mem -/

theorem eq_nil_of_forall_not_mem : ∀ {l : list α}, (∀ a, a ∉ l) → l = nil
| []        := assume h, rfl
| (b :: l') := assume h, absurd (mem_cons_self b l') (h b)

theorem mem_singleton {a b : α} : a ∈ [b] → a = b :=
assume : a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (assume : a = b, this)
  (assume : a ∈ [], absurd this (not_mem_nil a))

@[simp] theorem mem_singleton_iff (a b : α) : a ∈ [b] ↔ a = b :=
iff.intro mem_singleton (begin intro h, simp [h] end)

theorem mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (assume : a = b, begin subst a, exact binl end)
  (assume : a ∈ l, this)

theorem not_mem_append {a : α} {s t : list α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s++t :=
mt mem_append.1 $ not_or_of_not_and_not ⟨h₁, h₂⟩

theorem length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| (b::l) _ := zero_lt_succ _

theorem mem_split {a : α} {l : list α} (h : a ∈ l) : ∃ s t : list α, l = s ++ (a::t) :=
begin
  induction l with b l ih; simp at h; cases h with h h,
  { subst h, exact ⟨[], l, rfl⟩ },
  { cases ih h with s e, cases e with t e,
    subst l, exact ⟨b::s, t, rfl⟩ }
end

theorem mem_of_ne_of_mem {a y : α} {l : list α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
or.elim (eq_or_mem_of_mem_cons h₂) (λe, absurd e h₁) (λr, r)

theorem ne_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : list α} : a ≠ y → a ∉ l → a ∉ y::l :=
assume p1 p2, not.intro (assume Pain, absurd (eq_or_mem_of_mem_cons Pain) (not_or p1 p2))

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : list α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
assume p, and.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

@[simp] theorem mem_reverse (a : α) (l : list α) : a ∈ reverse l ↔ a ∈ l :=
by induction l; simp [*]; rw mem_append_eq

theorem mem_map (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l with b l' ih,
  {simp at h, contradiction },
  {simp, simp at h, cases h with h h,
    {simp [*]},
    {exact or.inr (ih h)}}
end

theorem exists_of_mem_map {f : α → β} {b : β} {l : list α} (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  {simp at h, contradiction},
  {cases (eq_or_mem_of_mem_cons h) with h h,
    {existsi c, simp [h]},
    {cases ih h with a ha, cases ha with ha₁ ha₂,
      existsi a, simp [*] }}
end

theorem mem_map_iff {f : α → β} {b : β} {l : list α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
⟨exists_of_mem_map, λ ⟨a, la, h⟩, by rw [← h]; exact mem_map f la⟩

theorem mem_join_iff {a : α} : ∀ {L : list (list α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l
| []       := ⟨false.elim, λ⟨_, h, _⟩, false.elim h⟩
| (c :: L) := by simp [join, @mem_join_iff L]; exact
  ⟨λh, match h with
  | or.inl ac         := ⟨c, ac, or.inl rfl⟩
  | or.inr ⟨l, al, lL⟩ := ⟨l, al, or.inr lL⟩
  end,
  λ⟨l, al, o⟩, o.elim (λ lc, by rw lc at al; exact or.inl al) (λlL, or.inr ⟨l, al, lL⟩)⟩

theorem exists_of_mem_join {a : α} {L : list (list α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
mem_join_iff.1

theorem mem_join {a : α} {L : list (list α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
mem_join_iff.2 ⟨l, lL, al⟩

lemma mem_bind_iff {b : β} {l : list α} {f : α → list β} : b ∈ bind l f ↔ ∃ a ∈ l, b ∈ f a :=
iff.trans mem_join_iff
  ⟨λ ⟨l', h1, h2⟩, let ⟨a, al, fa⟩ := exists_of_mem_map h1 in ⟨a, al, fa.symm ▸ h2⟩,
  λ ⟨a, al, bfa⟩, ⟨f a, mem_map _ al, bfa⟩⟩

lemma exists_of_mem_bind {b : β} {l : list α} {f : α → list β} : b ∈ bind l f → ∃ a ∈ l, b ∈ f a :=
mem_bind_iff.1

lemma mem_bind {b : β} {l : list α} {f : α → list β} {a} (al : a ∈ l) (h : b ∈ f a) : b ∈ bind l f :=
mem_bind_iff.2 ⟨a, al, h⟩

/- list subset -/

theorem subset_app_of_subset_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_left _ _

theorem subset_app_of_subset_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_right _ _

theorem cons_subset_of_subset_of_mem {a : α} {l m : list α} (ainm : a ∈ m) (lsubm : l ⊆ m) :
  a::l ⊆ m :=
λ b, or_imp_iff_and_imp.2 ⟨λ e, e.symm ▸ ainm, @lsubm _⟩

theorem app_subset_of_subset_of_subset {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
λ a h, (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

theorem eq_nil_of_subset_nil : ∀ {l : list α}, l ⊆ [] → l = []
| []     s := rfl
| (a::l) s := false.elim $ s $ mem_cons_self a l

/- sublists -/

@[simp] theorem nil_sublist : Π (l : list α), [] <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons _ _ a (nil_sublist l)

@[refl, simp] theorem sublist.refl : Π (l : list α), l <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons2 _ _ a (sublist.refl l)

@[trans] theorem sublist.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
sublist.rec_on h₂ (λ_ s, s)
  (λl₂ l₃ a h₂ IH l₁ h₁, sublist.cons _ _ _ (IH l₁ h₁))
  (λl₂ l₃ a h₂ IH l₁ h₁, @sublist.cases_on _ (λl₁ l₂', l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁
    (λ_, nil_sublist _)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ := sublist.cons _ _ _ (IH _ h₁) end)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ := sublist.cons2 _ _ _ (IH _ h₁) end) rfl)
  l₁ h₁

@[simp] theorem sublist_cons (a : α) (l : list α) : l <+ a::l :=
sublist.cons _ _ _ (sublist.refl l)

theorem sublist_of_cons_sublist {a : α} {l₁ l₂ : list α} : a::l₁ <+ l₂ → l₁ <+ l₂ :=
sublist.trans (sublist_cons a l₁)

theorem cons_sublist_cons {l₁ l₂ : list α} (a : α) (s : l₁ <+ l₂) : a::l₁ <+ a::l₂ :=
sublist.cons2 _ _ _ s

@[simp] theorem sublist_append_left : Π (l₁ l₂ : list α), l₁ <+ l₁++l₂
| []      l₂ := nil_sublist _
| (a::l₁) l₂ := cons_sublist_cons _ (sublist_append_left l₁ l₂)

@[simp] theorem sublist_append_right : Π (l₁ l₂ : list α), l₂ <+ l₁++l₂
| []      l₂ := sublist.refl _
| (a::l₁) l₂ := sublist.cons _ _ _ (sublist_append_right l₁ l₂)

theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : list α} : l₁ <+ l₂ → l₁ <+ a::l₂ :=
sublist.cons _ _ _

theorem sublist_app_of_sublist_left (l l₁ l₂ : list α) (s : l <+ l₁) : l <+ l₁++l₂ :=
s.trans $ sublist_append_left _ _

theorem sublist_app_of_sublist_right (l l₁ l₂ : list α) (s : l <+ l₂) : l <+ l₁++l₂ :=
s.trans $ sublist_append_right _ _

theorem sublist_of_cons_sublist_cons {l₁ l₂ : list α} : ∀ {a : α}, a::l₁ <+ a::l₂ → l₁ <+ l₂
| ._ (sublist.cons  ._ ._ a s) := sublist_of_cons_sublist s
| ._ (sublist.cons2 ._ ._ a s) := s

theorem subset_of_sublist : Π {l₁ l₂ : list α}, l₁ <+ l₂ → l₁ ⊆ l₂
| ._ ._ sublist.slnil             b h := h
| ._ ._ (sublist.cons  l₁ l₂ a s) b h := mem_cons_of_mem _ (subset_of_sublist s h)
| ._ ._ (sublist.cons2 l₁ l₂ a s) b h :=
  match eq_or_mem_of_mem_cons h with
  | or.inl h := h ▸ mem_cons_self _ _
  | or.inr h := mem_cons_of_mem _ (subset_of_sublist s h)
  end

theorem eq_nil_of_sublist_nil {l : list α} (s : l <+ []) : l = [] :=
eq_nil_of_subset_nil $ subset_of_sublist s

theorem eq_nil_of_map_eq_nil {f : α → β} {l :list α} (h : map f l = nil) : l = nil :=
eq_nil_of_length_eq_zero (begin rw [← length_map f l], simp [h] end)

theorem eq_of_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) : b₁ = b₂ :=
let ⟨a, _, e⟩ := exists_of_mem_map h in e.symm

/- index_of -/

section index_of
variable [decidable_eq α]

@[simp] theorem index_of_nil (a : α) : index_of a [] = 0 := rfl

theorem index_of_cons (a b : α) (l : list α) : index_of a (b::l) = if a = b then 0 else succ (index_of a l) := rfl

theorem index_of_cons_eq {a b : α} (l : list α) : a = b → index_of a (b::l) = 0 :=
assume e, if_pos e

@[simp] theorem index_of_cons_self (a : α) (l : list α) : index_of a (a::l) = 0 :=
index_of_cons_eq _ rfl

@[simp] theorem index_of_cons_ne {a b : α} (l : list α) : a ≠ b → index_of a (b::l) = succ (index_of a l) :=
assume n, if_neg n

theorem index_of_eq_length {a : α} {l : list α} : index_of a l = length l ↔ a ∉ l :=
begin
  induction l with b l ih; simp [not_or_iff, -add_comm],
  by_cases a = b with h; simp [h, -add_comm],
  { intro, contradiction },
  { rw ← ih, exact ⟨succ_inj, congr_arg _⟩ }
end

@[simp] theorem index_of_of_not_mem {l : list α} {a : α} : a ∉ l → index_of a l = length l :=
index_of_eq_length.2

theorem index_of_le_length {a : α} {l : list α} : index_of a l ≤ length l :=
begin
  induction l with b l ih; simp [-add_comm, index_of_cons],
  by_cases a = b with h; simp [h, -add_comm, zero_le],
  exact succ_le_succ ih
end

theorem index_of_lt_length {a} {l : list α} : index_of a l < length l ↔ a ∈ l :=
⟨λh, by_contradiction $ λ al, ne_of_lt h $ index_of_eq_length.2 al,
λal, lt_of_le_of_ne index_of_le_length $ λ h, index_of_eq_length.1 h al⟩

end index_of

/- nth element -/
theorem nth_le_nth : Π (l : list α) (n h), nth l n = some (nth_le l n h)
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := rfl
| (a :: l) (n+1) h := nth_le_nth l n _

theorem nth_ge_len : Π (l : list α) (n), n ≥ length l → nth l n = none
| []       n     h := rfl
| (a :: l) 0     h := absurd h (not_lt_zero _)
| (a :: l) (n+1) h := nth_ge_len l n (le_of_succ_le_succ h)

theorem ext : Π {l₁ l₂ : list α}, (∀n, nth l₁ n = nth l₂ n) → l₁ = l₂
| []      []       h := rfl
| (a::l₁) []       h := by have h0 := h 0; contradiction
| []      (a'::l₂) h := by have h0 := h 0; contradiction
| (a::l₁) (a'::l₂) h := by have h0 : some a = some a' := h 0; injection h0 with aa; simp [*, ext (λn, h (n+1))]

theorem ext_le {l₁ l₂ : list α} (hl : length l₁ = length l₂) (h : ∀n h₁ h₂, nth_le l₁ n h₁ = nth_le l₂ n h₂) : l₁ = l₂ :=
ext $ λn, if h₁ : n < length l₁
  then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa [← hl])]
  else let h₁ := le_of_not_gt h₁ in by rw [nth_ge_len _ _ h₁, nth_ge_len _ _ (by rwa [← hl])]

@[simp] theorem index_of_nth_le [decidable_eq α] {a : α} : ∀ {l : list α} h, nth_le l (index_of a l) h = a
| (b::l) h := by by_cases a = b with h'; simp *

@[simp] theorem index_of_nth [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) : nth l (index_of a l) = some a :=
by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]

theorem nth_le_reverse_aux1 : Π (l r : list α) (i h1 h2), nth_le (reverse_core l r) (i + length l) h1 = nth_le r i h2
| []       r i := λh1 h2, rfl
| (a :: l) r i := by rw (show i + length (a :: l) = i + 1 + length l, by simp); exact
  λh1 h2, nth_le_reverse_aux1 l (a :: r) (i+1) h1 (succ_lt_succ h2)

theorem nth_le_reverse_aux2 : Π (l r : list α) (i : nat) (h1) (h2),
  nth_le (reverse_core l r) (length l - 1 - i) h1 = nth_le l i h2
| []       r i     h1 h2 := absurd h2 (not_lt_zero _)
| (a :: l) r 0     h1 h2 := begin
    have aux := nth_le_reverse_aux1 l (a :: r) 0,
    rw zero_add at aux,
    exact aux _ (zero_lt_succ _)
  end
| (a :: l) r (i+1) h1 h2 := begin
    have aux := nth_le_reverse_aux2 l (a :: r) i,
    have heq := calc length (a :: l) - 1 - (i + 1)
          = length l - (1 + i) : by rw add_comm; refl
      ... = length l - 1 - i   : by rw nat.sub_sub,
    rw [← heq] at aux,
    apply aux
  end

@[simp] theorem nth_le_reverse (l : list α) (i : nat) (h1 h2) :
  nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2 :=
nth_le_reverse_aux2 _ _ _ _ _

def to_array (l : list α) : array α l.length :=
{data := λ v, l.nth_le v.1 v.2}

def inth [h : inhabited α] (l : list α) (n : nat) : α := (nth l n).iget
attribute [simp] inth

/- take, drop -/
@[simp] theorem take_zero : ∀ (l : list α), take 0 l = [] :=
begin intros, reflexivity end

@[simp] theorem take_nil : ∀ n, take n [] = ([] : list α)
| 0     := rfl
| (n+1) := rfl

theorem take_cons (n) (a : α) (l : list α) : take (succ n) (a::l) = a :: take n l := rfl

theorem take_all : ∀ (l : list α), take (length l) l = l
| []     := rfl
| (a::l) := begin change a :: (take (length l) l) = a :: l, rw take_all end

theorem take_all_of_ge : ∀ {n} {l : list α}, n ≥ length l → take n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt (zero_lt_succ _))
| (n+1) []     h := rfl
| (n+1) (a::l) h :=
  begin
    change a :: take n l = a :: l,
    rw [take_all_of_ge (le_of_succ_le_succ h)]
  end

theorem take_take : ∀ (n m) (l : list α), take n (take m l) = take (min n m) l
| n         0        l      := by rw [min_zero, take_zero, take_nil]
| 0         m        l      := by simp
| (succ n)  (succ m) nil    := by simp
| (succ n)  (succ m) (a::l) := by simp [min_succ_succ, take_take]

/- take_while -/

def take_while (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: take_while l else []

/- find -/

def find (p : α → Prop) [decidable_pred p] : list α → option α
| []     := none
| (a::l) := if p a then some a else find l

def find_indexes_aux (p : α → Prop) [decidable_pred p] : list α → nat → list nat
| []     n := []
| (a::l) n := let t := find_indexes_aux l (succ n) in if p a then n :: t else t

def find_indexes (p : α → Prop) [decidable_pred p] (l : list α) : list nat :=
find_indexes_aux p l 0

def indexes_of [decidable_eq α] (a : α) : list α → list nat := find_indexes (eq a)

/- foldl, foldr, scanl, scanr -/

attribute [simp] foldl foldr

@[simp] lemma foldr_eta : ∀ (l : list α), foldr cons [] l = l
| []     := rfl
| (x::l) := by simp [foldr_eta l]

def scanl (f : α → β → α) : α → list β → list α
| a []     := [a]
| a (b::l) := a :: scanl (f a b) l

def scanr_aux (f : α → β → β) (b : β) : list α → β × list β
| []     := (b, [])
| (a::l) := let (b', l') := scanr_aux l in (f a b', b' :: l')

def scanr (f : α → β → β) (b : β) (l : list α) : list β :=
let (b', l') := scanr_aux f b l in b' :: l'

@[simp] lemma scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] := rfl

@[simp] lemma scanr_aux_cons (f : α → β → β) (b : β) : ∀ (a : α) (l : list α),
  scanr_aux f b (a::l) = (foldr f b (a::l), scanr f b l)
| a []     := rfl
| a (x::l) := let t := scanr_aux_cons x l in
  by simp [scanr, scanr_aux] at t; simp [scanr, scanr_aux, t]

@[simp] lemma scanr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  scanr f b (a::l) = foldr f b (a::l) :: scanr f b l :=
by simp [scanr]

/- sum -/

def sum [has_add α] [has_zero α] : list α → α :=
foldl (+) 0

/- filter -/

@[simp] theorem filter_subset {p : α → Prop} [h : decidable_pred p] (l : list α) : filter p l ⊆ l :=
subset_of_sublist $ filter_sublist l

theorem of_mem_filter {p : α → Prop} [h : decidable_pred p] {a : α} : ∀ {l}, a ∈ filter p l → p a
| []     ain := absurd ain (not_mem_nil a)
| (b::l) ain :=
  if pb : p b then
    have a ∈ b :: filter p l, begin simp [pb] at ain, assumption end,
    or.elim (eq_or_mem_of_mem_cons this)
      (assume : a = b, begin rw [← this] at pb, exact pb end)
      (assume : a ∈ filter p l, of_mem_filter this)
  else
    begin simp [pb] at ain, exact (of_mem_filter ain) end

theorem mem_of_mem_filter {p : α → Prop} [h : decidable_pred p] {a : α}
  {l} (h : a ∈ filter p l) : a ∈ l :=
filter_subset l h

theorem mem_filter_of_mem {p : α → Prop} [h : decidable_pred p] {a : α} :
  ∀ {l}, a ∈ l → p a → a ∈ filter p l
| []     ain pa := absurd ain (not_mem_nil a)
| (b::l) ain pa :=
  if pb : p b then
    or.elim (eq_or_mem_of_mem_cons ain)
      (assume : a = b, by simp [pb, this])
      (assume : a ∈ l, begin simp [pb], exact (mem_cons_of_mem _ (mem_filter_of_mem this pa)) end)
  else
    or.elim (eq_or_mem_of_mem_cons ain)
      (assume : a = b, begin simp [this] at pa, contradiction end) --absurd (this ▸ pa) pb)
      (assume : a ∈ l, by simp [pa, pb, mem_filter_of_mem this])

@[simp] lemma span_eq_take_drop (p : α → Prop) [decidable_pred p] : ∀ (l : list α), span p l = (take_while p l, drop_while p l)
| []     := rfl
| (a::l) := by by_cases p a with pa; simp [span, take_while, drop_while, pa, span_eq_take_drop l]

@[simp] lemma take_while_append_drop (p : α → Prop) [decidable_pred p] : ∀ (l : list α), take_while p l ++ drop_while p l = l
| []     := rfl
| (a::l) := by by_cases p a with pa; simp [take_while, drop_while, pa, take_while_append_drop l]

/- count -/

section count
variable [decidable_eq α]

def count (a : α) : list α → nat
| []      := 0
| (x::xs) := if a = x then succ (count xs) else count xs

@[simp] theorem count_nil (a : α) : count a [] = 0 := rfl

theorem count_cons (a b : α) (l : list α) :
  count a (b :: l) = if a = b then succ (count a l) else count a l := rfl

theorem count_cons' (a b : α) (l : list α) :
  count a (b :: l) = count a l + (if a = b then 1 else 0) :=
decidable.by_cases
  (assume : a = b, begin rw [count_cons, if_pos this, if_pos this] end)
  (assume : a ≠ b, begin rw [count_cons, if_neg this, if_neg this], reflexivity end)


@[simp] theorem count_cons_self (a : α) (l : list α) : count a (a::l) = succ (count a l) :=
if_pos rfl

@[simp] theorem count_cons_of_ne {a b : α} (h : a ≠ b) (l : list α) : count a (b::l) = count a l :=
if_neg h

theorem count_cons_ge_count (a b : α) (l : list α) : count a (b :: l) ≥ count a l :=
decidable.by_cases
  (assume : a = b, begin subst b, rw count_cons_self, apply le_succ end)
  (assume : a ≠ b, begin rw (count_cons_of_ne this), apply le_refl end)

-- TODO(Jeremy): without the reflexivity, this yields the goal "1 = 1". the first is from has_one,
-- the second is succ 0. Make sure the simplifier can eventually handle this.

theorem count_singleton (a : α) : count a [a] = 1 :=
by simp

@[simp] theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂
| []      l₂ := begin rw [nil_append, count_nil, zero_add] end
| (b::l₁) l₂ := decidable.by_cases
  (assume : a = b, by rw [←this, cons_append, count_cons_self, count_cons_self, succ_add,
                         count_append])
  (assume : a ≠ b, by rw [cons_append, count_cons_of_ne this, count_cons_of_ne this, count_append])

@[simp] theorem count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
by rw [concat_eq_append, count_append, count_singleton]

theorem mem_of_count_pos : ∀ {a : α} {l : list α}, count a l > 0 → a ∈ l
| a []     h := absurd h (lt_irrefl _)
| a (b::l) h := decidable.by_cases
  (assume : a = b, begin subst b, apply mem_cons_self end)
  (assume : a ≠ b,
   have count a l > 0, begin rw [count_cons_of_ne this] at h, exact h end,
   have a ∈ l,    from mem_of_count_pos this,
   show a ∈ b::l, from mem_cons_of_mem _ this)

theorem count_pos_of_mem : ∀ {a : α} {l : list α}, a ∈ l → count a l > 0
| a []     h := absurd h (not_mem_nil _)
| a (b::l) h := or.elim h
  (assume : a = b, begin subst b, rw count_cons_self, apply zero_lt_succ end)
  (assume : a ∈ l, calc
   count a (b::l) ≥ count a l : count_cons_ge_count _ _ _
           ...    > 0         : count_pos_of_mem this)

theorem mem_iff_count_pos (a : α) (l : list α) : a ∈ l ↔ count a l > 0 :=
iff.intro count_pos_of_mem mem_of_count_pos

@[simp] theorem count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
have ∀ n, count a l = n → count a l = 0,
  begin
    intro n, cases n,
     { intro this, exact this },
    intro this, exact absurd (mem_of_count_pos (begin rw this, exact dec_trivial end)) h
  end,
this (count a l) rfl

theorem not_mem_of_count_eq_zero {a : α} {l : list α} (h : count a l = 0) : a ∉ l :=
assume : a ∈ l,
have count a l > 0, from count_pos_of_mem this,
show false, begin rw h at this, exact nat.not_lt_zero _ this end

end count

/- prefix, suffix, infix -/

def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂
def is_suffix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, t ++ l₁ = l₂
def is_infix (l₁ : list α) (l₂ : list α) : Prop := ∃ s t, s ++ l₁ ++ t = l₂

infix ` <+: `:50 := is_prefix
infix ` <:+ `:50 := is_suffix
infix ` <:+: `:50 := is_infix

lemma prefix_append (l₁ l₂ : list α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩

lemma suffix_append (l₁ l₂ : list α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

lemma infix_append (l₁ l₂ l₃ : list α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

lemma prefix_refl (l : list α) : l <+: l := ⟨[], append_nil _⟩

lemma suffix_refl (l : list α) : l <:+ l := ⟨[], rfl⟩

lemma infix_of_prefix {l₁ l₂ : list α} : l₁ <+: l₂ → l₁ <:+: l₂ :=
λ⟨t, h⟩, ⟨[], t, h⟩

lemma infix_of_suffix {l₁ l₂ : list α} : l₁ <:+ l₂ → l₁ <:+: l₂ :=
λ⟨t, h⟩, ⟨t, [], by simp [h]⟩

lemma infix_refl (l : list α) : l <:+: l := infix_of_prefix $ prefix_refl l

lemma sublist_of_infix {l₁ l₂ : list α} : l₁ <:+: l₂ → l₁ <+ l₂ :=
λ⟨s, t, h⟩, by rw [← h]; exact (sublist_append_right _ _).trans (sublist_append_left _ _)

lemma length_le_of_infix {l₁ l₂ : list α} (s : l₁ <:+: l₂) : length l₁ ≤ length l₂ :=
length_le_of_sublist $ sublist_of_infix s

lemma eq_nil_of_infix_nil {l : list α} (s : l <:+: []) : l = [] :=
eq_nil_of_sublist_nil $ sublist_of_infix s

lemma eq_nil_of_prefix_nil {l : list α} (s : l <+: []) : l = [] :=
eq_nil_of_infix_nil $ infix_of_prefix s

lemma eq_nil_of_suffix_nil {l : list α} (s : l <:+ []) : l = [] :=
eq_nil_of_infix_nil $ infix_of_suffix s

lemma infix_iff_prefix_suffix (l₁ l₂ : list α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
⟨λ⟨s, t, e⟩, ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc]; exact ⟨_, rfl⟩⟩,
λ⟨._, ⟨t, rfl⟩, ⟨s, e⟩⟩, ⟨s, t, by rw append_assoc; exact e⟩⟩

def inits : list α → list (list α)
| []     := [[]]
| (a::l) := [] :: map (λt, a::t) (inits l)
attribute [simp] inits

local infixr :: := list.cons -- temporary hack to fix overload issue

@[simp] lemma mem_inits : ∀ (s t : list α), s ∈ inits t ↔ s <+: t
| s []     := by simp; exact ⟨λh, by rw h; exact prefix_refl [], eq_nil_of_prefix_nil⟩
| s (a::t) := by simp; exact ⟨λo, match s, o with
  | ._, or.inl rfl := ⟨_, rfl⟩
  | s, or.inr mm := let ⟨r, hr, hs⟩ := exists_of_mem_map mm, ⟨s, ht⟩ := (mem_inits _ _).1 hr in
    by rw [← hs, ← ht]; exact ⟨s, rfl⟩
  end, λmi, match s, mi with
  | [], ⟨._, rfl⟩ := or.inl rfl
  | (b::s), ⟨r, hr⟩ := list.no_confusion hr $ λba st, or.inr $
    by rw ba; exact mem_map _ ((mem_inits _ _).2 ⟨_, st⟩)
  end⟩

def tails : list α → list (list α)
| []     := [[]]
| (a::l) := (a::l) :: tails l
attribute [simp] tails

@[simp] lemma mem_tails : ∀ (s t : list α), s ∈ tails t ↔ s <:+ t
| s []     := by simp; exact ⟨λh, by rw h; exact suffix_refl [], eq_nil_of_suffix_nil⟩
| s (a::t) := by simp [mem_tails s t]; exact show s <:+ t ∨ s = a :: t ↔ s <:+ a :: t, from
  ⟨λo, match s, t, o with
  | s, ._, or.inl ⟨l, rfl⟩ := ⟨a::l, rfl⟩
  | ._, t, or.inr rfl := suffix_refl _
  end, λe, match s, t, e with
  | ._, t, ⟨[], rfl⟩ := or.inr rfl
  | s, t, ⟨b::l, he⟩ := list.no_confusion he (λab lt, or.inl ⟨l, lt⟩)
  end⟩

def sublists_aux : list α → (list α → list β → list β) → list β
| []     f := []
| (a::l) f := f [a] (sublists_aux l (λys r, f ys (f (a :: ys) r)))

def sublists (l : list α) : list (list α) :=
[] :: sublists_aux l cons

lemma sublists_aux_eq_foldl : ∀ (l : list α) {β : Type u} (f : list α → list β → list β),
  sublists_aux l f = foldr f [] (sublists_aux l cons)
| []     β f := rfl
| (a::l) β f := suffices ∀ t, foldr (λ ys r, f ys (f (a :: ys) r)) [] t =
                         foldr f [] (t.foldr (λ ys r, ys :: (a :: ys) :: r) nil),
by simp [sublists_aux]; rw [sublists_aux_eq_foldl l, sublists_aux_eq_foldl l (λ ys r, ys :: (a :: ys) :: r), this],
λt, by induction t; simp; simp [ih_1]


lemma sublists_aux_cons_cons (l : list α) (a : α) :
  sublists_aux (a::l) cons = [a] :: foldr (λys r, ys :: (a :: ys) :: r) [] (sublists_aux l cons) :=
by rw [← sublists_aux_eq_foldl]; refl

@[simp] lemma mem_sublists (s t : list α) : s ∈ sublists t ↔ s <+ t :=
by simp [sublists]; exact
⟨λm, let good := λ (l : list (list α)), ∀ s ∈ l, s <+ t in
  suffices ∀ l (f : list α → list (list α) → list (list α)),
    (∀ {x y}, x <+ l → good y → good (f x y)) → l <+ t → good (sublists_aux l f), from
    or.elim m (λe, by rw e; apply nil_sublist)
      (this t cons (λ x y hx hy s m, by exact or.elim m (λe, by rw e; exact hx) (hy s)) (sublist.refl _) s),
  begin
    intro l; induction l with a l IH; intros f al sl x m,
    exact false.elim m,
    refine al (cons_sublist_cons a (nil_sublist _)) _ _ m,
    exact λs hs, IH _ (λx y hx hy, al (sublist_cons_of_sublist _ hx) (al (cons_sublist_cons _ hx) hy))
      (sublist_of_cons_sublist sl) _ hs
  end,
λsl, begin
  have this : ∀ {a : α} {y t}, y ∈ t → y ∈ foldr (λ ys r, ys :: (a :: ys) :: r) nil t
                                  ∧ a :: y ∈ foldr (λ ys r, ys :: (a :: ys) :: r) nil t,
  { intros a y t yt, induction t with x t IH, exact absurd yt (not_mem_nil _),
    simp, simp at yt, cases yt with yx yt,
    { rw yx, exact ⟨or.inl rfl, or.inr $ or.inl rfl⟩ },
    { cases IH yt with h1 h2,
      exact ⟨or.inr $ or.inr h1, or.inr $ or.inr h2⟩ } },
  induction sl with l₁ l₂ a sl IH l₁ l₂ a sl IH, exact or.inl rfl,
  { refine or.imp_right (λh, _) IH,
    rw sublists_aux_cons_cons,
    exact mem_cons_of_mem _ (this h).left },
  { refine or.inr _,
    rw sublists_aux_cons_cons, simp,
    refine or.imp (λ(h : l₁ = []), by rw h) (λh, _) IH,
    exact (this h).right },
end⟩

instance decidable_prefix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+: l₂)
| []      l₂ := is_true ⟨l₂, rfl⟩
| (a::l₁) [] := is_false $ λ⟨t, te⟩, list.no_confusion te
| (a::l₁) (b::l₂) :=
  if h : a = b then
    decidable_of_decidable_of_iff (decidable_prefix l₁ l₂) $ by rw [← h]; exact
      ⟨λ⟨t, te⟩, ⟨t, by rw [← te]; refl⟩,
       λ⟨t, te⟩, list.no_confusion te (λ_ te, ⟨t, te⟩)⟩
  else
    is_false $ λ⟨t, te⟩, list.no_confusion te $ λh', absurd h' h

-- Alternatively, use mem_tails
instance decidable_suffix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+ l₂)
| []      l₂ := is_true ⟨l₂, append_nil _⟩
| (a::l₁) [] := is_false $ λ⟨t, te⟩, absurd te $
                append_ne_nil_of_ne_nil_right _ _ $ λh, list.no_confusion h
| l₁      l₂ := let len1 := length l₁, len2 := length l₂ in
  if hl : len1 ≤ len2 then
    if he : drop (len2 - len1) l₂ = l₁ then is_true $
      ⟨take (len2 - len1) l₂, by rw [← he, take_append_drop]⟩
    else is_false $
      suffices length l₁ ≤ length l₂ → l₁ <:+ l₂ → drop (length l₂ - length l₁) l₂ = l₁,
        from λsuf, he (this hl suf),
      λ hl ⟨t, te⟩, and.right $
        append_right_inj (eq.trans (take_append_drop (length l₂ - length l₁) l₂) te.symm) $
        by simp; exact nat.sub_sub_self hl
  else is_false $ λ⟨t, te⟩, hl $
    show length l₁ ≤ length l₂, by rw [← te, length_append]; apply nat.le_add_left

instance decidable_infix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+: l₂)
| []      l₂ := is_true ⟨[], l₂, rfl⟩
| (a::l₁) [] := is_false $ λ⟨s, t, te⟩, absurd te $ append_ne_nil_of_ne_nil_left _ _ $
                append_ne_nil_of_ne_nil_right _ _ $ λh, list.no_confusion h
| l₁      l₂ := decidable_of_decidable_of_iff (list.decidable_bex (λt, l₁ <+: t) (tails l₂)) $
  by refine (exists_congr (λt, _)).trans (infix_iff_prefix_suffix _ _).symm;
     exact ⟨λ⟨h1, h2⟩, ⟨h2, (mem_tails _ _).1 h1⟩, λ⟨h2, h1⟩, ⟨(mem_tails _ _).2 h1, h2⟩⟩

instance decidable_sublist [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+ l₂)
| []      l₂      := is_true $ nil_sublist _
| (a::l₁) []      := is_false $ λh, list.no_confusion $ eq_nil_of_sublist_nil h
| (a::l₁) (b::l₂) :=
  if h : a = b then
    decidable_of_decidable_of_iff (decidable_sublist l₁ l₂) $
      by rw [← h]; exact ⟨cons_sublist_cons _, sublist_of_cons_sublist_cons⟩
  else decidable_of_decidable_of_iff (decidable_sublist (a::l₁) l₂)
    ⟨sublist_cons_of_sublist _, λs, match a, l₁, s, h with
    | a, l₁, sublist.cons ._ ._ ._ s', h := s'
    | ._, ._, sublist.cons2 t ._ ._ s', h := absurd rfl h
    end⟩

/- transpose -/

def transpose_aux : list α → list (list α) → list (list α)
| []     ls      := ls
| (a::i) []      := [a] :: transpose_aux i []
| (a::i) (l::ls) := (a::l) :: transpose_aux i ls

def transpose : list (list α) → list (list α)
| []      := []
| (l::ls) := transpose_aux l (transpose ls)

/- permutations -/

def permutations_aux2 (t : α) (ts : list α) : list α → (list α → β) → list β → list α × list β
| []      f r := (ts, r)
| (y::ys) f r := let (us, zs) := permutations_aux2 ys (λx : list α, f (y::x)) r in
                (y :: us, f (t :: y :: us) :: zs)

private def meas : list α × list α → ℕ × ℕ | (l, i) := (length l + length i, length l)

local infix ` ≺ `:50 := inv_image (prod.lex (<) (<)) meas

def permutations_aux.F : Π (x : list α × list α), (Π (y : list α × list α), y ≺ x → list (list α)) → list (list α)
| ([],    is) IH := []
| (t::ts, is) IH :=
have h1 : (ts, t :: is) ≺ (t :: ts, is), from
  show prod.lex _ _ (succ (length ts + length is), length ts) (succ (length ts) + length is, length (t :: ts)),
  by rw nat.succ_add; exact prod.lex.right _ _ (lt_succ_self _),
have h2 : (is, []) ≺ (t :: ts, is), from prod.lex.left _ _ _ (lt_add_of_pos_left _ (succ_pos _)),
foldr (λy r, (permutations_aux2 t ts y id r).2) (IH (ts, t::is) h1) (is :: IH (is, []) h2)

def permutations_aux : list α × list α → list (list α) :=
well_founded.fix (inv_image.wf meas (prod.lex_wf lt_wf lt_wf)) permutations_aux.F

def permutations (l : list α) : list (list α) :=
l :: permutations_aux (l, [])

def permutations_aux.eqn_1 (is : list α) : permutations_aux ([], is) = [] :=
well_founded.fix_eq _ _ _

def permutations_aux.eqn_2 (t : α) (ts is) : permutations_aux (t::ts, is) =
  foldr (λy r, (permutations_aux2 t ts y id r).2) (permutations_aux (ts, t::is)) (permutations is) :=
well_founded.fix_eq _ _ _

end list
