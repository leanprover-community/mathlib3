/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

Basic properties of lists.
-/
import logic.basic data.nat.basic data.option data.bool
       tactic.interactive algebra.group
open function nat

namespace list
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

@[simp] theorem cons_ne_nil (a : α) (l : list α) : a::l ≠ [].

theorem head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

theorem tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

theorem cons_inj {a : α} : injective (cons a) :=
assume l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

@[simp] theorem cons_inj' (a : α) {l l' : list α} : a::l = a::l' ↔ l = l' :=
⟨λ e, cons_inj e, congr_arg _⟩

/- mem -/

theorem eq_nil_of_forall_not_mem : ∀ {l : list α}, (∀ a, a ∉ l) → l = nil
| []        := assume h, rfl
| (b :: l') := assume h, absurd (mem_cons_self b l') (h b)

theorem mem_singleton_self (a : α) : a ∈ [a] := mem_cons_self _ _

theorem eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b :=
assume : a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (assume : a = b, this)
  (assume : a ∈ [], absurd this (not_mem_nil a))

@[simp] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
⟨eq_of_mem_singleton, by intro h; simp [h]⟩

theorem mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (assume : a = b, begin subst a, exact binl end)
  (assume : a ∈ l, this)

theorem not_mem_append {a : α} {s t : list α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
mt mem_append.1 $ not_or_distrib.2 ⟨h₁, h₂⟩

theorem length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| (b::l) _ := zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : list α}, 0 < length l → ∃ a, a ∈ l
| (b::l) _ := ⟨b, mem_cons_self _ _⟩

theorem mem_split {a : α} {l : list α} (h : a ∈ l) : ∃ s t : list α, l = s ++ a :: t :=
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

theorem mem_map_of_mem (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l with b l' ih,
  {simp at h, contradiction },
  {simp, simp at h, cases h with h h,
    {simp *},
    {exact or.inr (ih h)}}
end

theorem exists_of_mem_map {f : α → β} {b : β} {l : list α} (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  {simp at h, contradiction},
  {cases (eq_or_mem_of_mem_cons h) with h h,
    {existsi c, simp [h]},
    {cases ih h with a ha, cases ha with ha₁ ha₂,
      existsi a, simp * }}
end

@[simp] theorem mem_map {f : α → β} {b : β} {l : list α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
⟨exists_of_mem_map, λ ⟨a, la, h⟩, by rw [← h]; exact mem_map_of_mem f la⟩

@[simp] theorem mem_map_of_inj {f : α → β} (H : injective f) {a : α} {l : list α} :
  f a ∈ map f l ↔ a ∈ l :=
⟨λ m, let ⟨a', m', e⟩ := exists_of_mem_map m in H e ▸ m', mem_map_of_mem _⟩

@[simp] theorem mem_join {a : α} : ∀ {L : list (list α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l
| []       := ⟨false.elim, λ⟨_, h, _⟩, false.elim h⟩
| (c :: L) := by simp [join, @mem_join L]; exact
  ⟨λh, match h with
  | or.inl ac         := ⟨c, ac, or.inl rfl⟩
  | or.inr ⟨l, al, lL⟩ := ⟨l, al, or.inr lL⟩
  end,
  λ⟨l, al, o⟩, o.elim (λ lc, by rw lc at al; exact or.inl al) (λlL, or.inr ⟨l, al, lL⟩)⟩

theorem exists_of_mem_join {a : α} {L : list (list α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
mem_join.1

theorem mem_join_of_mem {a : α} {L : list (list α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
mem_join.2 ⟨l, lL, al⟩

@[simp] theorem mem_bind {b : β} {l : list α} {f : α → list β} : b ∈ bind l f ↔ ∃ a ∈ l, b ∈ f a :=
iff.trans mem_join
  ⟨λ ⟨l', h1, h2⟩, let ⟨a, al, fa⟩ := exists_of_mem_map h1 in ⟨a, al, fa.symm ▸ h2⟩,
  λ ⟨a, al, bfa⟩, ⟨f a, mem_map_of_mem _ al, bfa⟩⟩

theorem exists_of_mem_bind {b : β} {l : list α} {f : α → list β} : b ∈ bind l f → ∃ a ∈ l, b ∈ f a :=
mem_bind.1

theorem mem_bind_of_mem {b : β} {l : list α} {f : α → list β} {a} (al : a ∈ l) (h : b ∈ f a) : b ∈ bind l f :=
mem_bind.2 ⟨a, al, h⟩

/- list subset -/

theorem subset_app_of_subset_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_left _ _

theorem subset_app_of_subset_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_right _ _

theorem cons_subset_of_subset_of_mem {a : α} {l m : list α} (ainm : a ∈ m) (lsubm : l ⊆ m) :
  a::l ⊆ m :=
λ b, or_imp_distrib.2 ⟨λ e, e.symm ▸ ainm, @lsubm _⟩

theorem app_subset_of_subset_of_subset {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
λ a h, (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

theorem eq_nil_of_subset_nil : ∀ {l : list α}, l ⊆ [] → l = []
| []     s := rfl
| (a::l) s := false.elim $ s $ mem_cons_self a l

theorem eq_nil_iff_forall_not_mem {l : list α} : l = [] ↔ ∀ a, a ∉ l :=
show l = [] ↔ l ⊆ [], from ⟨λ e, e ▸ subset.refl _, eq_nil_of_subset_nil⟩

/- append -/

theorem append_ne_nil_of_ne_nil_left (s t : list α) : s ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

theorem append_ne_nil_of_ne_nil_right (s t : list α) : t ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

theorem append_foldl (f : α → β → α) (a : α) (s t : list β) : foldl f a (s ++ t) = foldl f (foldl f a s) t :=
by {induction s with b s H generalizing a, refl, simp [foldl], rw H _}

theorem append_foldr (f : α → β → β) (a : β) (s t : list α) : foldr f a (s ++ t) = foldr f (foldr f a t) s :=
by {induction s with b s H generalizing a, refl, simp [foldr], rw H _}

/- join -/

attribute [simp] join

@[simp] theorem join_append (L₁ L₂ : list (list α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ :=
by induction L₁; simp *

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

theorem append_inj' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
append_inj h $ @nat.add_right_cancel _ (length t₁) _ $
let hap := congr_arg length h in by simp at hap; rwa [← hl] at hap

theorem append_inj_left' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
(append_inj' h hl).left

theorem append_inj_right' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
(append_inj' h hl).right

theorem append_left_cancel {s₁ s₂ t : list α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
append_inj_left' h rfl

theorem append_right_cancel {s t₁ t₂ : list α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
append_inj_right h rfl

theorem eq_of_mem_repeat {a b : α} : ∀ {n}, b ∈ repeat a n → b = a
| (n+1) h := or.elim h id $ @eq_of_mem_repeat _

theorem eq_repeat_of_mem {a : α} : ∀ {l : list α}, (∀ b ∈ l, b = a) → l = repeat a l.length
| [] H := rfl
| (b::l) H :=
  have b = a ∧ ∀ (x : α), x ∈ l → x = a,
  by simpa [or_imp_distrib, forall_and_distrib] using H,
  by dsimp; congr; [exact this.1, exact eq_repeat_of_mem this.2]

theorem eq_repeat' {a : α} {l : list α} : l = repeat a l.length ↔ ∀ b ∈ l, b = a :=
⟨λ h, h.symm ▸ λ b, eq_of_mem_repeat, eq_repeat_of_mem⟩

theorem eq_repeat {a : α} {n} {l : list α} : l = repeat a n ↔ length l = n ∧ ∀ b ∈ l, b = a :=
⟨λ h, h.symm ▸ ⟨length_repeat _ _, λ b, eq_of_mem_repeat⟩,
 λ ⟨e, al⟩, e ▸ eq_repeat_of_mem al⟩

theorem repeat_subset_singleton (a : α) (n) : repeat a n ⊆ [a] :=
λ b h, mem_singleton.2 (eq_of_mem_repeat h)

@[simp] theorem map_const {l : list α} {b : β} : map (function.const α b) l = repeat b l.length :=
by induction l; simp [-add_comm, *]

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) : b₁ = b₂ :=
by rw map_const at h; exact eq_of_mem_repeat h

/- concat -/

@[simp] def concat : list α → α → list α
| []     a := [a]
| (b::l) a := b :: concat l a

@[simp] theorem concat_nil (a : α) : concat [] a = [a] := rfl

@[simp] theorem concat_cons (a b : α) (l : list α) : concat (a :: l) b  = a :: concat l b := rfl

@[simp] theorem concat_ne_nil (a : α) (l : list α) : concat l a ≠ [] :=
by induction l; intro h; contradiction

@[simp] theorem concat_append (a : α) (l₁ l₂ : list α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
by induction l₁ with b l₁ ih; [simp, simp [ih]]

@[simp] theorem concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
by induction l; simp [*, concat]

@[simp] theorem length_concat (a : α) (l : list α) : length (concat l a) = succ (length l) :=
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

theorem reverse_cons' (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] :=
by simp

@[simp] theorem reverse_singleton (a : α) : reverse [a] = [a] :=
rfl

@[simp] theorem reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
by induction s; simp *

@[simp] theorem reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; simp *

theorem concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
by simp

@[simp] theorem length_reverse (l : list α) : length (reverse l) = length l :=
by induction l; simp *

@[simp] theorem map_reverse (f : α → β) (l : list α) : map f (reverse l) = reverse (map f l) :=
by induction l; simp *

@[simp] theorem mem_reverse {a : α} {l : list α} : a ∈ reverse l ↔ a ∈ l :=
by induction l; simp *; rw mem_append_eq

/- last -/

@[simp] theorem last_cons {a : α} {l : list α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
by {induction l; intros, contradiction, simp *, reflexivity}

@[simp] theorem last_append {a : α} (l : list α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
begin
  induction l with hd tl ih; rsimp,
  have haux : tl ++ [a] ≠ [],
    {apply append_ne_nil_of_ne_nil_right, contradiction},
  simp *
end

theorem last_concat {a : α} (l : list α) (h : concat l a ≠ []) : last (concat l a) h = a :=
by simp *

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

lemma map_congr {f g : α → β} : ∀ {l : list α}, (∀ x ∈ l, f x = g x) → map f l = map g l
| [] _     := rfl
| (a::l) h :=
  have f a = g a, from h _ (mem_cons_self _ _),
  have map f l = map g l, from map_congr $ assume a', h _ ∘ mem_cons_of_mem _,
  show f a :: map f l = g a :: map g l, by simp [*]

theorem map_concat (f : α → β) (a : α) (l : list α) : map f (concat l a) = concat (map f l) (f a) :=
by induction l; simp *

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : list α) : map f l = l :=
by induction l; simp *

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : list β) : foldl f a (map g l) = foldl (λx y, f x (g y)) a l :=
by revert a; induction l; intros; simp *

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : list β) : foldr f a (map g l) = foldr (f ∘ g) a l :=
by revert a; induction l; intros; simp *

theorem foldl_hom (f : α → β) (g : α → γ → α) (g' : β → γ → β) (a : α)
  (h : ∀a x, f (g a x) = g' (f a) x) (l : list γ) : f (foldl g a l) = foldl g' (f a) l :=
by revert a; induction l; intros; simp *

theorem foldr_hom (f : α → β) (g : γ → α → α) (g' : γ → β → β) (a : α)
  (h : ∀x a, f (g x a) = g' x (f a)) (l : list γ) : f (foldr g a l) = foldr g' (f a) l :=
by revert a; induction l; intros; simp *

theorem eq_nil_of_map_eq_nil {f : α → β} {l : list α} (h : map f l = nil) : l = nil :=
eq_nil_of_length_eq_zero (begin rw [← length_map f l], simp [h] end)

@[simp] theorem map_join (f : α → β) (L : list (list α)) :
  map f (join L) = join (map (map f) L) :=
by induction L; simp *

/- map₂ -/

theorem nil_map₂ (f : α → β → γ) (l : list β) : map₂ f [] l = [] :=
by cases l; refl

theorem map₂_nil (f : α → β → γ) (l : list α) : map₂ f l [] = [] :=
by cases l; refl

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

theorem sublist_app_of_sublist_left {l l₁ l₂ : list α} (s : l <+ l₁) : l <+ l₁++l₂ :=
s.trans $ sublist_append_left _ _

theorem sublist_app_of_sublist_right {l l₁ l₂ : list α} (s : l <+ l₂) : l <+ l₁++l₂ :=
s.trans $ sublist_append_right _ _

theorem sublist_of_cons_sublist_cons {l₁ l₂ : list α} : ∀ {a : α}, a::l₁ <+ a::l₂ → l₁ <+ l₂
| ._ (sublist.cons  ._ ._ a s) := sublist_of_cons_sublist s
| ._ (sublist.cons2 ._ ._ a s) := s

theorem cons_sublist_cons_iff {l₁ l₂ : list α} {a : α} : a::l₁ <+ a::l₂ ↔ l₁ <+ l₂ :=
⟨sublist_of_cons_sublist_cons, cons_sublist_cons _⟩

@[simp] theorem append_sublist_append_left {l₁ l₂ : list α} : ∀ l, l++l₁ <+ l++l₂ ↔ l₁ <+ l₂
| []     := iff.rfl
| (a::l) := cons_sublist_cons_iff.trans (append_sublist_append_left l)

theorem append_sublist_append_of_sublist_right {l₁ l₂ : list α} (h : l₁ <+ l₂) (l) : l₁++l <+ l₂++l :=
by induction h; [refl,
  apply sublist_cons_of_sublist _ ih_1,
  apply cons_sublist_cons _ ih_1]

theorem sublist_or_mem_of_sublist {l l₁ l₂ : list α} {a : α} (h : l <+ l₁ ++ a::l₂) : l <+ l₁ ++ l₂ ∨ a ∈ l :=
begin
  induction l₁ with b l₁ IH generalizing l,
  { cases h; simp * },
  { cases h with _ _ _ h _ _ _ h,
    { exact or.imp_left (sublist_cons_of_sublist _) (IH h) },
    { exact (IH h).imp (cons_sublist_cons _) (mem_cons_of_mem _) } }
end

theorem reverse_sublist {l₁ l₂ : list α} (h : l₁ <+ l₂) : l₁.reverse <+ l₂.reverse :=
by induction h; simp; [
  exact sublist_app_of_sublist_left ih_1,
  exact append_sublist_append_of_sublist_right ih_1 _]

@[simp] theorem reverse_sublist_iff {l₁ l₂ : list α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
⟨λ h, by have := reverse_sublist h; simp at this; assumption, reverse_sublist⟩

@[simp] theorem append_sublist_append_right {l₁ l₂ : list α} (l) : l₁++l <+ l₂++l ↔ l₁ <+ l₂ :=
⟨λ h, by have := reverse_sublist h; simp at this; assumption,
 λ h, append_sublist_append_of_sublist_right h l⟩

theorem subset_of_sublist : Π {l₁ l₂ : list α}, l₁ <+ l₂ → l₁ ⊆ l₂
| ._ ._ sublist.slnil             b h := h
| ._ ._ (sublist.cons  l₁ l₂ a s) b h := mem_cons_of_mem _ (subset_of_sublist s h)
| ._ ._ (sublist.cons2 l₁ l₂ a s) b h :=
  match eq_or_mem_of_mem_cons h with
  | or.inl h := h ▸ mem_cons_self _ _
  | or.inr h := mem_cons_of_mem _ (subset_of_sublist s h)
  end

theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l :=
⟨λ h, subset_of_sublist h (mem_singleton_self _), λ h,
let ⟨s, t, e⟩ := mem_split h in e.symm ▸
  (cons_sublist_cons _ (nil_sublist _)).trans (sublist_append_right _ _)⟩

theorem eq_nil_of_sublist_nil {l : list α} (s : l <+ []) : l = [] :=
eq_nil_of_subset_nil $ subset_of_sublist s

theorem repeat_sublist_repeat (a : α) {m n} : repeat a m <+ repeat a n ↔ m ≤ n :=
⟨λ h, by simpa using length_le_of_sublist h,
 λ h, by induction h; [apply sublist.refl, simp [*, sublist.cons]] ⟩

theorem eq_of_sublist_of_length_eq : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
| ._ ._ sublist.slnil             h := rfl
| ._ ._ (sublist.cons  l₁ l₂ a s) h :=
  absurd (length_le_of_sublist s) $ not_le_of_gt $ by rw h; apply lt_succ_self
| ._ ._ (sublist.cons2 l₁ l₂ a s) h :=
  by rw [length, length] at h; injection h with h; rw eq_of_sublist_of_length_eq s h

theorem sublist_antisymm {l₁ l₂ : list α} (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
eq_of_sublist_of_length_eq s₁ (le_antisymm (length_le_of_sublist s₁) (length_le_of_sublist s₂))

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
  induction l with b l ih; simp [-add_comm],
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

theorem nth_le_of_mem : ∀ {a} {l : list α}, a ∈ l → ∃ n h, nth_le l n h = a
| a (_ :: l) (or.inl rfl) := ⟨0, succ_pos _, rfl⟩
| a (b :: l) (or.inr m)   :=
  let ⟨n, h, e⟩ := nth_le_of_mem m in ⟨n+1, succ_lt_succ h, e⟩

theorem nth_le_nth : ∀ {l : list α} {n} h, nth l n = some (nth_le l n h)
| (a :: l) 0     h := rfl
| (a :: l) (n+1) h := @nth_le_nth l n _

theorem nth_ge_len : ∀ {l : list α} {n}, n ≥ length l → nth l n = none
| []       n     h := rfl
| (a :: l) (n+1) h := nth_ge_len (le_of_succ_le_succ h)

theorem nth_eq_some {l : list α} {n a} : nth l n = some a ↔ ∃ h, nth_le l n h = a :=
⟨λ e,
  have h : n < length l, from lt_of_not_ge $ λ hn,
    by rw nth_ge_len hn at e; contradiction,
  ⟨h, by rw nth_le_nth h at e;
    injection e with e; apply nth_le_mem⟩,
λ ⟨h, e⟩, e ▸ nth_le_nth _⟩

theorem nth_of_mem {a} {l : list α} (h : a ∈ l) : ∃ n, nth l n = some a :=
let ⟨n, h, e⟩ := nth_le_of_mem h in ⟨n, by rw [nth_le_nth, e]⟩

theorem nth_le_mem : ∀ (l : list α) n h, nth_le l n h ∈ l
| (a :: l) 0     h := mem_cons_self _ _
| (a :: l) (n+1) h := mem_cons_of_mem _ (nth_le_mem _ _ _)

theorem nth_mem {l : list α} {n a} (e : nth l n = some a) : a ∈ l :=
let ⟨h, e⟩ := nth_eq_some.1 e in e ▸ nth_le_mem _ _ _

theorem mem_iff_nth_le {a} {l : list α} : a ∈ l ↔ ∃ n h, nth_le l n h = a :=
⟨nth_le_of_mem, λ ⟨n, h, e⟩, e ▸ nth_le_mem _ _ _⟩

theorem mem_iff_nth {a} {l : list α} : a ∈ l ↔ ∃ n, nth l n = some a :=
mem_iff_nth_le.trans $ exists_congr $ λ n, nth_eq_some.symm

theorem ext : ∀ {l₁ l₂ : list α}, (∀n, nth l₁ n = nth l₂ n) → l₁ = l₂
| []      []       h := rfl
| (a::l₁) []       h := by have h0 := h 0; contradiction
| []      (a'::l₂) h := by have h0 := h 0; contradiction
| (a::l₁) (a'::l₂) h := by have h0 : some a = some a' := h 0; injection h0 with aa; simp [*, ext (λn, h (n+1))]

theorem ext_le {l₁ l₂ : list α} (hl : length l₁ = length l₂) (h : ∀n h₁ h₂, nth_le l₁ n h₁ = nth_le l₂ n h₂) : l₁ = l₂ :=
ext $ λn, if h₁ : n < length l₁
  then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa [← hl])]
  else let h₁ := le_of_not_gt h₁ in by rw [nth_ge_len h₁, nth_ge_len (by rwa [← hl])]

@[simp] theorem index_of_nth_le [decidable_eq α] {a : α} : ∀ {l : list α} h, nth_le l (index_of a l) h = a
| (b::l) h := by by_cases a = b with h'; simp *

@[simp] theorem index_of_nth [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) : nth l (index_of a l) = some a :=
by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]

theorem nth_le_reverse_aux1 : ∀ (l r : list α) (i h1 h2), nth_le (reverse_core l r) (i + length l) h1 = nth_le r i h2
| []       r i := λh1 h2, rfl
| (a :: l) r i := by rw (show i + length (a :: l) = i + 1 + length l, by simp); exact
  λh1 h2, nth_le_reverse_aux1 l (a :: r) (i+1) h1 (succ_lt_succ h2)

theorem nth_le_reverse_aux2 : ∀ (l r : list α) (i : nat) (h1) (h2),
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

def to_array (l : list α) : array l.length α :=
{data := λ v, l.nth_le v.1 v.2}

@[simp] def inth [h : inhabited α] (l : list α) (n : nat) : α := (nth l n).iget

/- nth tail operation -/

@[simp] def modify_nth_tail (f : list α → list α) : ℕ → list α → list α
| 0     l      := f l
| (n+1) []     := []
| (n+1) (a::l) := a :: modify_nth_tail n l

@[simp] def modify_head (f : α → α) : list α → list α
| []     := []
| (a::l) := f a :: l

def modify_nth (f : α → α) : ℕ → list α → list α :=
modify_nth_tail (modify_head f)

theorem remove_nth_eq_nth_tail : ∀ n (l : list α), remove_nth l n = modify_nth_tail tail n l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (cons _) (remove_nth_eq_nth_tail _ _)

theorem update_nth_eq_modify_nth (a : α) : ∀ n (l : list α),
  update_nth l n a = modify_nth (λ _, a) n l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (b::l) := congr_arg (cons _) (update_nth_eq_modify_nth _ _)

theorem modify_nth_eq_update_nth (f : α → α) : ∀ n (l : list α),
  modify_nth f n l = ((λ a, update_nth l n (f a)) <$> nth l n).get_or_else l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (b::l) := (congr_arg (cons b)
  (modify_nth_eq_update_nth n l)).trans $ by cases nth l n; refl

theorem nth_modify_nth (f : α → α) : ∀ n (l : list α) m,
  nth (modify_nth f n l) m = (λ a, if n = m then f a else a) <$> nth l m
| n     l      0     := by cases l; cases n; refl
| n     []     (m+1) := by cases n; refl
| 0     (a::l) (m+1) := by cases nth l m; refl
| (n+1) (a::l) (m+1) := (nth_modify_nth n l m).trans $
  by cases nth l m with b; by_cases n = m; simp [h, mt succ_inj]

theorem modify_nth_tail_length (f : list α → list α) (H : ∀ l, length (f l) = length l) :
  ∀ n l, length (modify_nth_tail f n l) = length l
| 0     l      := H _
| (n+1) []     := rfl
| (n+1) (a::l) := @congr_arg _ _ _ _ (+1) (modify_nth_tail_length _ _)

@[simp] theorem modify_nth_length (f : α → α) :
  ∀ n l, length (modify_nth f n l) = length l :=
modify_nth_tail_length _ (λ l, by cases l; refl)

@[simp] theorem update_nth_length (l : list α) (n) (a : α) :
  length (update_nth l n a) = length l :=
by simp [update_nth_eq_modify_nth]

@[simp] theorem nth_modify_nth_eq (f : α → α) (n) (l : list α) :
  nth (modify_nth f n l) n = f <$> nth l n :=
by simp [nth_modify_nth]

@[simp] theorem nth_modify_nth_ne (f : α → α) {m n} (l : list α) (h : m ≠ n) :
  nth (modify_nth f m l) n = nth l n :=
by simp [nth_modify_nth, h]; cases nth l n; refl

theorem nth_update_nth_eq (a : α) (n) (l : list α) :
  nth (update_nth l n a) n = (λ _, a) <$> nth l n :=
by simp [update_nth_eq_modify_nth]

theorem nth_update_nth_of_lt (a : α) {n} {l : list α} (h : n < length l) :
  nth (update_nth l n a) n = some a :=
by rw [nth_update_nth_eq, nth_le_nth h]; refl

theorem nth_update_nth_ne (a : α) {m n} (l : list α) (h : m ≠ n) :
  nth (update_nth l m a) n = nth l n :=
by simp [update_nth_eq_modify_nth, h]

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

theorem drop_eq_nth_le_cons : ∀ {n} {l : list α} h,
  drop n l = nth_le l n h :: drop (n+1) l
| 0     (a::l) h := rfl
| (n+1) (a::l) h := @drop_eq_nth_le_cons n _ _

theorem modify_nth_tail_eq_take_drop (f : list α → list α) (H : f [] = []) :
  ∀ n l, modify_nth_tail f n l = take n l ++ f (drop n l)
| 0     l      := rfl
| (n+1) []     := H.symm
| (n+1) (b::l) := congr_arg (cons b) (modify_nth_tail_eq_take_drop n l)

theorem modify_nth_eq_take_drop (f : α → α) :
  ∀ n l, modify_nth f n l = take n l ++ modify_head f (drop n l) :=
modify_nth_tail_eq_take_drop _ rfl

theorem modify_nth_eq_take_cons_drop (f : α → α) {n l} (h) :
  modify_nth f n l = take n l ++ f (nth_le l n h) :: drop (n+1) l :=
by rw [modify_nth_eq_take_drop, drop_eq_nth_le_cons h]; refl

theorem update_nth_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
  update_nth l n a = take n l ++ a :: drop (n+1) l :=
by rw [update_nth_eq_modify_nth, modify_nth_eq_take_cons_drop _ h]

/- take_while -/

def take_while (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: take_while l else []

/- foldl, foldr, scanl, scanr -/

@[simp] theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a := rfl

@[simp] theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : list β) :
  foldl f a (b::l) = foldl f (f a b) l := rfl

@[simp] theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  foldr f b (a::l) = f a (foldr f b l) := rfl

@[simp] theorem foldl_append (f : α → β → α) :
  ∀ (a : α) (l₁ l₂ : list β), foldl f a (l₁++l₂) = foldl f (foldl f a l₁) l₂
| a []      l₂ := rfl
| a (b::l₁) l₂ := by simp [foldl_append]

@[simp] theorem foldr_append (f : α → β → β) :
  ∀ (b : β) (l₁ l₂ : list α), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by simp [foldr_append]

@[simp] theorem foldl_join (f : α → β → α) :
  ∀ (a : α) (L : list (list β)), foldl f a (join L) = foldl (foldl f) a L
| a []     := rfl
| a (l::L) := by simp [foldl_join]

@[simp] theorem foldr_join (f : α → β → β) :
  ∀ (b : β) (L : list (list α)), foldr f b (join L) = foldr (λ l b, foldr f b l) b L
| a []     := rfl
| a (l::L) := by simp [foldr_join]

theorem foldl_reverse (f : α → β → α) (a : α) (l : list β) : foldl f a (reverse l) = foldr (λx y, f y x) a l :=
by induction l; simp [*, foldr]

theorem foldr_reverse (f : α → β → β) (a : β) (l : list α) : foldr f a (reverse l) = foldl (λx y, f y x) a l :=
let t := foldl_reverse (λx y, f y x) a (reverse l) in
by rw reverse_reverse l at t; rwa t

@[simp] theorem foldr_eta : ∀ (l : list α), foldr cons [] l = l
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

@[simp] theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] := rfl

@[simp] theorem scanr_aux_cons (f : α → β → β) (b : β) : ∀ (a : α) (l : list α),
  scanr_aux f b (a::l) = (foldr f b (a::l), scanr f b l)
| a []     := rfl
| a (x::l) := let t := scanr_aux_cons x l in
  by simp [scanr, scanr_aux] at t; simp [scanr, scanr_aux, t]

@[simp] theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  scanr f b (a::l) = foldr f b (a::l) :: scanr f b l :=
by simp [scanr]

section foldl_eq_foldr
  -- foldl and foldr coincide when f is commutative and associative
  variables {f : α → α → α} (hcomm : commutative f) (hassoc : associative f)

  include hassoc
  theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l++[b]) = foldr f b (a::l)
  | a b nil      := rfl
  | a b (c :: l) := by simp [foldl1_eq_foldr1 _ _ l]; rw hassoc

  include hcomm
  theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b::l) = f b (foldl f a l)
  | a b  nil    := hcomm a b
  | a b  (c::l) := by simp;
    rw [← foldl_eq_of_comm_of_assoc, right_comm _ hcomm hassoc]; simp

  theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a nil      := rfl
  | a (b :: l) :=
    by simp [foldl_eq_of_comm_of_assoc hcomm hassoc]; rw (foldl_eq_foldr a l)
end foldl_eq_foldr

section
variables {op : α → α → α} [ha : is_associative α op] [hc : is_commutative α op]
local notation a * b := op a b
local notation l <*> a := foldl op a l

include ha

lemma foldl_assoc : ∀ {l : list α} {a₁ a₂}, l <*> (a₁ * a₂) = a₁ * (l <*> a₂)
| [] a₁ a₂ := by simp
| (a :: l) a₁ a₂ :=
  calc a::l <*> (a₁ * a₂) = l <*> (a₁ * (a₂ * a)) : by simp [ha.assoc]
    ... = a₁ * (a::l <*> a₂) : by rw [foldl_assoc]; simp

lemma foldl_op_eq_op_foldr_assoc : ∀{l : list α} {a₁ a₂}, (l <*> a₁) * a₂ = a₁ * l.foldr (*) a₂
| [] a₁ a₂ := by simp
| (a :: l) a₁ a₂ := by simp [foldl_assoc, ha.assoc]; rw [foldl_op_eq_op_foldr_assoc]

include hc

lemma foldl_assoc_comm_cons {l : list α} {a₁ a₂} : (a₁ :: l) <*> a₂ = a₁ * (l <*> a₂) :=
by rw [foldl_cons, hc.comm, foldl_assoc]

end

/- sum -/

@[to_additive list.sum]
def prod [has_mul α] [has_one α] : list α → α := foldl (*) 1
attribute [to_additive list.sum.equations._eqn_1] list.prod.equations._eqn_1

section monoid
variables [monoid α] {l l₁ l₂ : list α} {a : α}

@[simp, to_additive list.sum_nil]
theorem prod_nil : ([] : list α).prod = 1 := rfl

@[simp, to_additive list.sum_cons]
theorem prod_cons : (a::l).prod = a * l.prod :=
calc (a::l).prod = foldl (*) (a * 1) l : by simp [list.prod]
  ... = _ : foldl_assoc

@[simp, to_additive list.sum_append]
theorem prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
calc (l₁ ++ l₂).prod = foldl (*) (foldl (*) 1 l₁ * 1) l₂ : by simp [list.prod]
  ... = l₁.prod * l₂.prod : foldl_assoc

@[simp, to_additive list.sum_join]
theorem prod_join {l : list (list α)} : l.join.prod = (l.map list.prod).prod :=
by induction l; simp [list.join, *] at *

end monoid

/- all & any, bounded quantifiers over lists -/

theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x :=
by simp

@[simp] theorem forall_mem_cons' {p : α → Prop} {a : α} {l : list α} :
  (∀ (x : α), x = a ∨ x ∈ l → p x) ↔ p a ∧ ∀ x ∈ l, p x :=
by simp [or_imp_distrib, forall_and_distrib]

theorem forall_mem_cons {p : α → Prop} {a : α} {l : list α} :
  (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
by simp

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : list α}
    (h : ∀ x ∈ a :: l, p x) :
  ∀ x ∈ l, p x :=
(forall_mem_cons.1 h).2

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x ∈ @nil α, p x :=
by simp

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : list α) (h : p a) :
  ∃ x ∈ a :: l, p x :=
bex.intro a (by simp) h

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ l, p x) :
  ∃ x ∈ a :: l, p x :=
bex.elim h (λ x xl px, bex.intro x (by simp [xl]) px)

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ a :: l, p x) :
  p a ∨ ∃ x ∈ l, p x :=
bex.elim h (λ x xal px,
  or.elim (eq_or_mem_of_mem_cons xal)
    (assume : x = a, begin rw ←this, simp [px] end)
    (assume : x ∈ l, or.inr (bex.intro x this px)))

@[simp] theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : list α) :
  (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
iff.intro or_exists_of_exists_mem_cons
  (assume h, or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists)

@[simp] theorem all_nil (p : α → bool) : all [] p = tt := rfl

@[simp] theorem all_cons (p : α → bool) (a : α) (l : list α) : all (a::l) p = (p a && all l p) := rfl

theorem all_iff_forall {p : α → bool} {l : list α} : all l p ↔ ∀ a ∈ l, p a :=
by induction l with a l; simp [forall_and_distrib, *]

theorem all_iff_forall_prop {p : α → Prop} [decidable_pred p]
  {l : list α} : all l (λ a, p a) ↔ ∀ a ∈ l, p a :=
by simp [all_iff_forall]

@[simp] theorem any_nil (p : α → bool) : any [] p = ff := rfl

@[simp] theorem any_cons (p : α → bool) (a : α) (l : list α) : any (a::l) p = (p a || any l p) := rfl

theorem any_iff_exists {p : α → bool} {l : list α} : any l p ↔ ∃ a ∈ l, p a :=
by induction l with a l; simp [and_or_distrib_left, exists_or_distrib, *]

theorem any_iff_exists_prop {p : α → Prop} [decidable_pred p]
  {l : list α} : any l (λ a, p a) ↔ ∃ a ∈ l, p a :=
by simp [any_iff_exists]

theorem any_of_mem {p : α → bool} {a : α} {l : list α} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
any_iff_exists.2 ⟨_, h₁, h₂⟩

instance decidable_forall_mem {p : α → Prop} [decidable_pred p] (l : list α) :
  decidable (∀ x ∈ l, p x) :=
decidable_of_iff _ all_iff_forall_prop

instance decidable_exists_mem {p : α → Prop} [decidable_pred p] (l : list α) :
  decidable (∃ x ∈ l, p x) :=
decidable_of_iff _ any_iff_exists_prop

/- find -/

section find
variables (p : α → Prop) [decidable_pred p] 
def find : list α → option α
| []     := none
| (a::l) := if p a then some a else find l

def find_indexes_aux (p : α → Prop) [decidable_pred p] : list α → nat → list nat
| []     n := []
| (a::l) n := let t := find_indexes_aux l (succ n) in if p a then n :: t else t

def find_indexes (p : α → Prop) [decidable_pred p] (l : list α) : list nat :=
find_indexes_aux p l 0

@[simp] theorem find_nil : find p [] = none := rfl

@[simp] theorem find_cons_of_pos {p : α → Prop} [h : decidable_pred p] {a : α}
  (l) (h : p a) : find p (a::l) = some a :=
if_pos h

@[simp] theorem find_cons_of_neg {p : α → Prop} [h : decidable_pred p] {a : α}
  (l) (h : ¬ p a) : find p (a::l) = find p l :=
if_neg h

@[simp] theorem find_eq_none {p : α → Prop} [h : decidable_pred p] {l : list α} :
  find p l = none ↔ ∀ x ∈ l, ¬ p x :=
begin
  induction l with a l IH, {simp},
  by_cases p a; simp [h, IH],
  intro, contradiction
end

@[simp] theorem find_some {p : α → Prop} [h : decidable_pred p] {l : list α} {a : α}
  (H : find p l = some a) : p a :=
begin
  induction l with b l IH, {contradiction},
  by_cases p b; simp [h] at H,
  { subst b, assumption },
  { exact IH H }
end

@[simp] theorem find_mem {p : α → Prop} [h : decidable_pred p] {l : list α} {a : α}
  (H : find p l = some a) : a ∈ l :=
begin
  induction l with b l IH, {contradiction},
  by_cases p b; simp [h] at H,
  { subst b, apply mem_cons_self },
  { exact mem_cons_of_mem _ (IH H) }
end

end find

def indexes_of [decidable_eq α] (a : α) : list α → list nat := find_indexes (eq a)

/- filter_map -/

@[simp] theorem filter_map_nil (f : α → option β) : filter_map f [] = [] := rfl

@[simp] theorem filter_map_cons_none {f : α → option β} (a : α) (l : list α) (h : f a = none) :
  filter_map f (a :: l) = filter_map f l :=
by simp [filter_map, h]

@[simp] theorem filter_map_cons_some (f : α → option β)
  (a : α) (l : list α) {b : β} (h : f a = some b) :
  filter_map f (a :: l) = b :: filter_map f l :=
by simp [filter_map, h]

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
funext $ λ l, begin
  induction l with a l IH, {simp},
  simp [filter_map_cons_some (some ∘ f) _ _ rfl, IH]
end

theorem filter_map_eq_filter (p : α → Prop) [decidable_pred p] :
  filter_map (option.guard p) = filter p :=
funext $ λ l, begin
  induction l with a l IH, {simp},
  by_cases p a with pa; simp [filter_map, option.guard, pa, IH]
end

theorem filter_map_filter_map (f : α → option β) (g : β → option γ) (l : list α) :
  filter_map g (filter_map f l) = filter_map (λ x, (f x).bind g) l :=
begin
  induction l with a l IH, {refl},
  cases h : f a with b,
  { rw [filter_map_cons_none _ _ h, filter_map_cons_none, IH],
    simp [h, option.bind] },
  rw filter_map_cons_some _ _ _ h,
  cases h' : g b with c;
  [ rw [filter_map_cons_none _ _ h', filter_map_cons_none, IH],
    rw [filter_map_cons_some _ _ _ h', filter_map_cons_some, IH] ];
  simp [h, h', option.bind]
end

theorem map_filter_map (f : α → option β) (g : β → γ) (l : list α) :
  map g (filter_map f l) = filter_map (λ x, (f x).map g) l :=
by rw [← filter_map_eq_map, filter_map_filter_map]; refl

theorem filter_map_map (f : α → β) (g : β → option γ) (l : list α) :
  filter_map g (map f l) = filter_map (g ∘ f) l :=
by rw [← filter_map_eq_map, filter_map_filter_map]; refl

theorem filter_filter_map (f : α → option β) (p : β → Prop) [decidable_pred p] (l : list α) :
  filter p (filter_map f l) = filter_map (λ x, (f x).filter p) l :=
by rw [← filter_map_eq_filter, filter_map_filter_map]; refl

theorem filter_map_filter (p : α → Prop) [decidable_pred p] (f : α → option β) (l : list α) :
  filter_map f (filter p l) = filter_map (λ x, if p x then f x else none) l :=
begin
  rw [← filter_map_eq_filter, filter_map_filter_map], congr,
  apply funext, intro x,
  show (option.guard p x).bind f = ite (p x) (f x) none,
  by_cases p x; simp [h, option.guard, option.bind]
end

@[simp] theorem filter_map_some (l : list α) : filter_map some l = l :=
by rw filter_map_eq_map; apply map_id

@[simp] theorem mem_filter_map (f : α → option β) (l : list α) {b : β} :
  b ∈ filter_map f l ↔ ∃ a, a ∈ l ∧ f a = some b :=
begin
  induction l with a l IH, {simp},
  cases h : f a with b',
  { have : f a ≠ some b, {rw h, intro, contradiction},
    simp [filter_map_cons_none _ _ h, IH,
          or_and_distrib_right, exists_or_distrib, this] },
  { have : f a = some b ↔ b = b',
    { split; intro t, {rw t at h; injection h}, {exact t.symm ▸ h} },
    simp [filter_map_cons_some _ _ _ h, IH,
          or_and_distrib_right, exists_or_distrib, this] }
end

theorem map_filter_map_of_inv (f : α → option β) (g : β → α)
  (H : ∀ x : α, (f x).map g = some x) (l : list α) :
  map g (filter_map f l) = l :=
by simp [map_filter_map, H]

theorem filter_map_sublist_filter_map (f : α → option β) {l₁ l₂ : list α}
  (s : l₁ <+ l₂) : filter_map f l₁ <+ filter_map f l₂ :=
by induction s with l₁ l₂ a s IH l₁ l₂ a s IH;
   simp [filter_map]; cases f a with b;
   simp [filter_map, IH, sublist.cons, sublist.cons2]

/- filter -/

section filter
variables {p : α → Prop} [decidable_pred p]

@[simp] theorem filter_subset (l : list α) : filter p l ⊆ l :=
subset_of_sublist $ filter_sublist l

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
| []     ain := absurd ain (not_mem_nil a)
| (b::l) ain :=
  if pb : p b then
    have a ∈ b :: filter p l, begin simp [pb] at ain, assumption end,
    or.elim (eq_or_mem_of_mem_cons this)
      (assume : a = b, begin rw [← this] at pb, exact pb end)
      (assume : a ∈ filter p l, of_mem_filter this)
  else
    begin simp [pb] at ain, exact (of_mem_filter ain) end

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
filter_subset l h

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
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

@[simp] theorem mem_filter {a : α} {l} : a ∈ filter p l ↔ a ∈ l ∧ p a :=
⟨λ h, ⟨mem_of_mem_filter h, of_mem_filter h⟩, λ ⟨h₁, h₂⟩, mem_filter_of_mem h₁ h₂⟩

theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a :=
begin
  induction l with a l, {simp},
  by_cases p a; simp [filter, *],
  show filter p l ≠ a :: l, intro e,
  have := filter_sublist l, rw e at this,
  exact not_lt_of_ge (length_le_of_sublist this) (lt_succ_self _)
end

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a ∈ l, ¬p a :=
by simp [-and.comm, eq_nil_iff_forall_not_mem, mem_filter]

theorem filter_sublist_filter {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
by rw ← filter_map_eq_filter; exact filter_map_sublist_filter_map _ s

@[simp] theorem span_eq_take_drop (p : α → Prop) [decidable_pred p] : ∀ (l : list α), span p l = (take_while p l, drop_while p l)
| []     := rfl
| (a::l) := by by_cases p a with pa; simp [span, take_while, drop_while, pa, span_eq_take_drop l]

@[simp] theorem take_while_append_drop (p : α → Prop) [decidable_pred p] : ∀ (l : list α), take_while p l ++ drop_while p l = l
| []     := rfl
| (a::l) := by by_cases p a with pa; simp [take_while, drop_while, pa, take_while_append_drop l]

def countp (p : α → Prop) [decidable_pred p] : list α → nat
| []      := 0
| (x::xs) := if p x then succ (countp xs) else countp xs

@[simp] theorem countp_nil (p : α → Prop) [decidable_pred p] : countp p [] = 0 := rfl

@[simp] theorem countp_cons_of_pos {a : α} (l) (pa : p a) : countp p (a::l) = countp p l + 1 :=
if_pos pa

@[simp] theorem countp_cons_of_neg {a : α} (l) (pa : ¬ p a) : countp p (a::l) = countp p l :=
if_neg pa

theorem countp_eq_length_filter (l) : countp p l = length (filter p l) :=
by induction l with x l; [refl, by_cases (p x)]; simp [*, -add_comm]
local attribute [simp] countp_eq_length_filter

@[simp] theorem countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ :=
by simp

theorem exists_mem_of_countp_pos {l} (h : countp p l > 0) : ∃ a ∈ l, p a :=
by simp at h; exact
exists_imp_exists
  (λ a al, ⟨mem_of_mem_filter al, of_mem_filter al⟩)
  (exists_mem_of_length_pos h)

theorem countp_pos_of_mem {l a} (h : a ∈ l) (pa : p a) : countp p l > 0 :=
by simp; exact length_pos_of_mem (mem_filter_of_mem h pa)

theorem countp_le_of_sublist {l₁ l₂} (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ :=
by simpa using length_le_of_sublist (filter_sublist_filter s)

end filter

/- count -/

section count
variable [decidable_eq α]

def count (a : α) : list α → nat := countp (eq a)

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

theorem count_le_of_sublist (a : α) {l₁ l₂} : l₁ <+ l₂ → count a l₁ ≤ count a l₂ :=
countp_le_of_sublist

theorem count_cons_ge_count (a b : α) (l : list α) : count a (b :: l) ≥ count a l :=
count_le_of_sublist _ (sublist_cons _ _)

theorem count_singleton (a : α) : count a [a] = 1 :=
by simp

@[simp] theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
countp_append

@[simp] theorem count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
by rw [concat_eq_append, count_append, count_singleton]

theorem mem_of_count_pos {a : α} {l : list α} (h : count a l > 0) : a ∈ l :=
let ⟨a', ael, e⟩ := exists_mem_of_countp_pos h in e.symm ▸ ael

theorem count_pos_of_mem {a : α} {l : list α} (h : a ∈ l) : count a l > 0 :=
countp_pos_of_mem h rfl

theorem count_pos {a : α} {l : list α} : count a l > 0 ↔ a ∈ l :=
⟨mem_of_count_pos, count_pos_of_mem⟩

@[simp] theorem count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {l : list α} (h : count a l = 0) : a ∉ l :=
λ h', ne_of_gt (count_pos.2 h') h

@[simp] theorem count_repeat (a : α) (n : ℕ) : count a (repeat a n) = n :=
by rw [count, countp_eq_length_filter, filter_eq_self.2, length_repeat];
   exact λ b m, (eq_of_mem_repeat m).symm

theorem le_count_iff_repeat_sublist {a : α} {l : list α} {n : ℕ} : n ≤ count a l ↔ repeat a n <+ l :=
⟨λ h, ((repeat_sublist_repeat a).2 h).trans $
  have filter (eq a) l = repeat a (count a l), from eq_repeat.2
    ⟨by simp [count, countp_eq_length_filter], λ b m, (of_mem_filter m).symm⟩,
  by rw ← this; apply filter_sublist,
 λ h, by simpa using count_le_of_sublist a h⟩

end count

/- prefix, suffix, infix -/

def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂
def is_suffix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, t ++ l₁ = l₂
def is_infix (l₁ : list α) (l₂ : list α) : Prop := ∃ s t, s ++ l₁ ++ t = l₂

infix ` <+: `:50 := is_prefix
infix ` <:+ `:50 := is_suffix
infix ` <:+: `:50 := is_infix

@[simp] theorem prefix_append (l₁ l₂ : list α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩

@[simp] theorem suffix_append (l₁ l₂ : list α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

@[simp] theorem infix_append (l₁ l₂ l₃ : list α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

@[refl] theorem prefix_refl (l : list α) : l <+: l := ⟨[], append_nil _⟩

@[refl] theorem suffix_refl (l : list α) : l <:+ l := ⟨[], rfl⟩

@[simp] theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l := suffix_append [a]

@[simp] theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp

theorem infix_of_prefix {l₁ l₂ : list α} : l₁ <+: l₂ → l₁ <:+: l₂ :=
λ⟨t, h⟩, ⟨[], t, h⟩

theorem infix_of_suffix {l₁ l₂ : list α} : l₁ <:+ l₂ → l₁ <:+: l₂ :=
λ⟨t, h⟩, ⟨t, [], by simp [h]⟩

@[refl] theorem infix_refl (l : list α) : l <:+: l := infix_of_prefix $ prefix_refl l

@[trans] theorem is_prefix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
| l ._ ._ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩ := ⟨r₁ ++ r₂, by simp⟩

@[trans] theorem is_suffix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
| l ._ ._ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩ := ⟨l₂ ++ l₁, by simp⟩

@[trans] theorem is_infix.trans : ∀ {l₁ l₂ l₃ : list α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
| l ._ ._ ⟨l₁, r₁, rfl⟩ ⟨l₂, r₂, rfl⟩ := ⟨l₂ ++ l₁, r₁ ++ r₂, by simp⟩

theorem sublist_of_infix {l₁ l₂ : list α} : l₁ <:+: l₂ → l₁ <+ l₂ :=
λ⟨s, t, h⟩, by rw [← h]; exact (sublist_append_right _ _).trans (sublist_append_left _ _)

theorem sublist_of_prefix {l₁ l₂ : list α} : l₁ <+: l₂ → l₁ <+ l₂ :=
sublist_of_infix ∘ infix_of_prefix 

theorem sublist_of_suffix {l₁ l₂ : list α} : l₁ <:+ l₂ → l₁ <+ l₂ :=
sublist_of_infix ∘ infix_of_suffix

theorem length_le_of_infix {l₁ l₂ : list α} (s : l₁ <:+: l₂) : length l₁ ≤ length l₂ :=
length_le_of_sublist $ sublist_of_infix s

theorem eq_nil_of_infix_nil {l : list α} (s : l <:+: []) : l = [] :=
eq_nil_of_sublist_nil $ sublist_of_infix s

theorem eq_nil_of_prefix_nil {l : list α} (s : l <+: []) : l = [] :=
eq_nil_of_infix_nil $ infix_of_prefix s

theorem eq_nil_of_suffix_nil {l : list α} (s : l <:+ []) : l = [] :=
eq_nil_of_infix_nil $ infix_of_suffix s

theorem infix_iff_prefix_suffix (l₁ l₂ : list α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
⟨λ⟨s, t, e⟩, ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc]; exact ⟨_, rfl⟩⟩,
λ⟨._, ⟨t, rfl⟩, ⟨s, e⟩⟩, ⟨s, t, by rw append_assoc; exact e⟩⟩

theorem eq_of_infix_of_length_eq {l₁ l₂ : list α} (s : l₁ <:+: l₂) : length l₁ = length l₂ → l₁ = l₂ :=
eq_of_sublist_of_length_eq $ sublist_of_infix s

theorem eq_of_prefix_of_length_eq {l₁ l₂ : list α} (s : l₁ <+: l₂) : length l₁ = length l₂ → l₁ = l₂ :=
eq_of_sublist_of_length_eq $ sublist_of_prefix s

theorem eq_of_suffix_of_length_eq {l₁ l₂ : list α} (s : l₁ <:+ l₂) : length l₁ = length l₂ → l₁ = l₂ :=
eq_of_sublist_of_length_eq $ sublist_of_suffix s

theorem infix_of_mem_join : ∀ {L : list (list α)} {l}, l ∈ L → l <:+: join L
| (_  :: L) l (or.inl rfl) := infix_append [] _ _
| (l' :: L) l (or.inr h)   :=
  is_infix.trans (infix_of_mem_join h) $ infix_of_suffix $ suffix_append _ _

@[simp] def inits : list α → list (list α)
| []     := [[]]
| (a::l) := [] :: map (λt, a::t) (inits l)

@[simp] theorem mem_inits : ∀ (s t : list α), s ∈ inits t ↔ s <+: t
| s []     := suffices s = nil ↔ s <+: nil, by simpa,
  ⟨λh, h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
| s (a::t) :=
  suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t, by simpa,
  ⟨λo, match s, o with
  | ._, or.inl rfl := ⟨_, rfl⟩
  | s, or.inr ⟨r, hr, hs⟩ := let ⟨s, ht⟩ := (mem_inits _ _).1 hr in
    by rw [← hs, ← ht]; exact ⟨s, rfl⟩
  end, λmi, match s, mi with
  | [], ⟨._, rfl⟩ := or.inl rfl
  | (b::s), ⟨r, hr⟩ := list.no_confusion hr $ λba (st : s++r = t), or.inr $
    by rw ba; exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩
  end⟩

@[simp] def tails : list α → list (list α)
| []     := [[]]
| (a::l) := (a::l) :: tails l

@[simp] theorem mem_tails : ∀ (s t : list α), s ∈ tails t ↔ s <:+ t
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

theorem sublists_aux_eq_foldl : ∀ (l : list α) {β : Type u} (f : list α → list β → list β),
  sublists_aux l f = foldr f [] (sublists_aux l cons)
| []     β f := rfl
| (a::l) β f := suffices ∀ t, foldr (λ ys r, f ys (f (a :: ys) r)) [] t =
                         foldr f [] (t.foldr (λ ys r, ys :: (a :: ys) :: r) nil),
by simp [sublists_aux]; rw [sublists_aux_eq_foldl l, sublists_aux_eq_foldl l (λ ys r, ys :: (a :: ys) :: r), this],
λt, by induction t; simp; simp [ih_1]

theorem sublists_aux_cons_cons (l : list α) (a : α) :
  sublists_aux (a::l) cons = [a] :: foldr (λys r, ys :: (a :: ys) :: r) [] (sublists_aux l cons) :=
by rw [← sublists_aux_eq_foldl]; refl

@[simp] theorem mem_sublists (s t : list α) : s ∈ sublists t ↔ s <+ t :=
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
    { simp [yx] },
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
      λ hl ⟨t, te⟩, append_inj_right'
        ((take_append_drop (length l₂ - length l₁) l₂).trans te.symm)
        (by simp; exact nat.sub_sub_self hl)
  else is_false $ λ⟨t, te⟩, hl $
    show length l₁ ≤ length l₂, by rw [← te, length_append]; apply nat.le_add_left

instance decidable_infix [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <:+: l₂)
| []      l₂ := is_true ⟨[], l₂, rfl⟩
| (a::l₁) [] := is_false $ λ⟨s, t, te⟩, absurd te $ append_ne_nil_of_ne_nil_left _ _ $
                append_ne_nil_of_ne_nil_right _ _ $ λh, list.no_confusion h
| l₁      l₂ := decidable_of_decidable_of_iff (list.decidable_bex (λt, l₁ <+: t) (tails l₂)) $
  by refine (exists_congr (λt, _)).trans (infix_iff_prefix_suffix _ _).symm;
     exact ⟨λ⟨h1, h2⟩, ⟨h2, (mem_tails _ _).1 h1⟩, λ⟨h2, h1⟩, ⟨(mem_tails _ _).2 h1, h2⟩⟩

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

/- insert -/
section insert
variable [decidable_eq α]

@[simp] theorem insert_nil (a : α) : insert a nil = [a] := rfl

theorem insert.def (a : α) (l : list α) : insert a l = if a ∈ l then l else a :: l := rfl

@[simp] theorem insert_of_mem {a : α} {l : list α} (h : a ∈ l) : insert a l = l :=
by simp [insert.def, h]

@[simp] theorem insert_of_not_mem {a : α} {l : list α} (h : a ∉ l) : insert a l = a :: l :=
by simp [insert.def, h]

@[simp] theorem mem_insert_iff {a b : α} {l : list α} : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
begin
  by_cases b ∈ l with h'; simp [h'],
  apply (or_iff_right_of_imp _).symm,
  exact λ e, e.symm ▸ h'
end

@[simp] theorem suffix_insert (a : α) (l : list α) : l <:+ insert a l :=
by by_cases a ∈ l; simp *

@[simp] theorem mem_insert_self (a : α) (l : list α) : a ∈ insert a l :=
mem_insert_iff.2 (or.inl rfl)

@[simp] theorem mem_insert_of_mem {a b : α} {l : list α} (h : a ∈ l) : a ∈ insert b l :=
mem_insert_iff.2 (or.inr h)

theorem eq_or_mem_of_mem_insert {a b : α} {l : list α} (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
mem_insert_iff.1 h

@[simp] theorem length_insert_of_mem {a : α} [decidable_eq α] {l : list α} (h : a ∈ l) :
  length (insert a l) = length l :=
by simp [h]

@[simp] theorem length_insert_of_not_mem {a : α} [decidable_eq α] {l : list α} (h : a ∉ l) :
  length (insert a l) = length l + 1 :=
by simp [h]

end insert

/- erase -/
section erase
variable [decidable_eq α]

@[simp] theorem erase_nil (a : α) : [].erase a = [] := rfl

theorem erase_cons (a b : α) (l : list α) : (b :: l).erase a = if b = a then l else b :: l.erase a := rfl

@[simp] theorem erase_cons_head (a : α) (l : list α) : (a :: l).erase a = l :=
by simp [erase_cons]

@[simp] theorem erase_cons_tail {a b : α} (l : list α) (h : b ≠ a) : (b::l).erase a = b :: l.erase a :=
by simp [erase_cons, h]

@[simp] theorem erase_of_not_mem {a : α} {l : list α} (h : a ∉ l) : l.erase a = l :=
by induction l with b l; [refl,
  simp [(ne_of_not_mem_cons h).symm, ih_1 (not_mem_of_not_mem_cons h)]]

theorem exists_erase_eq {a : α} {l : list α} (h : a ∈ l) :
  ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ :=
by induction l with b l; [cases h, {
  simp at h,
  by_cases b = a with e,
  { subst b, exact ⟨[], l, not_mem_nil _, rfl, by simp⟩ },
  { exact let ⟨l₁, l₂, h₁, h₂, h₃⟩ := ih_1 (h.resolve_left (ne.symm e)) in
    ⟨b::l₁, l₂, not_mem_cons_of_ne_of_not_mem (ne.symm e) h₁,
      by rw h₂; refl,
      by simp [e, h₃]⟩ } }]

@[simp] theorem length_erase_of_mem {a : α} {l : list α} (h : a ∈ l) : length (l.erase a) = pred (length l) :=
match l, l.erase a, exists_erase_eq h with
| ._, ._, ⟨l₁, l₂, _, rfl, rfl⟩ := by simp [-add_comm]; refl
end

theorem erase_append_left {a : α} : ∀ {l₁ : list α} (l₂), a ∈ l₁ → (l₁++l₂).erase a = l₁.erase a ++ l₂
| (x::xs) l₂  h := begin
  by_cases x = a with h'; simp [h'],
  rw erase_append_left l₂ (mem_of_ne_of_mem (ne.symm h') h)
end

theorem erase_append_right {a : α} : ∀ {l₁ : list α} (l₂), a ∉ l₁ → (l₁++l₂).erase a = l₁ ++ l₂.erase a
| []      l₂ h := rfl
| (x::xs) l₂ h := by simp [*, (ne_of_not_mem_cons h).symm, (not_mem_of_not_mem_cons h)]

theorem erase_sublist (a : α) (l : list α) : l.erase a <+ l :=
if h : a ∈ l then match l, l.erase a, exists_erase_eq h with
| ._, ._, ⟨l₁, l₂, _, rfl, rfl⟩ := by simp
end else by simp [h]

theorem erase_subset (a : α) (l : list α) : l.erase a ⊆ l :=
subset_of_sublist (erase_sublist a l)

theorem erase_sublist_erase (a : α) : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → l₁.erase a <+ l₂.erase a
| ._ ._ sublist.slnil             := sublist.slnil
| ._ ._ (sublist.cons  l₁ l₂ b s) := if h : b = a
  then by rw [h, erase_cons_head]; exact (erase_sublist _ _).trans s
  else by rw erase_cons_tail _ h; exact (erase_sublist_erase s).cons _ _ _
| ._ ._ (sublist.cons2 l₁ l₂ b s) := if h : b = a
  then by rw [h, erase_cons_head, erase_cons_head]; exact s
  else by rw [erase_cons_tail _ h, erase_cons_tail _ h]; exact (erase_sublist_erase s).cons2 _ _ _

theorem mem_erase_of_ne_of_mem {a b : α} {l : list α} (ab : a ≠ b) (al : a ∈ l) : a ∈ l.erase b :=
if h : b ∈ l then match l, l.erase b, exists_erase_eq h, al with
| ._, ._, ⟨l₁, l₂, _, rfl, rfl⟩, al :=
  by simp at *; exact or.resolve_left al ab
end else by simp [h, al]

theorem mem_of_mem_erase {a b : α} {l : list α} : a ∈ l.erase b → a ∈ l :=
@erase_subset _ _ _ _ _

theorem erase_comm (a b : α) (l : list α) : (l.erase a).erase b = (l.erase b).erase a :=
if ab : a = b then by simp [ab] else
if ha : a ∈ l then
if hb : b ∈ l then match l, l.erase a, exists_erase_eq ha, hb with
| ._, ._, ⟨l₁, l₂, ha', rfl, rfl⟩, hb :=
  if h₁ : b ∈ l₁ then
    by rw [erase_append_left _ h₁, erase_append_left _ h₁,
           erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
  else
    by rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
           erase_cons_tail _ ab, erase_cons_head]
end
else by simp [hb, mt mem_of_mem_erase hb]
else by simp [ha, mt mem_of_mem_erase ha]

end erase

/- diff -/
section diff
variable [decidable_eq α]

@[simp] theorem diff_nil (l : list α) : l.diff [] = l := rfl 

@[simp] theorem diff_cons (l₁ l₂ : list α) (a : α) : l₁.diff (a::l₂) = (l₁.erase a).diff l₂ :=
by by_cases a ∈ l₁; simp [list.diff, h]

theorem diff_eq_foldl : ∀ (l₁ l₂ : list α), l₁.diff l₂ = foldl list.erase l₁ l₂
| l₁ []      := rfl
| l₁ (a::l₂) := (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)

end diff

/- zip & unzip -/

@[simp] theorem zip_cons_cons (a : α) (b : β) (l₁ : list α) (l₂ : list β) :
  zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ := rfl

@[simp] theorem zip_nil_left (l : list α) : zip ([] : list β) l = [] := rfl

@[simp] theorem zip_nil_right (l : list α) : zip l ([] : list β) = [] :=
by cases l; refl

@[simp] theorem unzip_nil : unzip (@nil (α × β)) = ([], []) := rfl

@[simp] theorem unzip_cons (a : α) (b : β) (l : list (α × β)) :
   unzip ((a, b) :: l) = (a :: (unzip l).1, b :: (unzip l).2) :=
by rw unzip; cases unzip l; refl

theorem zip_unzip : ∀ (l : list (α × β)), zip (unzip l).1 (unzip l).2 = l
| []            := rfl
| ((a, b) :: l) := by simp [zip_unzip l]

/- enum -/

theorem length_enum_from : ∀ n (l : list α), length (enum_from n l) = length l
| n []     := rfl
| n (a::l) := congr_arg nat.succ (length_enum_from _ _)

theorem length_enum : ∀ (l : list α), length (enum l) = length l := length_enum_from _

@[simp] theorem enum_from_nth : ∀ n (l : list α) m,
  nth (enum_from n l) m = (λ a, (n + m, a)) <$> nth l m
| n []       m     := rfl
| n (a :: l) 0     := rfl
| n (a :: l) (m+1) := (enum_from_nth (n+1) l m).trans $
  by rw [add_right_comm]; refl

@[simp] theorem enum_nth : ∀ (l : list α) n,
  nth (enum l) n = (λ a, (n, a)) <$> nth l n :=
by simp [enum]

@[simp] theorem enum_from_map_snd : ∀ n (l : list α),
  map prod.snd (enum_from n l) = l
| n []       := rfl
| n (a :: l) := congr_arg (cons _) (enum_from_map_snd _ _)

@[simp] theorem enum_map_snd : ∀ (l : list α),
  map prod.snd (enum l) = l := enum_from_map_snd _


/- product -/

def product (l₁ : list α) (l₂ : list β) : list (α × β) :=
l₁.bind $ λ a, l₂.map $ prod.mk a

@[simp] theorem nil_product (l : list β) : product (@nil α) l = [] := rfl

@[simp] theorem product_cons (a : α) (l₁ : list α) (l₂ : list β)
        : product (a::l₁) l₂ = map (λ b, (a, b)) l₂ ++ product l₁ l₂ := rfl

@[simp] theorem product_nil : ∀ (l : list α), product l (@nil β) = []
| []     := rfl
| (a::l) := begin rw [product_cons, product_nil], reflexivity end

@[simp] theorem mem_product {l₁ : list α} {l₂ : list β} {a : α} {b : β} :
  (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ :=
by simp [product]

theorem length_product (l₁ : list α) (l₂ : list β) :
  length (product l₁ l₂) = length l₁ * length l₂ :=
by induction l₁ with x l₁ IH; simp [*, right_distrib]

/- disjoint -/
section disjoint

def disjoint (l₁ l₂ : list α) : Prop := ∀ ⦃a⦄, (a ∈ l₁ → a ∈ l₂ → false)

theorem disjoint.symm {l₁ l₂ : list α} (d : disjoint l₁ l₂) : disjoint l₂ l₁
| a i₂ i₁ := d i₁ i₂

@[simp] theorem disjoint_comm {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ disjoint l₂ l₁ :=
⟨disjoint.symm, disjoint.symm⟩

theorem disjoint_left {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ ∀ {a}, a ∈ l₁ → a ∉ l₂ := iff.rfl

theorem disjoint_right {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
disjoint_comm

theorem disjoint_iff_ne {l₁ l₂ : list α} : disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
by simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {l₁ l₂ l : list α} (ss : l₁ ⊆ l) (d : disjoint l l₂) : disjoint l₁ l₂
| x m₁ := d (ss m₁)

theorem disjoint_of_subset_right {l₁ l₂ l : list α} (ss : l₂ ⊆ l) (d : disjoint l₁ l) : disjoint l₁ l₂
| x m m₁ := d m (ss m₁)

theorem disjoint_of_disjoint_cons_left {a : α} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
disjoint_of_subset_left (list.subset_cons _ _)

theorem disjoint_of_disjoint_cons_right {a : α} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
disjoint_of_subset_right (list.subset_cons _ _)

@[simp] theorem disjoint_nil_left (l : list α) : disjoint [] l
| a := (not_mem_nil a).elim

@[simp] theorem singleton_disjoint {l : list α} {a : α} : disjoint [a] l ↔ a ∉ l :=
by simp [disjoint]; refl

@[simp] theorem disjoint_singleton {l : list α} {a : α} : disjoint l [a] ↔ a ∉ l :=
by rw disjoint_comm; simp

@[simp] theorem disjoint_append_left {l₁ l₂ l : list α} :
  disjoint (l₁++l₂) l ↔ disjoint l₁ l ∧ disjoint l₂ l :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_append_right {l₁ l₂ l : list α} :
  disjoint l (l₁++l₂) ↔ disjoint l l₁ ∧ disjoint l l₂ :=
disjoint_comm.trans $ by simp [disjoint_append_left]

@[simp] theorem disjoint_cons_left {a : α} {l₁ l₂ : list α} :
  disjoint (a::l₁) l₂ ↔ a ∉ l₂ ∧ disjoint l₁ l₂ :=
(@disjoint_append_left _ [a] l₁ l₂).trans $ by simp

@[simp] theorem disjoint_cons_right {a : α} {l₁ l₂ : list α} :
  disjoint l₁ (a::l₂) ↔ a ∉ l₁ ∧ disjoint l₁ l₂ :=
disjoint_comm.trans $ by simp [disjoint_cons_left]

theorem disjoint_append_of_disjoint_left {l₁ l₂ l : list α} :
  disjoint l₁ l → disjoint l₂ l → disjoint (l₁++l₂) l :=
λ d₁ d₂ x h, or.elim (mem_append.1 h) (@d₁ x) (@d₂ x)

theorem disjoint_of_disjoint_append_left_left {l₁ l₂ l : list α} (d : disjoint (l₁++l₂) l) : disjoint l₁ l :=
(disjoint_append_left.1 d).1

theorem disjoint_of_disjoint_append_left_right {l₁ l₂ l : list α} (d : disjoint (l₁++l₂) l) : disjoint l₂ l :=
(disjoint_append_left.1 d).2

theorem disjoint_of_disjoint_append_right_left {l₁ l₂ l : list α} (d : disjoint l (l₁++l₂)) : disjoint l l₁ :=
(disjoint_append_right.1 d).1

theorem disjoint_of_disjoint_append_right_right {l₁ l₂ l : list α} (d : disjoint l (l₁++l₂)) : disjoint l l₂ :=
(disjoint_append_right.1 d).2

end disjoint

/- union -/
section union
variable [decidable_eq α]

@[simp] theorem nil_union (l : list α) : [] ∪ l = l := rfl

@[simp] theorem cons_union (l₁ l₂ : list α) (a : α) : a :: l₁ ∪ l₂ = insert a (l₁ ∪ l₂) := rfl

@[simp] theorem mem_union {l₁ l₂ : list α} {a : α} : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ :=
by induction l₁; simp *

theorem mem_union_left {a : α} {l₁ : list α} (h : a ∈ l₁) (l₂ : list α) : a ∈ l₁ ∪ l₂ :=
mem_union.2 (or.inl h)

theorem mem_union_right {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
mem_union.2 (or.inr h)

theorem sublist_suffix_of_union : Π l₁ l₂ : list α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
| [] l₂ := ⟨[], by refl, rfl⟩
| (a::l₁) l₂ := let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂ in
  by simp [e.symm]; by_cases a ∈ t ++ l₂ with h;
     [existsi t, existsi a::t]; simp [h];
     [apply sublist_cons_of_sublist _ s, apply cons_sublist_cons _ s]

theorem suffix_union_right (l₁ l₂ : list α) : l₂ <:+ l₁ ∪ l₂ :=
exists_imp_exists (λ a, and.right) (sublist_suffix_of_union l₁ l₂)

theorem union_sublist_append (l₁ l₂ : list α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂ in
e ▸ (append_sublist_append_right _).2 s

theorem forall_mem_union {p : α → Prop} {l₁ l₂ : list α} :
  (∀ x ∈ l₁ ∪ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
by simp [or_imp_distrib, forall_and_distrib]

theorem forall_mem_of_forall_mem_union_left {p : α → Prop} {l₁ l₂ : list α}
   (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₁, p x :=
(forall_mem_union.1 h).1

theorem forall_mem_of_forall_mem_union_right {p : α → Prop} {l₁ l₂ : list α}
   (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₂, p x :=
(forall_mem_union.1 h).2

end union

/- inter -/
section inter
variable [decidable_eq α]

@[simp] theorem inter_nil (l : list α) : [] ∩ l = [] := rfl

@[simp] theorem inter_cons_of_mem {a : α} (l₁ : list α) {l₂ : list α} (h : a ∈ l₂) :
  (a::l₁) ∩ l₂ = a :: (l₁ ∩ l₂) :=
if_pos h

@[simp] theorem inter_cons_of_not_mem {a : α} (l₁ : list α) {l₂ : list α} (h : a ∉ l₂) :
  (a::l₁) ∩ l₂ = l₁ ∩ l₂ :=
if_neg h

theorem mem_of_mem_inter_left {l₁ l₂ : list α} {a : α} : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
mem_of_mem_filter

theorem mem_of_mem_inter_right {l₁ l₂ : list α} {a : α} : a ∈ l₁ ∩ l₂ → a ∈ l₂ :=
of_mem_filter

theorem mem_inter_of_mem_of_mem {l₁ l₂ : list α} {a : α} : a ∈ l₁ → a ∈ l₂ → a ∈ l₁ ∩ l₂ :=
mem_filter_of_mem

@[simp] theorem mem_inter {a : α} {l₁ l₂ : list α} : a ∈ l₁ ∩ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ :=
mem_filter

theorem inter_subset_left (l₁ l₂ : list α) : l₁ ∩ l₂ ⊆ l₁ :=
filter_subset _

theorem inter_subset_right (l₁ l₂ : list α) : l₁ ∩ l₂ ⊆ l₂ :=
λ a, mem_of_mem_inter_right

theorem subset_inter {l l₁ l₂ : list α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ :=
λ a h, mem_inter.2 ⟨h₁ h, h₂ h⟩

theorem inter_eq_nil_iff_disjoint {l₁ l₂ : list α} : l₁ ∩ l₂ = [] ↔ disjoint l₁ l₂ :=
by simp [eq_nil_iff_forall_not_mem]; refl

theorem forall_mem_inter_of_forall_left {p : α → Prop} {l₁ : list α} (h : ∀ x ∈ l₁, p x)
     (l₂ : list α) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
ball.imp_left (λ x, mem_of_mem_inter_left) h

theorem forall_mem_inter_of_forall_right {p : α → Prop} (l₁ : list α) {l₂ : list α}
    (h : ∀ x ∈ l₂, p x) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
ball.imp_left (λ x, mem_of_mem_inter_right) h

end inter

/- pairwise relation (generalized no duplicate) -/

section pairwise
variable (R : α → α → Prop)
inductive pairwise : list α → Prop
| nil  : pairwise []
| cons : ∀ {a : α} {l : list α}, (∀ a' ∈ l, R a a') → pairwise l → pairwise (a::l)
attribute [simp] pairwise.nil

variable {R}
@[simp] theorem pairwise_cons {a : α} {l : list α} :
  pairwise R (a::l) ↔ (∀ a' ∈ l, R a a') ∧ pairwise R l :=
⟨λ p, by cases p with a l n p; exact ⟨n, p⟩, λ ⟨n, p⟩, p.cons n⟩

theorem rel_of_pairwise_cons {a : α} {l : list α}
  (p : pairwise R (a::l)) : ∀ {a'}, a' ∈ l → R a a' :=
(pairwise_cons.1 p).1

theorem pairwise_of_pairwise_cons {a : α} {l : list α}
  (p : pairwise R (a::l)) : pairwise R l :=
(pairwise_cons.1 p).2

theorem pairwise.imp_of_mem {S : α → α → Prop} {l : list α}
  (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : pairwise R l) : pairwise S l :=
begin
  induction p with a l r p IH generalizing H; constructor,
  { exact ball.imp_right
      (λ x h, H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r },
  { exact IH (λ a b m m', H
      (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')) }
end

theorem pairwise.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {l : list α} : pairwise R l → pairwise S l :=
pairwise.imp_of_mem (λ a b _ _, H a b)

theorem pairwise.iff_of_mem {S : α → α → Prop} {l : list α}
  (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : pairwise R l ↔ pairwise S l :=
⟨pairwise.imp_of_mem (λ a b m m', (H m m').1),
 pairwise.imp_of_mem (λ a b m m', (H m m').2)⟩

theorem pairwise.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {l : list α} : pairwise R l ↔ pairwise S l :=
pairwise.iff_of_mem (λ a b _ _, H a b)

theorem pairwise_of_forall {l : list α} (H : ∀ x y, R x y) : pairwise R l :=
by induction l; simp *

theorem pairwise.and_mem {l : list α} :
  pairwise R l ↔ pairwise (λ x y, x ∈ l ∧ y ∈ l ∧ R x y) l :=
pairwise.iff_of_mem (by simp {contextual := tt})

theorem pairwise.imp_mem {l : list α} :
  pairwise R l ↔ pairwise (λ x y, x ∈ l → y ∈ l → R x y) l :=
pairwise.iff_of_mem (by simp {contextual := tt})

theorem pairwise_of_sublist : Π {l₁ l₂ : list α}, l₁ <+ l₂ → pairwise R l₂ → pairwise R l₁
| ._ ._ sublist.slnil h := h
| ._ ._ (sublist.cons l₁ l₂ a s) (pairwise.cons i n) := pairwise_of_sublist s n
| ._ ._ (sublist.cons2 l₁ l₂ a s) (pairwise.cons i n) :=
  (pairwise_of_sublist s n).cons (ball.imp_left (subset_of_sublist s) i)

theorem pairwise_singleton (R) (a : α) : pairwise R [a] :=
by simp

theorem pairwise_pair {a b : α} : pairwise R [a, b] ↔ R a b :=
by simp

theorem pairwise_append {l₁ l₂ : list α} : pairwise R (l₁++l₂) ↔
  pairwise R l₁ ∧ pairwise R l₂ ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, R x y :=
by induction l₁ with x l₁ IH; simp [or_imp_distrib, forall_and_distrib, *]

theorem pairwise_app_comm (s : symmetric R) {l₁ l₂ : list α} :
  pairwise R (l₁++l₂) ↔ pairwise R (l₂++l₁) :=
have ∀ l₁ l₂ : list α,
  (∀ (x : α), x ∈ l₁ → ∀ (y : α), y ∈ l₂ → R x y) →
  (∀ (x : α), x ∈ l₂ → ∀ (y : α), y ∈ l₁ → R x y),
from λ l₁ l₂ a x xm y ym, s (a y ym x xm),
by simp [pairwise_append]; rw iff.intro (this l₁ l₂) (this l₂ l₁)

theorem pairwise_middle (s : symmetric R) {a : α} {l₁ l₂ : list α} :
  pairwise R (l₁ ++ a::l₂) ↔ pairwise R (a::(l₁++l₂)) :=
show pairwise R (l₁ ++ ([a] ++ l₂)) ↔ pairwise R ([a] ++ l₁ ++ l₂),
by rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁),
       pairwise_app_comm s]; simp

theorem pairwise_map (f : β → α) :
  ∀ {l : list β}, pairwise R (map f l) ↔ pairwise (λ a b : β, R (f a) (f b)) l
| []     := by simp
| (b::l) :=
  have (∀ a b', f b' = a → b' ∈ l → R (f b) a) ↔ ∀ (b' : β), b' ∈ l → R (f b) (f b'), from
  forall_swap.trans $ forall_congr $ by simp,
  by simp *; rw this

theorem pairwise_of_pairwise_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {l : list α}
  (p : pairwise S (map f l)) : pairwise R l :=
((pairwise_map f).1 p).imp H

theorem pairwise_map_of_pairwise {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {l : list α}
  (p : pairwise R l) : pairwise S (map f l) :=
(pairwise_map f).2 $ p.imp H

theorem pairwise_filter_map (f : β → option α) {l : list β} :
  pairwise R (filter_map f l) ↔ pairwise (λ a a' : β, ∀ (b ∈ f a) (b' ∈ f a'), R b b') l :=
let S (a a' : β) := ∀ (b ∈ f a) (b' ∈ f a'), R b b' in
begin
  simp, induction l with a l IH; simp,
  cases e : f a with b; simp [e, IH],
  rw [filter_map_cons_some _ _ _ e], simp [IH],
  show (∀ (a' : α) (x : β), f x = some a' → x ∈ l → R b a') ∧ pairwise S l ↔
        (∀ (a' : β), a' ∈ l → ∀ (b' : α), f a' = some b' → R b b') ∧ pairwise S l,
  from and_congr ⟨λ h b mb a ma, h a b ma mb, λ h a b ma mb, h b mb a ma⟩ iff.rfl
end

theorem pairwise_filter_map_of_pairwise {S : β → β → Prop} (f : α → option β)
  (H : ∀ (a a' : α), R a a' → ∀ (b ∈ f a) (b' ∈ f a'), S b b') {l : list α}
  (p : pairwise R l) : pairwise S (filter_map f l) :=
(pairwise_filter_map _).2 $ p.imp H

theorem pairwise_filter (p : α → Prop) [decidable_pred p] {l : list α} :
  pairwise R (filter p l) ↔ pairwise (λ x y, p x → p y → R x y) l :=
begin
  rw [← filter_map_eq_filter, pairwise_filter_map],
  apply pairwise.iff, intros b c, simp,
  have : (∀ (b' : α), p b → b = b' → ∀ (c' : α), p c → c = c' → R b' c') ↔
          ∀ (b' : α), b = b' → p b → ∀ (c' : α), c = c' → p c → R b' c' :=
    ⟨λ h a b c d e f, h a c b d f e, λ h a c b d f e, h a b c d e f⟩,
  simp [this]
end

theorem pairwise_filter_of_pairwise (p : α → Prop) [decidable_pred p] {l : list α}
  : pairwise R l → pairwise R (filter p l) :=
pairwise_of_sublist (filter_sublist _)

theorem pairwise_join {L : list (list α)} : pairwise R (join L) ↔
  (∀ l ∈ L, pairwise R l) ∧ pairwise (λ l₁ l₂, ∀ (x ∈ l₁) (y ∈ l₂), R x y) L :=
begin
  induction L with l L IH, {simp},
  have : (∀ (x : α), x ∈ l → ∀ (y : α) (x_1 : list α), y ∈ x_1 → x_1 ∈ L → R x y) ↔
          ∀ (a' : list α), a' ∈ L → ∀ (x : α), x ∈ l → ∀ (y : α), y ∈ a' → R x y :=
    ⟨λ h a b c d e f, h c d e a f b, λ h c d e a f b, h a b c d e f⟩,
  simp [pairwise_append, IH, this]
end

@[simp] theorem pairwise_reverse : ∀ {R} {l : list α},
  pairwise R (reverse l) ↔ pairwise (λ x y, R y x) l :=
suffices ∀ {R l}, @pairwise α R l → pairwise (λ x y, R y x) (reverse l),
from λ R l, ⟨λ p, reverse_reverse l ▸ this p, this⟩,
λ R l p, by induction p with a l h p IH;
  [simp, simpa [pairwise_append, IH] using h]

variable [decidable_rel R]
instance decidable_pairwise (l : list α) : decidable (pairwise R l) :=
by induction l; simp; apply_instance

/- pairwise reduct -/

def pw_filter (R : α → α → Prop) [decidable_rel R] : list α → list α
| []        := []
| (x :: xs) := let IH := pw_filter xs in if ∀ y ∈ IH, R x y then x :: IH else IH

@[simp] theorem pw_filter_nil : pw_filter R [] = [] := rfl 

@[simp] theorem pw_filter_cons_of_pos {a : α} {l : list α} (h : ∀ b ∈ pw_filter R l, R a b) :
  pw_filter R (a::l) = a :: pw_filter R l := if_pos h

@[simp] theorem pw_filter_cons_of_neg {a : α} {l : list α} (h : ¬ ∀ b ∈ pw_filter R l, R a b) :
  pw_filter R (a::l) = pw_filter R l := if_neg h

theorem pw_filter_sublist : ∀ (l : list α), pw_filter R l <+ l
| []     := nil_sublist _
| (x::l) := begin
  by_cases (∀ y ∈ pw_filter R l, R x y); dsimp at h,
  { rw [pw_filter_cons_of_pos h],
    exact cons_sublist_cons _ (pw_filter_sublist l) },
  { rw [pw_filter_cons_of_neg h],
    exact sublist_cons_of_sublist _ (pw_filter_sublist l) },
end

theorem pw_filter_subset (l : list α) : pw_filter R l ⊆ l :=
subset_of_sublist (pw_filter_sublist _)

theorem pairwise_pw_filter : ∀ (l : list α), pairwise R (pw_filter R l)
| []     := pairwise.nil _
| (x::l) := begin
  by_cases (∀ y ∈ pw_filter R l, R x y); dsimp at h,
  { rw [pw_filter_cons_of_pos h],
    exact pairwise_cons.2 ⟨h, pairwise_pw_filter l⟩ },
  { rw [pw_filter_cons_of_neg h],
    exact pairwise_pw_filter l },
end

theorem pw_filter_eq_self {l : list α} : pw_filter R l = l ↔ pairwise R l :=
⟨λ e, e ▸ pairwise_pw_filter l, λ p, begin
  induction l with x l IH, {simp},
  cases pairwise_cons.1 p with al p,
  rw [pw_filter_cons_of_pos (ball.imp_left (pw_filter_subset l) al), IH p],
end⟩

theorem forall_mem_pw_filter (neg_trans : ∀ {x y z}, R x z → R x y ∨ R y z)
  (a : α) (l : list α) : (∀ b ∈ pw_filter R l, R a b) ↔ (∀ b ∈ l, R a b) :=
⟨begin
  induction l with x l IH; simp *,
  by_cases (∀ y ∈ pw_filter R l, R x y); dsimp at h,
  { simp [pw_filter_cons_of_pos h],
    exact λ r H, ⟨r, IH H⟩ },
  { rw [pw_filter_cons_of_neg h],
    refine λ H, ⟨_, IH H⟩,
    cases e : find (λ y, ¬ R x y) (pw_filter R l) with k,
    { exact h.elim (ball.imp_right (λ_ _, not_not.1) (find_eq_none.1 e)) },
    { have := find_some e,
      exact (neg_trans (H k (find_mem e))).resolve_right this } }
end, ball.imp_left (pw_filter_subset l)⟩

end pairwise

/- chain relation (conjunction of R a b ∧ R b c ∧ R c d ...) -/

section chain
variable (R : α → α → Prop)
inductive chain : α → list α → Prop
| nil  (a : α) : chain a []
| cons : ∀ {a b : α} {l : list α}, R a b → chain b l → chain a (b::l)
attribute [simp] chain.nil

variable {R}
@[simp] theorem chain_cons {a b : α} {l : list α} :
  chain R a (b::l) ↔ R a b ∧ chain R b l :=
⟨λ p, by cases p with _ a b l n p; exact ⟨n, p⟩, λ ⟨n, p⟩, p.cons n⟩

theorem rel_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b::l)) : R a b :=
(chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b::l)) : chain R b l :=
(chain_cons.1 p).2

theorem chain.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {a : α} {l : list α} (p : chain R a l) : chain S a l :=
by induction p with _ a b l r p IH; constructor;
   [exact H _ _ r, exact IH]

theorem chain.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {a : α} {l : list α} : chain R a l ↔ chain S a l :=
⟨chain.imp (λ a b, (H a b).1), chain.imp (λ a b, (H a b).2)⟩

theorem chain.iff_mem {S : α → α → Prop} {a : α} {l : list α} :
  chain R a l ↔ chain (λ x y, x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
⟨λ p, by induction p with _ a b l r p IH; constructor;
  [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩,
   exact IH.imp (λ a b ⟨am, bm, h⟩,
    ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩)],
 chain.imp (λ a b h, h.2.2)⟩

theorem chain_singleton {a b : α} : chain R a [b] ↔ R a b :=
by simp

theorem chain_split {a b : α} {l₁ l₂ : list α} : chain R a (l₁++b::l₂) ↔
  chain R a (l₁++[b]) ∧ chain R b l₂ :=
by induction l₁ with x l₁ IH generalizing a; simp *

theorem chain_map (f : β → α) {b : β} {l : list β} :
  chain R (f b) (map f l) ↔ chain (λ a b : β, R (f a) (f b)) b l :=
by induction l generalizing b; simp *

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {a : α} {l : list α}
  (p : chain S (f a) (map f l)) : chain R a l :=
((chain_map f).1 p).imp H

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {a : α} {l : list α}
  (p : chain R a l) : chain S (f a) (map f l) :=
(chain_map f).2 $ p.imp H

theorem chain_of_pairwise {a : α} {l : list α} (p : pairwise R (a::l)) : chain R a l :=
begin
  cases pairwise_cons.1 p with r p', clear p,
  induction p' with b l r' p IH generalizing a; simp,
  simp at r, simp [r],
  show chain R b l, from IH r'
end

theorem chain_iff_pairwise (tr : transitive R) {a : α} {l : list α} :
  chain R a l ↔ pairwise R (a::l) :=
⟨λ c, begin
  induction c with b b c l r p IH, {simp},
  apply IH.cons _, simp [r],
  show ∀ x ∈ l, R b x, from λ x m, (tr r (rel_of_pairwise_cons IH m)),
end, chain_of_pairwise⟩

instance decidable_chain [decidable_rel R] (a : α) (l : list α) : decidable (chain R a l) :=
by induction l generalizing a; simp; apply_instance

end chain

/- no duplicates predicate -/

def nodup : list α → Prop := pairwise (≠)

section nodup

@[simp] theorem forall_mem_ne {a : α} {l : list α} : (∀ (a' : α), a' ∈ l → ¬a = a') ↔ a ∉ l :=
⟨λ h m, h _ m rfl, λ h a' m e, h (e.symm ▸ m)⟩

@[simp] theorem nodup_nil : @nodup α [] := pairwise.nil _

@[simp] theorem nodup_cons {a : α} {l : list α} : nodup (a::l) ↔ a ∉ l ∧ nodup l :=
by simp [nodup]

theorem nodup_cons_of_nodup {a : α} {l : list α} (m : a ∉ l) (n : nodup l) : nodup (a::l) :=
nodup_cons.2 ⟨m, n⟩

theorem nodup_singleton (a : α) : nodup [a] :=
nodup_cons_of_nodup (not_mem_nil a) nodup_nil

theorem nodup_of_nodup_cons {a : α} {l : list α} (h : nodup (a::l)) : nodup l :=
(nodup_cons.1 h).2

theorem not_mem_of_nodup_cons {a : α} {l : list α} (h : nodup (a::l)) : a ∉ l :=
(nodup_cons.1 h).1

theorem not_nodup_cons_of_mem {a : α} {l : list α} : a ∈ l → ¬ nodup (a :: l) :=
imp_not_comm.1 not_mem_of_nodup_cons

theorem nodup_of_sublist {l₁ l₂ : list α} : l₁ <+ l₂ → nodup l₂ → nodup l₁ :=
pairwise_of_sublist

theorem not_nodup_pair (a : α) : ¬ nodup [a, a] :=
not_nodup_cons_of_mem $ mem_singleton_self _

theorem nodup_iff_sublist {l : list α} : nodup l ↔ ∀ a, ¬ [a, a] <+ l :=
⟨λ d a h, not_nodup_pair a (nodup_of_sublist h d), begin
  induction l with a l IH; intro h, {simp},
  exact nodup_cons_of_nodup
    (λ al, h a $ cons_sublist_cons _ $ singleton_sublist.2 al)
    (IH $ λ a s, h a $ sublist_cons_of_sublist _ s)
end⟩

theorem nodup_iff_count_le_one [decidable_eq α] {l : list α} : nodup l ↔ ∀ a, count a l ≤ 1 :=
nodup_iff_sublist.trans $ forall_congr $ λ a,
have [a, a] <+ l ↔ 1 < count a l, from (@le_count_iff_repeat_sublist _ _ a l 2).symm,
(not_congr this).trans not_lt

@[simp] theorem count_eq_one_of_mem [decidable_eq α] {a : α} {l : list α}
  (d : nodup l) (h : a ∈ l) : count a l = 1 :=
le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos_of_mem h)

theorem nodup_of_nodup_append_left {l₁ l₂ : list α} : nodup (l₁++l₂) → nodup l₁ :=
nodup_of_sublist (sublist_append_left l₁ l₂)

theorem nodup_of_nodup_append_right {l₁ l₂ : list α} : nodup (l₁++l₂) → nodup l₂ :=
nodup_of_sublist (sublist_append_right l₁ l₂)

theorem nodup_append {l₁ l₂ : list α} : nodup (l₁++l₂) ↔ nodup l₁ ∧ nodup l₂ ∧ disjoint l₁ l₂ :=
by simp [nodup, pairwise_append, disjoint_iff_ne]

theorem disjoint_of_nodup_append {l₁ l₂ : list α} (d : nodup (l₁++l₂)) : disjoint l₁ l₂ :=
(nodup_append.1 d).2.2

theorem nodup_append_of_nodup {l₁ l₂ : list α} (d₁ : nodup l₁) (d₂ : nodup l₂) (dj : disjoint l₁ l₂) : nodup (l₁++l₂) :=
nodup_append.2 ⟨d₁, d₂, dj⟩

theorem nodup_app_comm {l₁ l₂ : list α} : nodup (l₁++l₂) ↔ nodup (l₂++l₁) :=
by simp [nodup_append]

theorem nodup_middle {a : α} {l₁ l₂ : list α} : nodup (l₁ ++ a::l₂) ↔ nodup (a::(l₁++l₂)) :=
by simp [nodup_append, not_or_distrib]

theorem nodup_of_nodup_map (f : α → β) {l : list α} : nodup (map f l) → nodup l :=
pairwise_of_pairwise_map f $ λ a b, mt $ congr_arg f

theorem nodup_map_on {f : α → β} {l : list α} (H : ∀x∈l, ∀y∈l, f x = f y → x = y)
  (d : nodup l) : nodup (map f l) :=
pairwise_map_of_pairwise _ (by exact λ a b ⟨ma, mb, n⟩ e, n (H a ma b mb e)) (pairwise.and_mem.1 d)

theorem nodup_map {f : α → β} {l : list α} (hf : injective f) (h : nodup l) : nodup (map f l) :=
nodup_map_on (assume x _ y _ h, hf h) h

theorem nodup_filter (p : α → Prop) [decidable_pred p] {l} : nodup l → nodup (filter p l) :=
pairwise_filter_of_pairwise p

@[simp] theorem nodup_reverse {l : list α} : nodup (reverse l) ↔ nodup l :=
pairwise_reverse.trans $ by simp [nodup, eq_comm]

instance nodup_decidable [decidable_eq α] : ∀ l : list α, decidable (nodup l) :=
list.decidable_pairwise

theorem nodup_erase_eq_filter [decidable_eq α] (a : α) {l} (d : nodup l) : l.erase a = filter (≠ a) l :=
begin
  induction d with b l m d IH; simp [list.erase, list.filter],
  by_cases b = a; simp *, subst b,
  show l = filter (λ a', ¬ a' = a) l, rw filter_eq_self.2,
  simpa only [eq_comm] using m
end

theorem nodup_erase_of_nodup [decidable_eq α] (a : α) {l} : nodup l → nodup (l.erase a) :=
nodup_of_sublist (erase_sublist _ _)

theorem mem_erase_iff_of_nodup [decidable_eq α] {a b : α} {l} (d : nodup l) :
  a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l :=
by rw nodup_erase_eq_filter b d; simp

theorem mem_erase_of_nodup [decidable_eq α] {a : α} {l} (h : nodup l) : a ∉ l.erase a :=
by rw mem_erase_iff_of_nodup h; simp

theorem nodup_join {L : list (list α)} : nodup (join L) ↔ (∀ l ∈ L, nodup l) ∧ pairwise disjoint L :=
by simp [nodup, pairwise_join, disjoint_left.symm]

theorem nodup_bind {l₁ : list α} {f : α → list β} : nodup (l₁.bind f) ↔
  (∀ x ∈ l₁, nodup (f x)) ∧ pairwise (λ (a b : α), disjoint (f a) (f b)) l₁ :=
by simp [bind, nodup_join, pairwise_map];
   rw [show (∀ (l : list β) (x : α), f x = l → x ∈ l₁ → nodup l) ↔
            (∀ (x : α), x ∈ l₁ → nodup (f x)),
       from forall_swap.trans $ forall_congr $ λ_, by simp]

theorem nodup_product {l₁ : list α} {l₂ : list β} (d₁ : nodup l₁) (d₂ : nodup l₂) :
  nodup (product l₁ l₂) :=
 nodup_bind.2
  ⟨λ a ma, nodup_map (injective_of_left_inverse (λ b, (rfl : (a,b).2 = b))) d₂,
  d₁.imp (λ a₁ a₂ n x,
    suffices ∀ (b₁ : β), b₁ ∈ l₂ → (a₁, b₁) = x → ∀ (b₂ : β), b₂ ∈ l₂ → (a₂, b₂) ≠ x, by simpa,
    λ b₁ mb₁ e b₂ mb₂ e', by subst e'; injection e; contradiction)⟩

theorem nodup_filter_map {f : α → option β} (pdi : true) {l : list α}
  (H : ∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') :
  nodup l → nodup (filter_map f l) :=
pairwise_filter_map_of_pairwise f $ λ a a' n b bm b' bm' e, n $ H a a' b' (e ▸ bm) bm'

theorem nodup_concat {a : α} {l : list α} (h : a ∉ l) (h' : nodup l) : nodup (concat l a) :=
by simp; exact nodup_append_of_nodup h' (nodup_singleton _) (disjoint_singleton.2 h)

theorem nodup_insert [decidable_eq α] {a : α} {l : list α} (h : nodup l) : nodup (insert a l) :=
by by_cases a ∈ l with h'; simp [h', h]; apply nodup_cons h' h

theorem nodup_union [decidable_eq α] (l₁ : list α) {l₂ : list α} (h : nodup l₂) :
  nodup (l₁ ∪ l₂) :=
begin
  induction l₁ with a l₁ ih generalizing l₂,
  { exact h },
  simp,
  apply nodup_insert,
  exact ih h
end

theorem nodup_inter_of_nodup [decidable_eq α] {l₁ : list α} (l₂) : nodup l₁ → nodup (l₁ ∩ l₂) :=
nodup_filter _

end nodup

/- erase duplicates function -/

section erase_dup
variable [decidable_eq α]

def erase_dup : list α → list α := pw_filter (≠)

@[simp] theorem erase_dup_nil : erase_dup [] = ([] : list α) := rfl

theorem erase_dup_cons_of_mem' {a : α} {l : list α} (h : a ∈ erase_dup l) :
  erase_dup (a::l) = erase_dup l :=
pw_filter_cons_of_neg $ by simpa using h

theorem erase_dup_cons_of_not_mem' {a : α} {l : list α} (h : a ∉ erase_dup l) :
  erase_dup (a::l) = a :: erase_dup l :=
pw_filter_cons_of_pos $ by simpa using h

@[simp] theorem mem_erase_dup {a : α} {l : list α} : a ∈ erase_dup l ↔ a ∈ l :=
by simpa using not_congr (@forall_mem_pw_filter α (≠) _
  (λ x y z xz, not_and_distrib.1 $ mt (and.rec eq.trans) xz) a l)

@[simp] theorem erase_dup_cons_of_mem {a : α} {l : list α} (h : a ∈ l) :
  erase_dup (a::l) = erase_dup l :=
erase_dup_cons_of_mem' $ mem_erase_dup.2 h

@[simp] theorem erase_dup_cons_of_not_mem {a : α} {l : list α} (h : a ∉ l) :
  erase_dup (a::l) = a :: erase_dup l :=
erase_dup_cons_of_not_mem' $ mt mem_erase_dup.1 h

theorem erase_dup_sublist : ∀ (l : list α), erase_dup l <+ l := pw_filter_sublist

theorem erase_dup_subset : ∀ (l : list α), erase_dup l ⊆ l := pw_filter_subset

theorem subset_erase_dup (l : list α) : l ⊆ erase_dup l :=
λ a, mem_erase_dup.2

theorem nodup_erase_dup : ∀ l : list α, nodup (erase_dup l) := pairwise_pw_filter

theorem erase_dup_eq_self {l : list α} : erase_dup l = l ↔ nodup l := pw_filter_eq_self

theorem erase_dup_append {l₁ l₂ : list α} : erase_dup (l₁ ++ l₂) = l₁ ∪ erase_dup l₂ :=
begin
  induction l₁ with a l₁ IH; simp, rw ← IH,
  show erase_dup (a :: (l₁ ++ l₂)) = insert a (erase_dup (l₁ ++ l₂)),
  by_cases a ∈ erase_dup (l₁ ++ l₂);
  [ rw [erase_dup_cons_of_mem' h, insert_of_mem h],
    rw [erase_dup_cons_of_not_mem' h, insert_of_not_mem h]]
end

end erase_dup

/- iota and range -/

@[simp] def range' : ℕ → ℕ → list ℕ
| s 0     := []
| s (n+1) := s :: range' (s+1) n

@[simp] theorem length_range' : ∀ (s n : ℕ), length (range' s n) = n
| s 0     := rfl
| s (n+1) := congr_arg succ (length_range' _ _)

@[simp] theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
| s 0     := by simp
| s (n+1) :=
  have m = s → m < s + (n + 1),
    from λ e, e ▸ lt_succ_of_le (le_add_right _ _),
  have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m,
    by simpa [eq_comm] using (@le_iff_eq_or_lt _ _ s m).symm,
  by simp [@mem_range' (s+1) n, or_and_distrib_left, or_iff_right_of_imp this, l]

theorem chain_succ_range' : ∀ s n : ℕ, chain (λ a b, b = succ a) s (range' (s+1) n)
| s 0     := chain.nil _ _
| s (n+1) := (chain_succ_range' (s+1) n).cons rfl

theorem chain_lt_range' (s n : ℕ) : chain (<) s (range' (s+1) n) :=
(chain_succ_range' s n).imp (λ a b e, e.symm ▸ lt_succ_self _)

theorem pairwise_lt_range' : ∀ s n : ℕ, pairwise (<) (range' s n)
| s 0     := pairwise.nil _
| s (n+1) := (chain_iff_pairwise (by exact λ a b c, lt_trans)).1 (chain_lt_range' s n)

theorem nodup_range' (s n : ℕ) : nodup (range' s n) :=
(pairwise_lt_range' s n).imp (λ a b, ne_of_lt)

theorem range'_append : ∀ s m n : ℕ, range' s m ++ range' (s+m) n = range' s (n+m)
| s 0     n := rfl
| s (m+1) n := show s :: (range' (s+1) m ++ range' (s+m+1) n) = s :: range' (s+1) (n+m),
               by rw [add_right_comm, range'_append]

theorem range'_sublist_right {s m n : ℕ} : range' s m <+ range' s n ↔ m ≤ n :=
⟨λ h, by simpa using length_le_of_sublist h,
 λ h, by rw [← nat.sub_add_cancel h, ← range'_append]; apply sublist_append_left⟩

theorem range'_subset_right {s m n : ℕ} : range' s m ⊆ range' s n ↔ m ≤ n :=
⟨λ h, le_of_not_lt $ λ hn, lt_irrefl (s+n) $
  (mem_range'.1 $ h $ mem_range'.2 ⟨le_add_right _ _, nat.add_lt_add_left hn s⟩).2,
 λ h, subset_of_sublist (range'_sublist_right.2 h)⟩

theorem range'_concat (s n : ℕ) : range' s (n + 1) = range' s n ++ [s+n] :=
by rw add_comm n 1; exact (range'_append s n 1).symm

theorem range_core_range' : ∀ s n : ℕ, range_core s (range' s n) = range' 0 (n + s)
| 0     n := rfl
| (s+1) n := by rw [show n+(s+1) = n+1+s, by simp]; exact range_core_range' s (n+1)

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
(range_core_range' n 0).trans $ by rw zero_add

@[simp] theorem length_range (n : ℕ) : length (range n) = n :=
by simp [range_eq_range']

theorem pairwise_lt_range (n : ℕ) : pairwise (<) (range n) :=
by simp [range_eq_range', pairwise_lt_range']

theorem nodup_range (n : ℕ) : nodup (range n) :=
by simp [range_eq_range', nodup_range']

theorem range_sublist {m n : ℕ} : range m <+ range n ↔ m ≤ n :=
by simp [range_eq_range', range'_sublist_right]

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
by simp [range_eq_range', range'_subset_right]

@[simp] theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
by simp [range_eq_range', zero_le]

@[simp] theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
mt mem_range.1 $ lt_irrefl _ 

theorem iota_eq_reverse_range' : ∀ n : ℕ, iota n = reverse (range' 1 n)
| 0     := rfl
| (n+1) := by simp [iota, range'_concat, iota_eq_reverse_range' n]

@[simp] theorem length_iota (n : ℕ) : length (iota n) = n :=
by simp [iota_eq_reverse_range']

theorem pairwise_gt_iota (n : ℕ) : pairwise (>) (iota n) :=
by simp [iota_eq_reverse_range', pairwise_lt_range']

theorem nodup_iota (n : ℕ) : nodup (iota n) :=
by simp [iota_eq_reverse_range', nodup_range']

theorem mem_iota {m n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n :=
by simp [iota_eq_reverse_range', lt_succ_iff]

@[simp] theorem enum_from_map_fst : ∀ n (l : list α),
  map prod.fst (enum_from n l) = range' n l.length
| n []       := rfl
| n (a :: l) := congr_arg (cons _) (enum_from_map_fst _ _)

@[simp] theorem enum_map_fst (l : list α) :
  map prod.fst (enum l) = range l.length :=
by simp [enum, range_eq_range']

end list
