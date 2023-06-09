/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import data.list.infix

/-!
# Double universal quantification on a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides an API for `list.forall₂` (definition in `data.list.defs`).
`forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length, and whenever `a` is the nth element
of `l₁`, and `b` is the nth element of `l₂`, then `R a b` is satisfied.
-/

open nat function

namespace list

variables {α β γ δ : Type*} {R S : α → β → Prop} {P : γ → δ → Prop} {Rₐ : α → α → Prop}
open relator

mk_iff_of_inductive_prop list.forall₂ list.forall₂_iff

@[simp] theorem forall₂_cons {a b l₁ l₂} :
  forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ forall₂ R l₁ l₂ :=
⟨λ h, by cases h with h₁ h₂; split; assumption, λ ⟨h₁, h₂⟩, forall₂.cons h₁ h₂⟩

theorem forall₂.imp
  (H : ∀ a b, R a b → S a b) {l₁ l₂}
  (h : forall₂ R l₁ l₂) : forall₂ S l₁ l₂ :=
by induction h; constructor; solve_by_elim

lemma forall₂.mp {Q : α → β → Prop} (h : ∀ a b, Q a b → R a b → S a b) :
  ∀ {l₁ l₂}, forall₂ Q l₁ l₂ → forall₂ R l₁ l₂ → forall₂ S l₁ l₂
| []        []        forall₂.nil           forall₂.nil           := forall₂.nil
| (a :: l₁) (b :: l₂) (forall₂.cons hr hrs) (forall₂.cons hq hqs) :=
  forall₂.cons (h a b hr hq) (forall₂.mp hrs hqs)

lemma forall₂.flip : ∀ {a b}, forall₂ (flip R) b a → forall₂ R a b
| _ _                 forall₂.nil          := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := forall₂.cons h₁ h₂.flip

@[simp] lemma forall₂_same : ∀ {l : list α}, forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
| [] := by simp
| (a :: l) := by simp [@forall₂_same l]

lemma forall₂_refl [is_refl α Rₐ] (l : list α) : forall₂ Rₐ l l :=
forall₂_same.2 $ λ a h, refl _

@[simp] lemma forall₂_eq_eq_eq : forall₂ ((=) : α → α → Prop) = (=) :=
begin
  funext a b, apply propext,
  split,
  { intro h, induction h, {refl}, simp only [*]; split; refl },
  { rintro rfl, exact forall₂_refl _ }
end

@[simp, priority 900] lemma forall₂_nil_left_iff {l} : forall₂ R nil l ↔ l = nil :=
⟨λ H, by cases H; refl, by rintro rfl; exact forall₂.nil⟩

@[simp, priority 900] lemma forall₂_nil_right_iff {l} : forall₂ R l nil ↔ l = nil :=
⟨λ H, by cases H; refl, by rintro rfl; exact forall₂.nil⟩

lemma forall₂_cons_left_iff {a l u} :
  forall₂ R (a :: l) u ↔ (∃b u', R a b ∧ forall₂ R l u' ∧ u = b :: u') :=
iff.intro
  (λ h, match u, h with (b :: u'), forall₂.cons h₁ h₂ := ⟨b, u', h₁, h₂, rfl⟩ end)
  (λ h, match u, h with _, ⟨b, u', h₁, h₂, rfl⟩ := forall₂.cons h₁ h₂ end)

lemma forall₂_cons_right_iff {b l u} :
  forall₂ R u (b :: l) ↔ (∃a u', R a b ∧ forall₂ R u' l ∧ u = a :: u') :=
iff.intro
  (λ h, match u, h with (b :: u'), forall₂.cons h₁ h₂ := ⟨b, u', h₁, h₂, rfl⟩ end)
  (λ h, match u, h with _, ⟨b, u', h₁, h₂, rfl⟩ := forall₂.cons h₁ h₂ end)

lemma forall₂_and_left {p : α → Prop} :
  ∀ l u, forall₂ (λa b, p a ∧ R a b) l u ↔ (∀ a∈l, p a) ∧ forall₂ R l u
| []     u := by simp only [forall₂_nil_left_iff, forall_prop_of_false (not_mem_nil _),
    imp_true_iff, true_and]
| (a :: l) u := by simp only [forall₂_and_left l, forall₂_cons_left_iff, forall_mem_cons,
    and_assoc, and_comm, and.left_comm, exists_and_distrib_left.symm]

@[simp] lemma forall₂_map_left_iff {f : γ → α} :
  ∀ {l u}, forall₂ R (map f l) u ↔ forall₂ (λc b, R (f c) b) l u
| []     _ := by simp only [map, forall₂_nil_left_iff]
| (a :: l) _ := by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp] lemma forall₂_map_right_iff {f : γ → β} :
  ∀ {l u}, forall₂ R l (map f u) ↔ forall₂ (λa c, R a (f c)) l u
| _ []     := by simp only [map, forall₂_nil_right_iff]
| _ (b :: u) := by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]

lemma left_unique_forall₂' (hr : left_unique R) :
  ∀ {a b c}, forall₂ R a c → forall₂ R b c → a = b
| a₀ nil a₁ forall₂.nil forall₂.nil := rfl
| (a₀ :: l₀) (b :: l) (a₁ :: l₁) (forall₂.cons ha₀ h₀) (forall₂.cons ha₁ h₁) :=
  hr ha₀ ha₁ ▸ left_unique_forall₂' h₀ h₁ ▸ rfl

lemma _root_.relator.left_unique.forall₂ (hr : left_unique R) : left_unique (forall₂ R) :=
@left_unique_forall₂' _ _ _ hr

lemma right_unique_forall₂' (hr : right_unique R) : ∀ {a b c}, forall₂ R a b → forall₂ R a c → b = c
| nil a₀ a₁ forall₂.nil forall₂.nil := rfl
| (b :: l) (a₀ :: l₀) (a₁ :: l₁) (forall₂.cons ha₀ h₀) (forall₂.cons ha₁ h₁) :=
  hr ha₀ ha₁ ▸ right_unique_forall₂' h₀ h₁ ▸ rfl

lemma _root_.relator.right_unique.forall₂ (hr : right_unique R) : right_unique (forall₂ R) :=
@right_unique_forall₂' _ _ _ hr

lemma _root_.relator.bi_unique.forall₂ (hr : bi_unique R) : bi_unique (forall₂ R) :=
⟨hr.left.forall₂, hr.right.forall₂⟩

theorem forall₂.length_eq :
  ∀ {l₁ l₂}, forall₂ R l₁ l₂ → length l₁ = length l₂
| _ _ forall₂.nil          := rfl
| _ _ (forall₂.cons h₁ h₂) := congr_arg succ (forall₂.length_eq h₂)

theorem forall₂.nth_le :
  ∀ {x : list α} {y : list β} (h : forall₂ R x y) ⦃i : ℕ⦄ (hx : i < x.length) (hy : i < y.length),
      R (x.nth_le i hx) (y.nth_le i hy)
| (a₁ :: l₁) (a₂ :: l₂) (forall₂.cons ha hl) 0        hx hy := ha
| (a₁ :: l₁) (a₂ :: l₂) (forall₂.cons ha hl) (succ i) hx hy := hl.nth_le _ _

lemma forall₂_of_length_eq_of_nth_le : ∀ {x : list α} {y : list β},
  x.length = y.length → (∀ i h₁ h₂, R (x.nth_le i h₁) (y.nth_le i h₂)) → forall₂ R x y
| []         []         hl h := forall₂.nil
| (a₁ :: l₁) (a₂ :: l₂) hl h := forall₂.cons
    (h 0 (nat.zero_lt_succ _) (nat.zero_lt_succ _))
    (forall₂_of_length_eq_of_nth_le (succ.inj hl) (
      λ i h₁ h₂, h i.succ (succ_lt_succ h₁) (succ_lt_succ h₂)))

theorem forall₂_iff_nth_le {l₁ : list α} {l₂ : list β} :
  forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧ ∀ i h₁ h₂, R (l₁.nth_le i h₁) (l₂.nth_le i h₂) :=
⟨λ h, ⟨h.length_eq, h.nth_le⟩, and.rec forall₂_of_length_eq_of_nth_le⟩

theorem forall₂_zip :
  ∀ {l₁ l₂}, forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b
| _ _ (forall₂.cons h₁ h₂) x y (or.inl rfl) := h₁
| _ _ (forall₂.cons h₁ h₂) x y (or.inr h₃) := forall₂_zip h₂ h₃

theorem forall₂_iff_zip {l₁ l₂} : forall₂ R l₁ l₂ ↔
  length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b :=
⟨λ h, ⟨forall₂.length_eq h, @forall₂_zip _ _ _ _ _ h⟩,
 λ h, begin
  cases h with h₁ h₂,
  induction l₁ with a l₁ IH generalizing l₂,
  { cases length_eq_zero.1 h₁.symm, constructor },
  { cases l₂ with b l₂; injection h₁ with h₁,
    exact forall₂.cons (h₂ $ or.inl rfl) (IH h₁ $ λ a b h, h₂ $ or.inr h) }
end⟩

theorem forall₂_take :
  ∀ n {l₁ l₂}, forall₂ R l₁ l₂ → forall₂ R (take n l₁) (take n l₂)
| 0 _ _ _ := by simp only [forall₂.nil, take]
| (n+1) _ _ (forall₂.nil) := by simp only [forall₂.nil, take]
| (n+1) _ _ (forall₂.cons h₁ h₂) := by simp [and.intro h₁ h₂, forall₂_take n]

theorem forall₂_drop :
  ∀ n {l₁ l₂}, forall₂ R l₁ l₂ → forall₂ R (drop n l₁) (drop n l₂)
| 0 _ _ h := by simp only [drop, h]
| (n+1) _ _ (forall₂.nil) := by simp only [forall₂.nil, drop]
| (n+1) _ _ (forall₂.cons h₁ h₂) := by simp [and.intro h₁ h₂, forall₂_drop n]

theorem forall₂_take_append (l : list α) (l₁ : list β) (l₂ : list β)
  (h : forall₂ R l (l₁ ++ l₂)) : forall₂ R (list.take (length l₁) l) l₁ :=
have h': forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)),
from forall₂_take (length l₁) h,
by rwa [take_left] at h'

theorem forall₂_drop_append (l : list α) (l₁ : list β) (l₂ : list β)
  (h : forall₂ R l (l₁ ++ l₂)) : forall₂ R (list.drop (length l₁) l) l₂ :=
have h': forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)),
from forall₂_drop (length l₁) h,
by rwa [drop_left] at h'

lemma rel_mem (hr : bi_unique R) : (R ⇒ forall₂ R ⇒ iff) (∈) (∈)
| a b h [] [] forall₂.nil := by simp only [not_mem_nil]
| a b h (a' :: as) (b' :: bs) (forall₂.cons h₁ h₂) := rel_or (rel_eq hr h h₁) (rel_mem h h₂)

lemma rel_map : ((R ⇒ P) ⇒ forall₂ R ⇒ forall₂ P) map map
| f g h [] [] forall₂.nil := forall₂.nil
| f g h (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := forall₂.cons (h h₁) (rel_map @h h₂)

lemma rel_append : (forall₂ R ⇒ forall₂ R ⇒ forall₂ R) append append
| [] [] h l₁ l₂ hl := hl
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) l₁ l₂ hl := forall₂.cons h₁ (rel_append h₂ hl)

lemma rel_reverse : (forall₂ R ⇒ forall₂ R) reverse reverse
| [] [] forall₂.nil := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := begin
  simp only [reverse_cons],
  exact rel_append (rel_reverse h₂) (forall₂.cons h₁ forall₂.nil)
end

@[simp]
lemma forall₂_reverse_iff {l₁ l₂} : forall₂ R (reverse l₁) (reverse l₂) ↔ forall₂ R l₁ l₂ :=
iff.intro
  (λ h, by { rw [← reverse_reverse l₁, ← reverse_reverse l₂], exact rel_reverse h })
  (λ h, rel_reverse h)

lemma rel_join : (forall₂ (forall₂ R) ⇒ forall₂ R) join join
| [] [] forall₂.nil := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := rel_append h₁ (rel_join h₂)

lemma rel_bind : (forall₂ R ⇒ (R ⇒ forall₂ P) ⇒ forall₂ P) list.bind list.bind :=
λ a b h₁ f g h₂, rel_join (rel_map @h₂ h₁)

lemma rel_foldl : ((P ⇒ R ⇒ P) ⇒ P ⇒ forall₂ R ⇒ P) foldl foldl
| f g hfg _ _ h _ _ forall₂.nil := h
| f g hfg x y hxy _ _ (forall₂.cons hab hs) := rel_foldl @hfg (hfg hxy hab) hs

lemma rel_foldr : ((R ⇒ P ⇒ P) ⇒ P ⇒ forall₂ R ⇒ P) foldr foldr
| f g hfg _ _ h _ _ forall₂.nil := h
| f g hfg x y hxy _ _ (forall₂.cons hab hs) := hfg hab (rel_foldr @hfg hxy hs)

lemma rel_filter {p : α → Prop} {q : β → Prop} [decidable_pred p] [decidable_pred q]
  (hpq : (R ⇒ (↔)) p q) :
  (forall₂ R ⇒ forall₂ R) (filter p) (filter q)
| _ _ forall₂.nil := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) :=
  begin
    by_cases p a,
    { have : q b, { rwa [← hpq h₁] },
      simp only [filter_cons_of_pos _ h, filter_cons_of_pos _ this, forall₂_cons, h₁, rel_filter h₂,
        and_true], },
    { have : ¬ q b, { rwa [← hpq h₁] },
      simp only [filter_cons_of_neg _ h, filter_cons_of_neg _ this, rel_filter h₂], },
  end

lemma rel_filter_map : ((R ⇒ option.rel P) ⇒ forall₂ R ⇒ forall₂ P) filter_map filter_map
| f g hfg _ _ forall₂.nil := forall₂.nil
| f g hfg (a :: as) (b :: bs) (forall₂.cons h₁ h₂) :=
  by rw [filter_map_cons, filter_map_cons];
  from match f a, g b, hfg h₁ with
  | _, _, option.rel.none := rel_filter_map @hfg h₂
  | _, _, option.rel.some h := forall₂.cons h (rel_filter_map @hfg h₂)
  end

@[to_additive]
lemma rel_prod [monoid α] [monoid β]
  (h : R 1 1) (hf : (R ⇒ R ⇒ R) (*) (*)) : (forall₂ R ⇒ R) prod prod :=
rel_foldl hf h

/-- Given a relation `R`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublist of `l₂` such
  that `forall₂ r l₁ l₂`. -/
inductive sublist_forall₂ (R : α → β → Prop) : list α → list β → Prop
| nil {l} : sublist_forall₂ [] l
| cons {a₁ a₂ l₁ l₂} : R a₁ a₂ → sublist_forall₂ l₁ l₂ →
  sublist_forall₂ (a₁ :: l₁) (a₂ :: l₂)
| cons_right {a l₁ l₂} : sublist_forall₂ l₁ l₂ → sublist_forall₂ l₁ (a :: l₂)

lemma sublist_forall₂_iff {l₁ : list α} {l₂ : list β} :
  sublist_forall₂ R l₁ l₂ ↔ ∃ l, forall₂ R l₁ l ∧ l <+ l₂ :=
begin
  split; intro h,
  { induction h with _ a b l1 l2 rab rll ih b l1 l2 hl ih,
    { exact ⟨nil, forall₂.nil, nil_sublist _⟩ },
    { obtain ⟨l, hl1, hl2⟩ := ih,
      refine ⟨b :: l, forall₂.cons rab hl1, hl2.cons_cons b⟩ },
    { obtain ⟨l, hl1, hl2⟩ := ih,
      exact ⟨l, hl1, hl2.trans (sublist.cons _ _ _ (sublist.refl _))⟩ } },
  { obtain ⟨l, hl1, hl2⟩ := h,
    revert l₁,
    induction hl2 with _ _ _ _ ih _ _ _ _ ih; intros l₁ hl1,
    { rw [forall₂_nil_right_iff.1 hl1],
      exact sublist_forall₂.nil },
    { exact sublist_forall₂.cons_right (ih hl1) },
    { cases hl1 with _ _ _ _ hr hl _,
      exact sublist_forall₂.cons hr (ih hl) } }
end

instance sublist_forall₂.is_refl [is_refl α Rₐ] :
  is_refl (list α) (sublist_forall₂ Rₐ) :=
⟨λ l, sublist_forall₂_iff.2 ⟨l, forall₂_refl l, sublist.refl l⟩⟩

instance sublist_forall₂.is_trans [is_trans α Rₐ] :
  is_trans (list α) (sublist_forall₂ Rₐ) :=
⟨λ a b c, begin
  revert a b,
  induction c with _ _ ih,
  { rintros _ _ h1 (_ | _ | _),
    exact h1 },
  { rintros a b h1 h2,
    cases h2 with _ _ _ _ _ hbc tbc _ _ y1 btc,
    { cases h1,
      exact sublist_forall₂.nil },
    { cases h1 with _ _ _ _ _ hab tab _ _ _ atb,
      { exact sublist_forall₂.nil },
      { exact sublist_forall₂.cons (trans hab hbc) (ih _ _ tab tbc) },
      { exact sublist_forall₂.cons_right (ih _ _ atb tbc) } },
    { exact sublist_forall₂.cons_right (ih _ _ h1 btc), } }
end⟩

lemma sublist.sublist_forall₂ {l₁ l₂ : list α} (h : l₁ <+ l₂) [is_refl α Rₐ] :
  sublist_forall₂ Rₐ l₁ l₂ :=
sublist_forall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩

lemma tail_sublist_forall₂_self [is_refl α Rₐ] (l : list α) :
  sublist_forall₂ Rₐ l.tail l :=
l.tail_sublist.sublist_forall₂

end list
