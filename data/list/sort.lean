/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Insertion sort and merge sort.
-/
import data.list.perm
open list.perm

namespace list

section sorted
universe variable uu
variables {α : Type uu} {r : α → α → Prop}

def sorted := @pairwise

@[simp] theorem sorted_nil : sorted r [] := pairwise.nil _

@[simp] theorem sorted_singleton (a : α) : sorted r [a] := pairwise_singleton _ _

theorem sorted_of_sorted_cons {a : α} {l : list α} : sorted r (a :: l) → sorted r l :=
pairwise_of_pairwise_cons

theorem rel_of_sorted_cons {a : α} {l : list α} : sorted r (a :: l) →
  ∀ b ∈ l, r a b :=
rel_of_pairwise_cons

@[simp] theorem sorted_cons {a : α} {l : list α} :
  sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ sorted r l :=
pairwise_cons

theorem eq_of_sorted_of_perm (tr : transitive r) (anti : anti_symmetric r)
  {l₁ l₂ : list α} (p : l₁ ~ l₂) (s₁ : sorted r l₁) (s₂ : sorted r l₂) : l₁ = l₂ :=
begin
  induction s₁ with a l₁ h₁ s₁ IH generalizing l₂,
  { rw eq_nil_of_perm_nil p },
  { have : a ∈ l₂ := mem_of_perm p (mem_cons_self _ _),
    rcases mem_split this with ⟨u₂, v₂, e⟩, subst e,
    have p' := (perm_cons a).1 (p.trans perm_middle),
    have := IH p' (pairwise_of_sublist (by simp) s₂), subst l₁,
    change a::u₂ ++ v₂ = u₂ ++ ([a] ++ v₂), rw ← append_assoc, congr,
    have : ∀ (x : α) (h : x ∈ u₂), x = a := λ x m,
      anti ((pairwise_append.1 s₂).2.2 _ m a (mem_cons_self _ _))
        (h₁ _ (by simp [m])),
    rw [(@eq_repeat _ a (length u₂ + 1) (a::u₂)).2,
        (@eq_repeat _ a (length u₂ + 1) (u₂++[a])).2];
    split; simp [iff_true_intro this] }
end

end sorted

/-
  sorting procedures
-/

section sort
universe variable uu
parameters {α : Type uu} (r : α → α → Prop) [decidable_rel r]
local infix `≼` : 50 := r

/- insertion sort -/

section insertion_sort

@[simp] def ordered_insert (a : α) : list α → list α
| []       := [a]
| (b :: l) := if a ≼ b then a :: b :: l else b :: ordered_insert l

@[simp] def insertion_sort : list α → list α
| []       := []
| (b :: l) := ordered_insert b (insertion_sort l)

section correctness
parameter [deceqα : decidable_eq α]
include deceqα
open perm

theorem perm_ordered_insert (a) : ∀ l : list α, ordered_insert a l ~ a :: l
| []       := perm.refl _
| (b :: l) := by by_cases a ≼ b; [simp [ordered_insert, h],
  simpa [ordered_insert, h] using
    (perm.skip _ (perm_ordered_insert l)).trans (perm.swap _ _ _)]

theorem perm_insertion_sort : ∀ l : list α, insertion_sort l ~ l
| []       := perm.nil
| (b :: l) := by simpa [insertion_sort] using
  (perm_ordered_insert _ _ _).trans (perm.skip b (perm_insertion_sort l))

section total_and_transitive
variables (totr : total r) (transr : transitive r)
include totr transr

theorem sorted_ordered_insert (a : α) : ∀ l, sorted r l → sorted r (ordered_insert a l)
| []       h := sorted_singleton a
| (b :: l) h := begin
  by_cases a ≼ b with h',
  { simpa [ordered_insert, h', h] using λ b' bm, transr h' (rel_of_sorted_cons h _ bm) },
  { suffices : ∀ (b' : α), b' ∈ ordered_insert r a l → r b b',
    { simpa [ordered_insert, h', sorted_ordered_insert l (sorted_of_sorted_cons h)] },
    intros b' bm,
    cases (show b' = a ∨ b' ∈ l, by simpa using
      mem_of_perm (perm_ordered_insert _ _ _) bm) with be bm,
    { subst b', exact (totr _ _).resolve_left h' },
    { exact rel_of_sorted_cons h _ bm } }
end

theorem sorted_insertion_sort : ∀ l, sorted r (insertion_sort l)
| []       := sorted_nil
| (a :: l) := sorted_ordered_insert totr transr a _ (sorted_insertion_sort l)

end total_and_transitive
end correctness
end insertion_sort

/- merge sort -/

section merge_sort

-- TODO(Jeremy): observation: if instead we write (a :: (split l).1, b :: (split l).2), the
-- equation compiler can't prove the third equation

def split : list α → list α × list α
| []            := ([], [])
| (a :: l) := let (l₁, l₂) := split l in (a :: l₂, l₁)
attribute [simp] split

theorem split_cons_of_eq (a : α) {l l₁ l₂ : list α} (h : split l = (l₁, l₂)) :
  split (a :: l) = (a :: l₂, l₁) :=
by rw [split, h]; refl

theorem length_split_le : ∀ {l l₁ l₂ : list α},
  split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
| []     ._  ._  rfl := ⟨nat.le_refl 0, nat.le_refl 0⟩
| (a::l) l₁' l₂' h   := begin
  cases e : split l with l₁ l₂,
  injection (split_cons_of_eq _ e).symm.trans h, substs l₁' l₂',
  cases length_split_le e with h₁ h₂,
  exact ⟨nat.succ_le_succ h₂, nat.le_succ_of_le h₁⟩
end

theorem length_split_lt {a b} {l l₁ l₂ : list α} (h : split (a::b::l) = (l₁, l₂)) :
  length l₁ < length (a::b::l) ∧ length l₂ < length (a::b::l) :=
begin
  cases e : split l with l₁' l₂',
  injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h, substs l₁ l₂,
  cases length_split_le e with h₁ h₂,
  exact ⟨nat.succ_le_succ (nat.succ_le_succ h₁), nat.succ_le_succ (nat.succ_le_succ h₂)⟩
end

theorem perm_split : ∀ {l l₁ l₂ : list α}, split l = (l₁, l₂) → l ~ l₁ ++ l₂
| []     ._  ._  rfl := perm.refl _
| (a::l) l₁' l₂' h   := begin
  cases e : split l with l₁ l₂,
  injection (split_cons_of_eq _ e).symm.trans h, substs l₁' l₂',
  exact perm.skip a ((perm_split e).trans perm_app_comm),
end

def merge : list α → list α → list α
| []       l'        := l'
| l        []        := l
| (a :: l) (b :: l') := if a ≼ b then a :: merge l (b :: l') else b :: merge (a :: l) l'

include r
def merge_sort : list α → list α
| []        := []
| [a]       := [a]
| (a::b::l) := begin
  cases e : split (a::b::l) with l₁ l₂,
  cases length_split_lt e with h₁ h₂,
  exact merge r (merge_sort l₁) (merge_sort l₂)
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

theorem merge_sort_cons_cons {a b} {l l₁ l₂ : list α}
  (h : split (a::b::l) = (l₁, l₂)) :
  merge_sort (a::b::l) = merge (merge_sort l₁) (merge_sort l₂) :=
begin
  suffices : ∀ (L : list α) h1, @@and.rec
    (λ a a (_ : length l₁ < length l + 1 + 1 ∧
      length l₂ < length l + 1 + 1), L) h1 h1 = L,
  { simp [merge_sort, h], apply this },
  intros, cases h1, refl
end

section correctness
parameter [deceqα : decidable_eq α]
include deceqα

theorem perm_merge : ∀ (l l' : list α), merge l l' ~ l ++ l'
| []       []        := perm.nil
| []       (b :: l') := by simp [merge]
| (a :: l) []        := by simp [merge]
| (a :: l) (b :: l') := begin
  by_cases a ≼ b,
  { simpa [merge, h] using skip _ (perm_merge _ _) },
  { suffices : b :: merge r (a :: l) l' ~ a :: (l ++ b :: l'), {simpa [merge, h]},
    exact (skip _ (perm_merge _ _)).trans ((swap _ _ _).trans (skip _ perm_middle.symm)) }
end

theorem perm_merge_sort : ∀ l : list α, merge_sort l ~ l
| []        := perm.refl _
| [a]       := perm.refl _
| (a::b::l) := begin
  cases e : split (a::b::l) with l₁ l₂,
  cases length_split_lt e with h₁ h₂,
  rw [merge_sort_cons_cons r e],
  apply (perm_merge r _ _).trans,
  exact (perm_app (perm_merge_sort l₁) (perm_merge_sort l₂)).trans (perm_split e).symm
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

section total_and_transitive
variables (totr : total r) (transr : transitive r)
include totr transr

theorem sorted_merge : ∀ {l l' : list α}, sorted r l → sorted r l' → sorted r (merge l l')
| []       []        h₁ h₂ := sorted_nil
| []       (b :: l') h₁ h₂ := by simpa [merge] using h₂
| (a :: l) []        h₁ h₂ := by simpa [merge] using h₁
| (a :: l) (b :: l') h₁ h₂ := begin
  by_cases a ≼ b,
  { suffices : ∀ (b' : α) (_ : b' ∈ merge r l (b :: l')), r a b',
    { simpa [merge, h, sorted_merge (sorted_of_sorted_cons h₁) h₂] },
    intros b' bm,
    rcases (show b' = b ∨ b' ∈ l ∨ b' ∈ l', by simpa using
      mem_of_perm (perm_merge _ _ _) bm) with be | bl | bl',
    { subst b', assumption },
    { exact rel_of_sorted_cons h₁ _ bl },
    { exact transr h (rel_of_sorted_cons h₂ _ bl') } },
  { suffices : ∀ (b' : α) (_ : b' ∈ merge r (a :: l) l'), r b b',
    { simpa [merge, h, sorted_merge h₁ (sorted_of_sorted_cons h₂)] },
    intros b' bm,
    have ba : b ≼ a := (totr _ _).resolve_left h,
    rcases (show b' = a ∨ b' ∈ l ∨ b' ∈ l', by simpa using
      mem_of_perm (perm_merge _ _ _) bm) with be | bl | bl',
    { subst b', assumption },
    { exact transr ba (rel_of_sorted_cons h₁ _ bl) },
    { exact rel_of_sorted_cons h₂ _ bl' } }
end

theorem sorted_merge_sort : ∀ l : list α, sorted r (merge_sort l)
| []        := sorted_nil
| [a]       := sorted_singleton _
| (a::b::l) := begin
  cases e : split (a::b::l) with l₁ l₂,
  cases length_split_lt e with h₁ h₂,
  rw [merge_sort_cons_cons r e],
  exact sorted_merge r totr transr (sorted_merge_sort l₁) (sorted_merge_sort l₂)
end
using_well_founded {
  rel_tac := λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac := tactic.assumption }

end total_and_transitive
end correctness
end merge_sort
end sort

/- try them out! -/

--#eval insertion_sort (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

--#eval merge_sort     (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

end list
