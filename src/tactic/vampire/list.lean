/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  List lemmas and definitions.
-/

import data.list.basic
import tactic.vampire.misc

universes u v

variables {α : Type u} {β : Type v}

namespace list

def remove_one [decidable_eq α] (a : α) (as : list α) : option (list α) :=
if as.index_of a < as.length
then some (as.remove_nth $ as.index_of a)
else none

lemma exists_mem_iff_exists_mem_map
  {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a : α, q (f a) ↔ p a) :
  ∀ as : list α, ((∃ b ∈ as.map f, q b) ↔ (∃ a ∈ as, p a))
| []        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (a :: as) :=
  begin
    rw [map_cons],
    simp only [exists_mem_cons_iff],
    apply pred_mono_2 (h _),
    apply exists_mem_iff_exists_mem_map
  end

def exteq [decidable_eq α] : list α → list α → Prop
| []        []       := true
| []        (_ :: _) := false
| (a :: l1) l2       :=
  match l2.remove_one a with
  | none       := false
  | (some l2') := exteq l1 l2'
  end

lemma mem_remove_nth {a : α}  :
  ∀ l : list α, ∀ k m : nat,
  l.nth m = some a → k ≠ m → a ∈ l.remove_nth k
| [] k m h0 h1 := by cases h0
| (b :: l) 0 m h0 h1 :=
  begin
    cases m, {cases h1 rfl},
    simp only [list.remove_nth],
    rw list.mem_iff_nth, use m,
    exact h0
  end
| (b :: l) (k + 1) m h0 h1 :=
  begin
    cases m,
    { apply or.inl (option.some.inj h0.symm) },
    have h2 : k ≠ m,
    { intro h2, rw h2 at h1, cases h1 rfl },
    apply or.inr (mem_remove_nth _ k m h0 h2)
  end

lemma mem_of_mem_remove_nth {a : α} :
  ∀ l : list α, ∀ k : nat, a ∈ l.remove_nth k → a ∈ l
| []       k h0 := by cases k; cases h0
| (b :: l) 0 h0 := or.inr h0
| (b :: l) (k + 1) h0 :=
  by { cases h0, {exact or.inl h0},
       apply or.inr (mem_of_mem_remove_nth l k h0) }

lemma mem_iff_nth_eq_some_or_mem_remove_nth
  {a : α} {l : list α} (k : nat) :
  a ∈ l ↔ (a ∈ l.remove_nth k ∨ l.nth k = some a) :=
begin
  constructor; intro h0,
  { rw @list.mem_iff_nth _ a l at h0,
    rcases h0 with ⟨m, h1⟩,
    by_cases h2 : k = m,
    { right, rwa ← h2 at h1 },
    left, apply mem_remove_nth _ _ _ h1 h2 },
  cases h0,
  { apply mem_of_mem_remove_nth _ _ h0 },
  rw @list.mem_iff_nth _ a l,
  refine ⟨k, h0⟩
end

lemma remove_one_subset [decidable_eq α] (a : α) (l1 l2 : list α) :
  l1.remove_one a = some l2 → l2 ⊆ l1 :=
begin
  unfold list.remove_one,
  by_cases l1.index_of a < l1.length,
  { rw if_pos h, intro h1,
    rw ← (option.some.inj h1),
    intros x h2,
    rw list.mem_iff_nth_eq_some_or_mem_remove_nth (l1.index_of a),
    left, assumption },
  rw if_neg h, rintro ⟨_⟩
end

lemma subset_of_exteq [decidable_eq α] :
  ∀ l1 l2 : list α, list.exteq l1 l2 → l1 ⊆ l2
| []        []       h0 x h1 := by cases h1
| []        (_ :: _) h0 x h1 := by cases h0
| (a :: l1) l2       h0 x h1 :=
  begin
    unfold list.exteq at h0,
    cases h2 : (l2.remove_one a) with l2',
    { rw h2 at h0, cases h0 },
    cases h1,
    { subst h1,
      unfold list.remove_one at h2,
      by_cases h3 : l2.index_of x < l2.length,
      { rw list.index_of_lt_length at h3, exact h3 },
      rw if_neg h3 at h2, cases h2 },
    rw h2 at h0,
    have h3 := subset_of_exteq _ _ h0,
    apply list.remove_one_subset _ _ _ h2 (h3 h1)
  end

instance decidable_exteq [decidable_eq α] :
  ∀ l1 l2 : list α, decidable (list.exteq l1 l2)
| []        []       := by { right, trivial }
| []        (_ :: _) := by { left, rintro ⟨_⟩ }
| (a :: l1) l2       :=
  begin
    unfold list.exteq,
    cases (l2.remove_one a),
    { left, rintro ⟨_⟩ },
    apply decidable_exteq,
  end

theorem exists_mem_append {p : α → Prop} {l₁ l₂ : list α} :
  (∃ x ∈ l₁ ++ l₂, p x) ↔ (∃ x ∈ l₁, p x) ∨ (∃ x ∈ l₂, p x) :=
begin
  constructor; intro h0,
  { rcases h0 with ⟨a, h1, h2⟩,
    rw list.mem_append at h1, cases h1,
    { left, refine ⟨_, h1, h2⟩ },
    right, refine ⟨_, h1, h2⟩ },
  cases h0; rcases h0 with ⟨a, h1, h2⟩;
  refine ⟨a, _, h2⟩; rw list.mem_append;
  [left, right]; assumption
end

def rot : nat → list α → list α
| _ [] := []
| 0 (a :: as) := (a :: as)
| (k + 1) (a :: as) :=
  match (as.rot k) with
  | [] := (a :: as)
  | (a' :: as') := (a' :: a :: as')
  end

lemma mem_rot {a : α} :
  ∀ {as : list α}, ∀ k : nat, a ∈ as → a ∈ as.rot k
| [] _ h0 := by cases h0
| (b :: as) 0 h0 := h0
| (b :: as) (k + 1) h0 :=
  begin
    cases h0; unfold rot;
    cases h1 : (as.rot k) with b' as',
    { left, assumption },
    { right, left, assumption },
    { right, assumption },
    have h2 := mem_rot _ h0,
    rw h1 at h2, cases h2,
    { left, assumption },
    right, right, assumption
  end

  #exit

lemma exists_mem_iff_exists_mem_map
  {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a : α, p a ↔ q (f a)) :
  ∀ as : list α, ((∃ a ∈ as, p a) ↔ (∃ b ∈ as.map f, q b))
| []        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (a :: as) :=
  begin
    rw [map_cons],
    simp only [exists_mem_cons_iff],
    apply pred_mono_2 (h _),
    apply exists_mem_iff_exists_mem_map
  end

lemma forall_mem_iff_forall_mem_map
  {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a : α, p a ↔ q (f a)) :
  ∀ as : list α, ((∀ a ∈ as, p a) ↔ (∀ b ∈ as.map f, q b))
| []        := by constructor; intro; apply forall_mem_nil
| (a :: as) :=
  begin
    rw [map_cons],
    simp only [forall_mem_cons],
    apply pred_mono_2 (h _),
    apply forall_mem_iff_forall_mem_map
  end


def halve (l : list α) : list α × list α :=
split_at (l.length / 2) l

end list


#exit
universes u v

variables {α : Type u} {β : Type v}

namespace list

open option

lemma exists_mem_iff_exists_mem_map
  {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a : α, p a ↔ q (f a)) :
  ∀ as : list α, ((∃ a ∈ as, p a) ↔ (∃ b ∈ as.map f, q b))
| []        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (a :: as) :=
  begin
    rw [map_cons],
    simp only [exists_mem_cons_iff],
    apply pred_mono_2 (h _),
    apply exists_mem_iff_exists_mem_map
  end

lemma forall_mem_iff_forall_mem_map
  {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a : α, p a ↔ q (f a)) :
  ∀ as : list α, ((∀ a ∈ as, p a) ↔ (∀ b ∈ as.map f, q b))
| []        := by constructor; intro; apply forall_mem_nil
| (a :: as) :=
  begin
    rw [map_cons],
    simp only [forall_mem_cons],
    apply pred_mono_2 (h _),
    apply forall_mem_iff_forall_mem_map
  end


lemma mem_remove_nth {a : α}  :
  ∀ l : list α, ∀ k m : nat,
  l.nth m = some a → k ≠ m → a ∈ l.remove_nth k
| [] k m h0 h1 := by cases h0
| (b :: l) 0 m h0 h1 :=
  begin
    cases m, {cases h1 rfl},
    simp only [list.remove_nth],
    rw list.mem_iff_nth, use m,
    exact h0
  end
| (b :: l) (k + 1) m h0 h1 :=
  begin
    cases m,
    { apply or.inl (option.some.inj h0.symm) },
    have h2 : k ≠ m,
    { intro h2, rw h2 at h1, cases h1 rfl },
    apply or.inr (mem_remove_nth _ k m h0 h2)
  end

lemma mem_of_mem_remove_nth {a : α} :
  ∀ l : list α, ∀ k : nat, a ∈ l.remove_nth k → a ∈ l
| []       k h0 := by cases k; cases h0
| (b :: l) 0 h0 := or.inr h0
| (b :: l) (k + 1) h0 :=
  by { cases h0, {exact or.inl h0},
       apply or.inr (mem_of_mem_remove_nth l k h0) }

lemma mem_iff_nth_eq_some_or_mem_remove_nth
  {a : α} {l : list α} (k : nat) :
  a ∈ l ↔ (a ∈ l.remove_nth k ∨ l.nth k = some a) :=
begin
  constructor; intro h0,
  { rw @list.mem_iff_nth _ a l at h0,
    rcases h0 with ⟨m, h1⟩,
    by_cases h2 : k = m,
    { right, rwa ← h2 at h1 },
    left, apply mem_remove_nth _ _ _ h1 h2 },
  cases h0,
  { apply mem_of_mem_remove_nth _ _ h0 },
  rw @list.mem_iff_nth _ a l,
  refine ⟨k, h0⟩
end

def remove_one [decidable_eq α] (a : α) (as : list α) : option (list α) :=
if as.index_of a < as.length
then some (as.remove_nth $ as.index_of a)
else none

/- Equivalent to perm, but includes no axioms -/

def exteq [decidable_eq α] : list α → list α → Prop
| []        []       := true
| []        (_ :: _) := false
| (a :: l1) l2       :=
  match l2.remove_one a with
  | none       := false
  | (some l2') := exteq l1 l2'
  end

lemma remove_one_subset [decidable_eq α] (a : α) (l1 l2 : list α) :
  l1.remove_one a = some l2 → l2 ⊆ l1 :=
begin
  unfold list.remove_one,
  by_cases l1.index_of a < l1.length,
  { rw if_pos h, intro h1,
    rw ← (option.some.inj h1),
    intros x h2,
    rw list.mem_iff_nth_eq_some_or_mem_remove_nth (l1.index_of a),
    left, assumption },
  rw if_neg h, rintro ⟨_⟩
end

lemma subset_of_exteq [decidable_eq α] :
  ∀ l1 l2 : list α, list.exteq l1 l2 → l1 ⊆ l2
| []        []       h0 x h1 := by cases h1
| []        (_ :: _) h0 x h1 := by cases h0
| (a :: l1) l2       h0 x h1 :=
  begin
    unfold list.exteq at h0,
    cases h2 : (l2.remove_one a) with l2',
    { rw h2 at h0, cases h0 },
    cases h1,
    { subst h1,
      unfold list.remove_one at h2,
      by_cases h3 : l2.index_of x < l2.length,
      { rw list.index_of_lt_length at h3, exact h3 },
      rw if_neg h3 at h2, cases h2 },
    rw h2 at h0,
    have h3 := subset_of_exteq _ _ h0,
    apply list.remove_one_subset _ _ _ h2 (h3 h1)
  end

instance decidable_exteq [decidable_eq α] :
  ∀ l1 l2 : list α, decidable (list.exteq l1 l2)
| []        []       := by { right, trivial }
| []        (_ :: _) := by { left, rintro ⟨_⟩ }
| (a :: l1) l2       :=
  begin
    unfold list.exteq,
    cases (l2.remove_one a),
    { left, rintro ⟨_⟩ },
    apply decidable_exteq,
  end

end list
