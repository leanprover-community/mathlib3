/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.finset.basic

/-!
# The powerset of a finset
-/

namespace finset
open multiset

variables {α : Type*}

/-! ### powerset -/
section powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : finset α) : finset (finset α) :=
⟨s.1.powerset.pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset.1 h) s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset.2 s.2)⟩

@[simp] theorem mem_powerset {s t : finset α} : s ∈ powerset t ↔ s ⊆ t :=
by cases s; simp only [powerset, mem_mk, mem_pmap, mem_powerset, exists_prop, exists_eq_right];
  rw ← val_le_iff

@[simp] theorem empty_mem_powerset (s : finset α) : ∅ ∈ powerset s :=
mem_powerset.2 (empty_subset _)

@[simp] theorem mem_powerset_self (s : finset α) : s ∈ powerset s :=
mem_powerset.2 (subset.refl _)

@[simp] lemma powerset_empty : finset.powerset (∅ : finset α) = {∅} := rfl

@[simp] theorem powerset_mono {s t : finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
⟨λ h, (mem_powerset.1 $ h $ mem_powerset_self _),
 λ st u h, mem_powerset.2 $ subset.trans (mem_powerset.1 h) st⟩

@[simp] theorem card_powerset (s : finset α) :
  card (powerset s) = 2 ^ card s :=
(card_pmap _ _ _).trans (card_powerset s.1)

lemma not_mem_of_mem_powerset_of_not_mem {s t : finset α} {a : α}
  (ht : t ∈ s.powerset) (h : a ∉ s) : a ∉ t :=
by { apply mt _ h, apply mem_powerset.1 ht }

lemma powerset_insert [decidable_eq α] (s : finset α) (a : α) :
  powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) :=
begin
  ext t,
  simp only [exists_prop, mem_powerset, mem_image, mem_union, subset_insert_iff],
  by_cases h : a ∈ t,
  { split,
    { exact λH, or.inr ⟨_, H, insert_erase h⟩ },
    { intros H,
      cases H,
      { exact subset.trans (erase_subset a t) H },
      { rcases H with ⟨u, hu⟩,
        rw ← hu.2,
        exact subset.trans (erase_insert_subset a u) hu.1 } } },
  { have : ¬ ∃ (u : finset α), u ⊆ s ∧ insert a u = t,
      by simp [ne.symm (ne_insert_of_not_mem _ _ h)],
    simp [finset.erase_eq_of_not_mem h, this] }
end

end powerset

section powerset_len

/-- Given an integer `n` and a finset `s`, then `powerset_len n s` is the finset of subsets of `s`
of cardinality `n`.-/
def powerset_len (n : ℕ) (s : finset α) : finset (finset α) :=
⟨(s.1.powerset_len n).pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset_len.1 h).1 s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset_len s.2)⟩

theorem mem_powerset_len {n} {s t : finset α} :
  s ∈ powerset_len n t ↔ s ⊆ t ∧ card s = n :=
by cases s; simp [powerset_len, val_le_iff.symm]; refl

@[simp] theorem powerset_len_mono {n} {s t : finset α} (h : s ⊆ t) :
  powerset_len n s ⊆ powerset_len n t :=
λ u h', mem_powerset_len.2 $
  and.imp (λ h₂, subset.trans h₂ h) id (mem_powerset_len.1 h')

@[simp] theorem card_powerset_len (n : ℕ) (s : finset α) :
  card (powerset_len n s) = nat.choose (card s) n :=
(card_pmap _ _ _).trans (card_powerset_len n s.1)

end powerset_len
end finset
