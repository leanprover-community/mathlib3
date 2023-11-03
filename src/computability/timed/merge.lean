/-
Copyright (c) 2022 Tomaz Gomes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes
-/
import data.list.sort
import data.nat.log
import init.data.nat
import tactic.linarith
/-!
# Timed Merge
  This file defines a new version of Merge that, besides combining the input lists, counts the
  number of operations made through the execution of the algorithm. Also, it presents proofs of
  it's time complexity and it's equivalence to the one defined in data/list/sort.lean
## Main Definition
  - Timed.merge : list α → list α → (list α × ℕ)
## Main Results
  - Timed.merge_complexity :
      ∀ l₁ l₂ : list α, (Timed.merge l₁ l₂).snd ≤ l₁.length + l₂.length
  - Timed.merge_equivalence :
      ∀ l₁ l₂ : list α, (Timed.merge l₁ l₂).fst = list.merge l₁ l₂
-/

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace timed

include r

/-- `merge l₁ l₂` merges l₁ and l₂ into a sorted list, assuming both are
  already sorted. It also returns the number of operations performed. -/
@[simp] def merge : list α → list α → (list α × ℕ)
| []       l₂        := (l₂, 0)
| l₁        []       := (l₁,  0)
| (h₁ :: t₁) (h₂ :: t₂) := if h₁ ≼ h₂
                           then let (l₃, n) := merge t₁ (h₂ :: t₂)
                                in  (h₁ :: l₃, n + 1)
                           else let (l₃, n) := merge (h₁ :: t₁) t₂
                                in  (h₂ :: l₃, n + 1)

theorem merge_complexity : ∀ l₁ l₂ : list α,
  (merge r l₁ l₂).snd ≤ l₁.length + l₂.length
| []   []               := by { unfold merge, simp }
| []   (h₂ :: t₂)       := by { unfold merge, simp }
| (h₁ :: t₁)    []      := by { unfold merge, simp }
| (h₁ :: t₁) (h₂ :: t₂) :=
begin
  unfold merge, split_ifs,
  { have IH := merge_complexity t₁ (h₂ :: t₂),
    cases (merge r t₁ (h₂ :: t₂)) with l₁ l₂,
    unfold merge,
    simp only [list.length] at IH,
    simp only [list.length],
    linarith, },
  { have IH := merge_complexity (h₁ :: t₁) t₂,
    cases (merge r (h₁ :: t₁) t₂) with l₁ l₂,
    unfold merge,
    simp only [list.length] at IH,
    simp only [list.length],
    linarith, }
end

theorem merge_equivalence : ∀ l₁ l₂ : list α,
  (merge r l₁ l₂).fst = list.merge r l₁ l₂
| []       []         := by { unfold merge, unfold list.merge }
| []       (h' :: t') := by { unfold merge, unfold list.merge }
| (h :: t) []         := by { unfold merge, unfold list.merge }
| (h :: t) (h' :: t') :=
begin
  unfold merge,
  split_ifs,
  { have IH := merge_equivalence t (h' :: t'),
    cases (merge r t (h' :: t')) with l₁ l₂,
    unfold merge,

    unfold list.merge,
    split_ifs,
    exact ⟨ rfl, IH ⟩, },
  { have IH := merge_equivalence (h :: t) t',
    cases (merge r (h :: t) t') with l₁ l₂,
    unfold merge,

    unfold list.merge,
    split_ifs,
    exact ⟨ rfl, IH ⟩, }
end

end timed
