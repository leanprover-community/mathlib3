/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johan Commelin, Scott Morrison
-/
import data.fintype.basic

/-!
# The fiber over a point, when the domain is a fintype.

We define the fiber of a function `f : α → β` over a point `b : β`, when we have `fintype α`,
as a `finset α`, and prove some basic properties.
-/

open function

namespace fintype
/--
The fiber of function `f : α → β` over a point `b : β` is a `finset α` when we have `fintype α`.
-/
def fiber {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) : finset α :=
set.to_finset { a | f a = b }

@[simp]
lemma mem_fiber {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) (a : α) :
  a ∈ fintype.fiber f b ↔ f a = b :=
by simp [fiber]

@[simp]
lemma card_fiber {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) :
  finset.card (fiber f b) = fintype.card { a | f a = b } :=
set.to_finset_card { a | f a = b }

lemma fibers_disjoint {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [decidable_eq β] (f : α → β) (b₁ b₂ : β) (h : b₁ ≠ b₂) :
  disjoint (fiber f b₁) (fiber f b₂) :=
begin
  dsimp [disjoint],
  rintros a w,
  simp [fiber] at w,
  exact false.elim (h (w.1.symm.trans w.2))
end

@[simp]
lemma fiber_prod_fst {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [fintype β] (a : α) :
  fiber (λ p : α × β, p.1) a = (@finset.univ β _).map (embedding.inr a β) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.2, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end

@[simp]
lemma fiber_prod_snd {α : Type*} [fintype α] {β : Type*} [fintype β] [decidable_eq β] (b : β) :
  fiber (λ p : α × β, p.2) b = (@finset.univ α _).map (embedding.inl α b) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.1, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end

end fintype
