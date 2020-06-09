/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johan Commelin, Scott Morrison
-/
import data.fintype.basic

/-!
# The fiber over a point.

We define the fiber of a function `f : α → β` over a point `b : β`,
as a `set α`, and prove some basic properties.
-/

open function

/--
The fiber of function `f : α → β` over a point `b : β`.
-/
def fiber {α β : Type*} (f : α → β) (b : β) : set α :=
{ a | f a = b }

@[simp]
lemma mem_fiber {α β : Type*} (f : α → β) (b : β) (a : α) :
  a ∈ fiber f b ↔ f a = b :=
by simp [fiber]

lemma fibers_disjoint {α β : Type*} (f : α → β) (b₁ b₂ : β) (h : b₁ ≠ b₂) :
  disjoint (fiber f b₁) (fiber f b₂) :=
begin
  dsimp [disjoint],
  rintros a w,
  simp [fiber] at w,
  exact false.elim (h (w.1.symm.trans w.2))
end

@[simp]
lemma fiber_prod_fst {α β : Type*} (a : α) :
  fiber (prod.fst : α × β → α) a = (@set.univ β).image (embedding.sectr a β) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.2, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end

@[simp]
lemma fiber_prod_snd {α β : Type*} (b : β) :
  fiber (prod.snd : α × β → β) b = (@set.univ α).image (embedding.sectl α b) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.1, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end
