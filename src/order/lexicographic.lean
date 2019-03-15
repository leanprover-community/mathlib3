/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Lexicographic preorder / partial_order / linear_order.
-/
import order.basic

universes u v

variables {α : Type u} {β : Type v}

/-- Dictionary / lexicographic ordering on pairs. -/
def lex_preorder [preorder α] [preorder β] : preorder (α × β) :=
{ le := λ a b, a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2),
  le_refl := λ a, or.inr ⟨rfl, le_refl _⟩,
  le_trans := λ a b c h₁ h₂,
  begin
    cases h₁,
    { left, cases h₂,
      { exact lt_trans h₁ h₂ },
      { rwa ←h₂.left } },
    { cases h₂,
      { exact or.inl (by rwa h₁.left) },
      { exact or.inr ⟨eq.trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩ }
    } end }

def lex_partial_order [partial_order α] [partial_order β] : partial_order (α × β) :=
{ le_antisymm :=
begin
  rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (a₁₂_lt | ⟨a₁₂_eq, b₁₂_le⟩) (a₂₁_lt | ⟨a₂₁_eq, b₂₁_le⟩),
  { exfalso, exact lt_irrefl a₁ (lt_trans a₁₂_lt a₂₁_lt) },
  { exfalso, rw a₂₁_eq at a₁₂_lt, exact lt_irrefl a₁ a₁₂_lt },
  { exfalso, rw a₁₂_eq at a₂₁_lt, exact lt_irrefl a₂ a₂₁_lt },
  { dsimp at a₁₂_eq, rw a₁₂_eq, have h := le_antisymm b₁₂_le b₂₁_le, dsimp at h, rw h }
end
  .. lex_preorder }

def lex_linear_order [linear_order α] [linear_order β] : linear_order (α × β) :=
{ le_total :=
begin
  rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  -- Whee! An 8 part case bash.
  rcases le_total a₁ a₂ with ha | ha;
    rcases le_total b₁ b₂ with hb | hb;
    cases lt_or_eq_of_le ha with a_lt a_eq,
  { left,  left,  exact a_lt },
  { left,  right, exact ⟨a_eq, hb⟩ },
  { left,  left,  exact a_lt },
  { right, right, exact ⟨a_eq.symm, hb⟩ },
  { right, left,  exact a_lt },
  { left,  right, exact ⟨a_eq.symm, hb⟩ },
  { right, left,  exact a_lt },
  { right, right, exact ⟨a_eq, hb⟩ }
end
  .. lex_partial_order }
