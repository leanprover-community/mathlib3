/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Lexicographic preorder / partial_order / linear_order / decidable_linear_order,
for pairs and dependent pairs.
-/
import order.basic
import tactic.interactive

universes u v

def lex (α : Type u) (β : Type v) := α × β

variables {α : Type u} {β : Type v}

/-- Dictionary / lexicographic ordering on pairs.  -/
instance lex_has_le [preorder α] [preorder β] : has_le (lex α β) :=
{ le := λ a b, a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) }

instance lex_has_lt [preorder α] [preorder β] : has_lt (lex α β) :=
{ lt := λ a b, a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) }

/-- Dictionary / lexicographic preorder for pairs. -/
instance lex_preorder [preorder α] [preorder β] : preorder (lex α β) :=
{ le_refl := λ a, or.inr ⟨rfl, le_refl _⟩,
  le_trans :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ (a₁₂_lt | ⟨a₁₂_eq, b₁₂_le⟩) (a₂₃_lt | ⟨a₂₃_eq, b₂₃_le⟩),
    { exact or.inl (lt_trans a₁₂_lt a₂₃_lt) },
    { left, rwa ←a₂₃_eq },
    { left, rwa a₁₂_eq },
    { exact or.inr ⟨eq.trans a₁₂_eq a₂₃_eq, le_trans b₁₂_le b₂₃_le⟩, }
    end,
  lt_iff_le_not_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    split,
    { rintros (⟨a₁₂_lt⟩ | ⟨a₁₂_eq, b₁₂_lt⟩),
      { exact ⟨
        or.inl a₁₂_lt,
        not_or_distrib.2 ⟨λ h, lt_irrefl _ (lt_trans h a₁₂_lt),
           λ h, begin cases h with h₁, dsimp at h₁, subst h₁, exact lt_irrefl _ a₁₂_lt end⟩ ⟩ },
      { dsimp at a₁₂_eq,
        subst a₁₂_eq,
        exact ⟨or.inr ⟨rfl, le_of_lt b₁₂_lt⟩,
          not_or_distrib.2 ⟨lt_irrefl _, λ h, (lt_iff_le_not_le.1 b₁₂_lt).2 h.2⟩⟩ } },
    { rintros ⟨a₁₂_lt | ⟨p, b₁₂_le⟩, b⟩,
      { exact or.inl a₁₂_lt, },
      { cases not_or_distrib.1 b with a₂₁_not_lt h,
        dsimp at p,
        subst p,
        exact or.inr ⟨rfl, lt_iff_le_not_le.2 ⟨b₁₂_le, by simpa using h⟩⟩ } }
  end,
  .. lex_has_le,
  .. lex_has_lt }

/-- Dictionary / lexicographic partial_order for pairs. -/
instance lex_partial_order [partial_order α] [partial_order β] : partial_order (lex α β) :=
{ le_antisymm :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (a₁₂_lt | ⟨a₁₂_eq, b₁₂_le⟩) (a₂₁_lt | ⟨a₂₁_eq, b₂₁_le⟩),
    { exact false.elim (lt_irrefl a₁ (lt_trans a₁₂_lt a₂₁_lt)) },
    { rw a₂₁_eq at a₁₂_lt, exact false.elim (lt_irrefl a₁ a₁₂_lt) },
    { rw a₁₂_eq at a₂₁_lt, exact false.elim (lt_irrefl a₂ a₂₁_lt) },
    { dsimp at a₁₂_eq, subst a₁₂_eq, have h := le_antisymm b₁₂_le b₂₁_le, dsimp at h, rw h }
  end
  .. lex_preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance lex_linear_order [linear_order α] [linear_order β] : linear_order (lex α β) :=
{ le_total :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    rcases le_total a₁ a₂ with ha | ha;
      cases lt_or_eq_of_le ha with a_lt a_eq,
    -- Deal with the two goals with a₁ ≠ a₂
    { left, left, exact a_lt },
    swap,
    { right, left, exact a_lt },
    -- Now deal with the two goals with a₁ = a₂
    all_goals { subst a_eq,
                rcases le_total b₁ b₂ with hb | hb },
    { left,  right, exact ⟨rfl, hb⟩ },
    { right, right, exact ⟨rfl, hb⟩ },
    { left,  right, exact ⟨rfl, hb⟩ },
    { right, right, exact ⟨rfl, hb⟩ }
  end
  .. lex_partial_order }.

/-- Dictionary / lexicographic decidable_linear_order for pairs. -/
instance lex_decidable_linear_order [decidable_linear_order α] [decidable_linear_order β] :
  decidable_linear_order (lex α β) :=
{ decidable_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    rcases decidable_linear_order.decidable_le α a₁ a₂ with a₂₁_lt | a₁₂_le,
    { -- a₂ < a₁
      exact decidable.is_false (not_le.2 (or.inl (not_le.1 a₂₁_lt))) },
    { -- a₁ ≤ a₂
      by_cases h : a₁ = a₂,
      { subst h,
        rcases decidable_linear_order.decidable_le _ b₁ b₂ with b₂₁_lt | b₁₂_le,
        { -- b₂ < b₁
          exact decidable.is_false (not_le.2 (or.inr ⟨rfl, not_le.1 b₂₁_lt⟩)) },
        { -- b₁ ≤ b₂
          apply decidable.is_true,
          cases lt_or_eq_of_le a₁₂_le with a₁₂_lt a₁₂_eq,
          { exact or.inl a₁₂_lt },
          { exact or.inr ⟨a₁₂_eq, b₁₂_le⟩ } } },
      { -- a₁ < a₂
        apply decidable.is_true,
        cases lt_or_eq_of_le a₁₂_le with a₁₂_lt a₁₂_eq,
        { exact or.inl a₁₂_lt },
        { exact or.inl (false.elim (h a₁₂_eq)) } }
    }
  end,
  .. lex_linear_order
}

variables {Z : α → Type v}

/--
Dictionary / lexicographic ordering on dependent pairs.

The 'pointwise' partial order `prod.has_le` doesn't make
sense for dependent pairs, so it's safe to mark these as
instances here.
-/
instance dlex_has_le [preorder α] [∀ a, preorder (Z a)] : has_le (Σ a, Z a) :=
{ le := λ a b, a.1 < b.1 ∨ (∃ p : a.1 = b.1, a.2 ≤ (by convert b.2)) }
instance dlex_has_lt [preorder α] [∀ a, preorder (Z a)] : has_lt (Σ a, Z a) :=
{ lt := λ a b, a.1 < b.1 ∨ (∃ p : a.1 = b.1, a.2 < (by convert b.2)) }

/-- Dictionary / lexicographic preorder on dependent pairs. -/
instance dlex_preorder [preorder α] [∀ a, preorder (Z a)] : preorder (Σ a, Z a) :=
{ le_refl := λ a, or.inr ⟨rfl, le_refl _⟩,
  le_trans :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ (a₁₂_lt | ⟨a₁₂_eq, b₁₂_le⟩) (a₂₃_lt | ⟨a₂₃_eq, b₂₃_le⟩),
    { exact or.inl (lt_trans a₁₂_lt a₂₃_lt) },
    { left, rwa ←a₂₃_eq },
    { left, rwa a₁₂_eq },
    { exact or.inr ⟨eq.trans a₁₂_eq a₂₃_eq, le_trans b₁₂_le (by convert b₂₃_le; simp) ⟩ }
  end,
  lt_iff_le_not_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    split,
    { rintros (⟨a₁₂_lt⟩ | ⟨a₁₂_eq, b₁₂_lt⟩),
      { exact ⟨
        or.inl a₁₂_lt,
        not_or_distrib.2 ⟨λ h, lt_irrefl _ (lt_trans h a₁₂_lt),
           not_exists.2 (λ h w, by {
            dsimp at h,
            subst h,
            exact lt_irrefl _ a₁₂_lt })⟩ ⟩ },
      { dsimp at a₁₂_eq,
        subst a₁₂_eq,
        exact ⟨or.inr ⟨rfl, le_of_lt b₁₂_lt⟩,
          not_or_distrib.2 ⟨lt_irrefl _, not_exists.2 (λ w h, (lt_iff_le_not_le.1 b₁₂_lt).2 h)⟩⟩,
           } },
    { rintros ⟨a₁₂_lt | ⟨p, b₁₂_le⟩, b⟩,
      { exact or.inl a₁₂_lt, },
      { cases not_or_distrib.1 b with a₂₁_not_lt h,
        dsimp at p,
        subst p,
        exact or.inr ⟨rfl, lt_iff_le_not_le.2 ⟨b₁₂_le, by apply (not_exists.1 h) rfl ⟩⟩ } }
  end,
  .. dlex_has_le,
  .. dlex_has_lt }

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance dlex_partial_order [partial_order α] [∀ a, partial_order (Z a)] : partial_order (Σ a, Z a) :=
{ le_antisymm :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (a₁₂_lt | ⟨a₁₂_eq, b₁₂_le⟩) (a₂₁_lt | ⟨a₂₁_eq, b₂₁_le⟩),
    { exact false.elim (lt_irrefl a₁ (lt_trans a₁₂_lt a₂₁_lt)) },
    { rw a₂₁_eq at a₁₂_lt, exact false.elim (lt_irrefl a₁ a₁₂_lt) },
    { rw a₁₂_eq at a₂₁_lt, exact false.elim (lt_irrefl a₂ a₂₁_lt) },
    { dsimp at a₁₂_eq, subst a₁₂_eq, have h := le_antisymm b₁₂_le b₂₁_le, dsimp at h, rw h, simp, }
  end
  .. dlex_preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance dlex_linear_order [linear_order α] [∀ a, linear_order (Z a)] : linear_order (Σ a, Z a) :=
{ le_total :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    rcases le_total a₁ a₂ with ha | ha;
      cases lt_or_eq_of_le ha with a_lt a_eq,
    -- Deal with the two goals with a₁ ≠ a₂
    { left, left, exact a_lt },
    swap,
    { right, left, exact a_lt },
    -- Now deal with the two goals with a₁ = a₂
    all_goals { subst a_eq,
                rcases le_total b₁ b₂ with hb | hb },
    { left,  right, exact ⟨rfl, hb⟩ },
    { right, right, exact ⟨rfl, hb⟩ },
    { left,  right, exact ⟨rfl, hb⟩ },
    { right, right, exact ⟨rfl, hb⟩ }
  end
  .. dlex_partial_order }.

/-- Dictionary / lexicographic decidable_linear_order for dependent pairs. -/
instance dlex_decidable_linear_order [decidable_linear_order α] [∀ a, decidable_linear_order (Z a)] :
  decidable_linear_order (Σ a, Z a) :=
{ decidable_le :=
  begin
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
    rcases decidable_linear_order.decidable_le α a₁ a₂ with a₂₁_lt | a₁₂_le,
    { -- a₂ < a₁
      exact decidable.is_false (not_le.2 (or.inl (not_le.1 a₂₁_lt))) },
    { -- a₁ ≤ a₂
      by_cases h : a₁ = a₂,
      { subst h,
        rcases decidable_linear_order.decidable_le _ b₁ b₂ with b₂₁_lt | b₁₂_le,
        { -- b₂ < b₁
          exact decidable.is_false (not_le.2 (or.inr ⟨rfl, not_le.1 b₂₁_lt⟩)) },
        { -- b₁ ≤ b₂
          apply decidable.is_true,
          cases lt_or_eq_of_le a₁₂_le with a₁₂_lt a₁₂_eq,
          { exact or.inl a₁₂_lt },
          { exact or.inr ⟨a₁₂_eq, b₁₂_le⟩ } } },
      { -- a₁ < a₂
        apply decidable.is_true,
        cases lt_or_eq_of_le a₁₂_le with a₁₂_lt a₁₂_eq,
        { exact or.inl a₁₂_lt },
        { exact or.inl (false.elim (h a₁₂_eq)) } }
    }
  end,
  .. dlex_linear_order
}
