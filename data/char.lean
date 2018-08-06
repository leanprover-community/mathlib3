/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Supplementary theorems about the `char` type.
-/

instance : decidable_linear_order char :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b h₁ h₂,
    char.eq_of_veq $ le_antisymm h₁ h₂,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  decidable_le := char.decidable_le,
  decidable_eq := char.decidable_eq,
  decidable_lt := char.decidable_lt,
  ..char.has_le, ..char.has_lt }
