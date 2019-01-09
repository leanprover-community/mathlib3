/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu
-/
import init.algebra.functions

universe u

section
variables {α : Type u} [decidable_linear_order α]

lemma max_absorb_left {a b : α} : max (max a b) a = max a b := 
begin 
  by_cases h : a ≤ b, 
  { simp [max_eq_right h, max_eq_left h] }, 
  { simp [max_eq_left (le_of_not_le h), max_self] } 
end

lemma max_absorb_right {a b : α} : max (max a b) b = max a b := 
begin 
  by_cases h : a ≤ b, 
  { simp [max_eq_right h, max_self] }, 
  { repeat {rw max_eq_left (le_of_not_le h)} }
end

lemma le_max_of_le_left {a b c : α} (h : c ≤ a) : c ≤ max a b := 
le_trans h $ le_max_left _ _

lemma le_max_of_le_right {a b c : α} (h : c ≤ b) : c ≤ max a b := 
le_trans h $ le_max_right _ _

lemma lt_max_of_lt_left {a b c : α} (h : c < a) : c < max a b := 
lt_of_lt_of_le h $ le_max_left _ _

lemma lt_max_of_lt_right {a b c : α} (h : c < b) : c < max a b := 
lt_of_lt_of_le h $ le_max_right _ _

lemma or_of_max {a b : α} : max a b = a ∨ max a b = b := 
begin 
  by_cases h : a ≤ b, 
  { right, rw max_eq_right h }, 
  { left, rw max_eq_left (le_of_not_le h) } 
end

lemma max_le_of_le {a b c d : α} (h₁ : a ≤ c) (h₂ : b ≤ d) : max a b ≤ max c d :=
max_le (le_max_of_le_left h₁) (le_max_of_le_right h₂)

lemma max_lt_of_lt {a b c d : α} (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

end
