/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.basic

/-!
# Ternary sum of types

This file defines `sum₃`, a shorthand for the ternary sum of types. In almost all cases,
`α ⊕ β ⊕ γ`, a nested binary sum, should be preferred over `sum₃ α β γ`. The only point of `sum₃`
is to offer better pattern-matching properties.
-/

variables (α β γ : Type*)

/-- Ternary sum of types. This is equivalent to a nested binary sum (see `sum₃_equiv_sum`), but has
better pattern-matching properties. In most cases, you should use `α ⊕ β ⊕ γ` over `sum₃ α β γ`. -/
inductive sum₃
| in₀ : α → sum₃
| in₁ : β → sum₃
| in₂ : γ → sum₃

open sum₃

instance [inhabited α] : inhabited (sum₃ α β γ) := ⟨in₀ default⟩

/-- A ternary sum is equivalent to a nested binary sum. -/
def sum₃_equiv_sum : sum₃ α β γ ≃ α ⊕ β ⊕ γ :=
{ to_fun := λ x, match x with
    | in₀ a := sum.inl a
    | in₁ b := sum.inr (sum.inl b)
    | in₂ c := sum.inr (sum.inr c)
  end,
  inv_fun := λ x, match x with
    | sum.inl a           := in₀ a
    | sum.inr (sum.inl b) := in₁ b
    | sum.inr (sum.inr c) := in₂ c
  end,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by obtain (_ | _ | _) := x; refl }

instance [fintype α] [fintype β] [fintype γ] : fintype (sum₃ α β γ) :=
fintype.of_equiv _ (sum₃_equiv_sum _ _ _).symm
