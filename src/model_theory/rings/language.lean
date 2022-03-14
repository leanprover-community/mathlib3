/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import model_theory.terms_and_formulas

/-!
# The language of rings

## Main Definitions
* A `first_order.language.ring.L` defines the language of rings,
  which consists of `0`, `1`, `-`, `+`, `*`.
-/
universes u v u'

namespace first_order
namespace language
namespace ring

/-- The constant symbols in `first_order.language.ring.L` -/
inductive consts : Type u
| zero : consts
| one : consts

/-- The unary function symbols in `first_order.language.ring.L` -/
inductive unaries : Type u
| neg : unaries

/-- The binary function symbols in `first_order.language.ring.L` -/
inductive binaries : Type u
| add : binaries
| mul : binaries

/-- All function symbols in `first_order.language.ring.L` -/
def functions : ℕ → Type u
| 0 := consts
| 1 := unaries
| 2 := binaries
| (n + 3) := pempty

instance : inhabited consts := ⟨ consts.zero ⟩
instance : inhabited unaries := ⟨ unaries.neg ⟩
instance : inhabited binaries := ⟨ binaries.add ⟩
instance : inhabited (functions 0) := ⟨ consts.zero ⟩

/-- The language of rings -/
@[reducible] def L : language.{u v} :=
{ functions := functions.{u},
  relations := λ n, pempty.{v+1} }

variable {α : Type u'}

@[simp] instance : has_zero (L.term α) := ⟨ @func L _ 0 consts.zero fin_zero_elim ⟩

@[simp] instance : has_one (L.term α) := ⟨ @func L _ 0 consts.one fin_zero_elim ⟩

@[simp] instance : has_neg (L.term α) := ⟨ λ x, @func L _ 1 unaries.neg ![x] ⟩

@[simp] instance : has_add (L.term α) :=
⟨ λ x y, @func L _ 2 binaries.add ![x, y] ⟩

@[simp] instance : has_mul (L.term α) :=
⟨ λ x y, @func L _ 2 binaries.mul ![x, y] ⟩

instance : has_pow (L.term α) ℕ := ⟨ λ t n, npow_rec n t ⟩

@[simp] lemma pow_zero (t : L.term α) : t ^ 0 = 1 := rfl
@[simp] lemma pow_succ {n} (t : L.term α) : t ^ (n + 1) = t * t ^ n := rfl

end ring
end language
end first_order
