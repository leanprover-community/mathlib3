/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import logic.basic

/-!
# `ne_zero` typeclass

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/

/-- A type-class version of `n ≠ 0`.  -/
class ne_zero {R} [has_zero R] (n : R) : Prop := (out : n ≠ 0)

lemma ne_zero.ne {R} [has_zero R] (n : R) [h : ne_zero n] : n ≠ 0 := h.out

lemma ne_zero.ne' {R} [has_zero R] (n : R) [h : ne_zero n] : 0 ≠ n := h.out.symm

lemma ne_zero_iff {R : Type*} [has_zero R] {n : R} : ne_zero n ↔ n ≠ 0 :=
⟨λ h, h.out, ne_zero.mk⟩

lemma not_ne_zero {R : Type*} [has_zero R] {n : R} : ¬ ne_zero n ↔ n = 0 :=
by simp [ne_zero_iff]

lemma eq_zero_or_ne_zero {α} [has_zero α] (a : α) : a = 0 ∨ ne_zero a :=
(eq_or_ne a 0).imp_right ne_zero.mk

section
variables {α : Type*} [has_zero α] [has_one α]

@[simp] lemma zero_ne_one [ne_zero (1 : α)] : (0 : α) ≠ 1 := ne_zero.ne' (1 : α)
@[simp] lemma one_ne_zero [ne_zero (1 : α)] : (1 : α) ≠ 0 := ne_zero.ne (1 : α)
lemma two_ne_zero [has_add α] [ne_zero (2 : α)] : (2 : α) ≠ 0 := ne_zero.ne (2 : α)
lemma three_ne_zero [has_add α] [ne_zero (3 : α)] : (3 : α) ≠ 0 := ne_zero.ne (3 : α)
lemma four_ne_zero [has_add α] [ne_zero (4 : α)] : (4 : α) ≠ 0 := ne_zero.ne (4 : α)

lemma ne_zero_of_eq_one [ne_zero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 :=
calc a = 1 : h
   ... ≠ 0 : one_ne_zero

variable (α)

lemma zero_ne_one' [ne_zero (1 : α)] : (0 : α) ≠ 1 := ne_zero.ne' (1 : α)
lemma one_ne_zero' [ne_zero (1 : α)] : (1 : α) ≠ 0 := ne_zero.ne (1 : α)
lemma two_ne_zero' [has_add α] [ne_zero (2 : α)] : (2 : α) ≠ 0 := ne_zero.ne (2 : α)
lemma three_ne_zero' [has_add α] [ne_zero (3 : α)] : (3 : α) ≠ 0 := ne_zero.ne (3 : α)
lemma four_ne_zero' [has_add α] [ne_zero (4 : α)] : (4 : α) ≠ 0 := ne_zero.ne (4 : α)

end

namespace ne_zero

variables {R S M F : Type*} {r : R} {x y : M} {n p : ℕ} --{a : ℕ+}

instance succ : ne_zero (n + 1) := ⟨n.succ_ne_zero⟩

lemma of_pos [preorder M] [has_zero M] (h : 0 < x) : ne_zero x := ⟨ne_of_gt h⟩

instance coe_trans [has_zero M] [has_coe R S] [has_coe_t S M] [h : ne_zero (r : M)] :
  ne_zero ((r : S) : M) := ⟨h.out⟩

lemma trans [has_zero M] [has_coe R S] [has_coe_t S M] (h : ne_zero ((r : S) : M)) :
  ne_zero (r : M) := ⟨h.out⟩

end ne_zero
