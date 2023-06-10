/-
Copyright (c) 2015 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import data.W.basic

/-!
# Examples of W-types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We take the view of W types as inductive types.
Given `α : Type` and `β : α → Type`, the W type determined by this data, `W_type β`, is the
inductively with constructors from `α` and arities of each constructor `a : α` given by `β a`.

This file contains `nat` and `list` as examples of W types.

## Main results
* `W_type.equiv_nat`: the construction of the naturals as a W-type is equivalent
  to `nat`
* `W_type.equiv_list`: the construction of lists on a type `γ` as a W-type is equivalent to
  `list γ`
-/

universes u v

namespace W_type

section nat

/-- The constructors for the naturals -/
inductive nat_α : Type
| zero : nat_α
| succ : nat_α

instance : inhabited nat_α := ⟨ nat_α.zero ⟩

/-- The arity of the constructors for the naturals, `zero` takes no arguments, `succ` takes one -/
def nat_β : nat_α → Type
| nat_α.zero := empty
| nat_α.succ := unit

instance : inhabited (nat_β nat_α.succ) := ⟨ () ⟩

/-- The isomorphism from the naturals to its corresponding `W_type` -/
@[simp] def of_nat : ℕ → W_type nat_β
| nat.zero := ⟨ nat_α.zero , empty.elim ⟩
| (nat.succ n) := ⟨ nat_α.succ , λ _ , of_nat n ⟩

/-- The isomorphism from the `W_type` of the naturals to the naturals -/
@[simp] def to_nat : W_type nat_β → ℕ
| (W_type.mk nat_α.zero f) := 0
| (W_type.mk nat_α.succ f) := (to_nat (f ())).succ

lemma left_inv_nat : function.left_inverse of_nat to_nat
| (W_type.mk nat_α.zero f) := by { simp, tidy }
| (W_type.mk nat_α.succ f) := by { simp, tidy }

lemma right_inv_nat : function.right_inverse of_nat to_nat
| nat.zero := rfl
| (nat.succ n) := by rw [of_nat, to_nat, right_inv_nat n]

/-- The naturals are equivalent to their associated `W_type` -/
def equiv_nat : W_type nat_β ≃ ℕ :=
{ to_fun := to_nat,
  inv_fun := of_nat,
  left_inv := left_inv_nat,
  right_inv := right_inv_nat }

open sum punit

/--
`W_type.nat_α` is equivalent to `punit ⊕ punit`.
This is useful when considering the associated polynomial endofunctor.
-/
@[simps] def nat_α_equiv_punit_sum_punit : nat_α ≃ punit.{u + 1} ⊕ punit :=
{ to_fun := λ c, match c with | nat_α.zero := inl star | nat_α.succ := inr star end,
  inv_fun := λ b, match b with | inl x := nat_α.zero | inr x := nat_α.succ end,
  left_inv := λ c, match c with | nat_α.zero := rfl | nat_α.succ := rfl end,
  right_inv := λ b, match b with | inl star := rfl | inr star := rfl end }

end nat

section list

variable (γ : Type u)

/--
The constructors for lists.
There is "one constructor `cons x` for each `x : γ`",
since we view `list γ` as
```
| nil : list γ
| cons x₀ : list γ → list γ
| cons x₁ : list γ → list γ
|   ⋮      γ many times
```
-/
inductive list_α : Type u
| nil : list_α
| cons : γ → list_α

instance : inhabited (list_α γ) := ⟨ list_α.nil ⟩

/-- The arities of each constructor for lists, `nil` takes no arguments, `cons hd` takes one -/
def list_β : list_α γ → Type u
| list_α.nil := pempty
| (list_α.cons hd) := punit

instance (hd : γ) : inhabited (list_β γ (list_α.cons hd)) := ⟨ punit.star ⟩

/-- The isomorphism from lists to the `W_type` construction of lists -/
@[simp] def of_list : list γ → W_type (list_β γ)
| list.nil := ⟨ list_α.nil, pempty.elim ⟩
| (list.cons hd tl) := ⟨ list_α.cons hd, λ _ , of_list tl ⟩

/-- The isomorphism from the `W_type` construction of lists to lists -/
@[simp] def to_list : W_type (list_β γ) → list γ
| (W_type.mk list_α.nil f) := []
| (W_type.mk (list_α.cons hd) f) := hd :: to_list (f punit.star)

lemma left_inv_list : function.left_inverse (of_list γ) (to_list _)
| (W_type.mk list_α.nil f) := by { simp, tidy }
| (W_type.mk (list_α.cons x) f) := by { simp, tidy }

lemma right_inv_list : function.right_inverse (of_list γ) (to_list _)
| list.nil := rfl
| (list.cons hd tl) := by simp [right_inv_list tl]

/-- Lists are equivalent to their associated `W_type` -/
def equiv_list : W_type (list_β γ) ≃ list γ :=
{ to_fun := to_list _,
  inv_fun := of_list _,
  left_inv := left_inv_list _,
  right_inv := right_inv_list _ }

/--
`W_type.list_α` is equivalent to `γ` with an extra point.
This is useful when considering the associated polynomial endofunctor
-/
def list_α_equiv_punit_sum : list_α γ ≃ punit.{v + 1} ⊕ γ :=
{ to_fun := λ c, match c with | list_α.nil := sum.inl punit.star | list_α.cons x := sum.inr x end,
  inv_fun := sum.elim (λ _, list_α.nil) (λ x, list_α.cons x),
  left_inv := λ c, match c with | list_α.nil := rfl | list_α.cons x := rfl end,
  right_inv := λ x, match x with | sum.inl punit.star := rfl | sum.inr x := rfl end, }

end list

end W_type
