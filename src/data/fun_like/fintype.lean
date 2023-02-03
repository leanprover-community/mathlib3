/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import data.finite.basic
import data.fintype.basic
import data.fun_like.basic

/-!
# Finiteness of `fun_like` types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show a type `F` with a `fun_like F α β` is finite if both `α` and `β` are finite.
This corresponds to the following two pairs of declarations:

 * `fun_like.fintype` is a definition stating all `fun_like`s are finite if their domain and
   codomain are.
 * `fun_like.finite` is a lemma stating all `fun_like`s are finite if their domain and
   codomain are.
 * `fun_like.fintype'` is a non-dependent version of `fun_like.fintype` and
 * `fun_like.finite` is a non-dependent version of `fun_like.finite`, because dependent instances
   are harder to infer.

You can use these to produce instances for specific `fun_like` types.
(Although there might be options for `fintype` instances with better definitional behaviour.)
They can't be instances themselves since they can cause loops.
-/

section type

variables (F G : Type*) {α γ : Type*} {β : α → Type*} [fun_like F α β] [fun_like G α (λ _, γ)]

/-- All `fun_like`s are finite if their domain and codomain are.

This is not an instance because specific `fun_like` types might have a better-suited definition.

See also `fun_like.finite`.
-/
noncomputable def fun_like.fintype [decidable_eq α] [fintype α] [Π i, fintype (β i)] : fintype F :=
fintype.of_injective _ fun_like.coe_injective

/-- All `fun_like`s are finite if their domain and codomain are.

Non-dependent version of `fun_like.fintype` that might be easier to infer.
This is not an instance because specific `fun_like` types might have a better-suited definition.
-/
noncomputable def fun_like.fintype' [decidable_eq α] [fintype α] [fintype γ] : fintype G :=
fun_like.fintype G

end type

section sort

variables (F G : Sort*) {α γ : Sort*} {β : α → Sort*} [fun_like F α β] [fun_like G α (λ _, γ)]

/-- All `fun_like`s are finite if their domain and codomain are.

Can't be an instance because it can cause infinite loops.
-/
lemma fun_like.finite [finite α] [∀ i, finite (β i)] : finite F :=
finite.of_injective _ fun_like.coe_injective

/-- All `fun_like`s are finite if their domain and codomain are.

Non-dependent version of `fun_like.finite` that might be easier to infer.
Can't be an instance because it can cause infinite loops.
-/
lemma fun_like.finite' [finite α] [finite γ] : finite G :=
fun_like.finite G

end sort
