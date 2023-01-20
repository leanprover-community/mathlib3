/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group.defs
import logic.embedding.basic

/-!
# The embedding of a cancellative semigroup into itself by multiplication by a fixed element.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {R : Type*}

section left_or_right_cancel_semigroup

/--
The embedding of a left cancellative semigroup into itself
by left multiplication by a fixed element.
 -/
@[to_additive
  "The embedding of a left cancellative additive semigroup into itself
   by left translation by a fixed element.", simps]
def mul_left_embedding {G : Type*} [left_cancel_semigroup G] (g : G) : G ↪ G :=
{ to_fun := λ h, g * h, inj' := mul_right_injective g }

/--
The embedding of a right cancellative semigroup into itself
by right multiplication by a fixed element.
 -/
@[to_additive
  "The embedding of a right cancellative additive semigroup into itself
   by right translation by a fixed element.", simps]
def mul_right_embedding {G : Type*} [right_cancel_semigroup G] (g : G) : G ↪ G :=
{ to_fun := λ h, h * g, inj' := mul_left_injective g }

@[to_additive]
lemma mul_left_embedding_eq_mul_right_embedding {G : Type*} [cancel_comm_monoid G] (g : G) :
  mul_left_embedding g = mul_right_embedding g :=
by { ext, exact mul_comm _ _ }

end left_or_right_cancel_semigroup
