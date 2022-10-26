/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.regular.basic
import logic.embedding

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

/--  Elements of a left cancel semigroup are left regular. -/
@[to_additive "Elements of an add left cancel semigroup are add-left-regular."]
lemma is_left_regular_of_left_cancel_semigroup [left_cancel_semigroup R] (g : R) :
  is_left_regular g :=
mul_right_injective g

/--  Elements of a right cancel semigroup are right regular. -/
@[to_additive "Elements of an add right cancel semigroup are add-right-regular"]
lemma is_right_regular_of_right_cancel_semigroup [right_cancel_semigroup R] (g : R) :
  is_right_regular g :=
mul_left_injective g

end left_or_right_cancel_semigroup
