/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Free monoid over a given alphabet
-/
import algebra.group.to_additive

@[to_additive free_add_monoid]
def free_monoid (α) := list α

@[to_additive]
instance {α} : monoid (free_monoid α) :=
{ one := [],
  mul := λ x y, (x ++ y : list α),
  mul_one := by intros; apply list.append_nil,
  one_mul := by intros; refl,
  mul_assoc := by intros; apply list.append_assoc }

@[to_additive]
instance {α} : inhabited (free_monoid α) := ⟨1⟩

@[simp, to_additive free_add_monoid.zero_def]
lemma free_monoid.one_def {α} : (1 : free_monoid α) = [] := rfl

@[simp, to_additive free_add_monoid.add_def]
lemma free_monoid.mul_def {α} (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) :=
rfl
