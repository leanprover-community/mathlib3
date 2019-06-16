/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Free monoid over a given alphabet
-/
def free_monoid (α) := list α

instance {α} : monoid (free_monoid α) :=
{ one := [],
  mul := λ x y, (x ++ y : list α),
  mul_one := by intros; apply list.append_nil,
  one_mul := by intros; refl,
  mul_assoc := by intros; apply list.append_assoc }

@[simp] lemma free_monoid.one_def {α} : (1 : free_monoid α) = [] := rfl

@[simp] lemma free_monoid.mul_def {α} (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) := rfl

def free_add_monoid (α) := list α

instance {α} : add_monoid (free_add_monoid α) :=
{ zero := [],
  add := λ x y, (x ++ y : list α),
  add_zero := by intros; apply list.append_nil,
  zero_add := by intros; refl,
  add_assoc := by intros; apply list.append_assoc }

@[simp] lemma free_add_monoid.zero_def {α} : (1 : free_monoid α) = [] := rfl

@[simp] lemma free_add_monoid.add_def {α} (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) := rfl
