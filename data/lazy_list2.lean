/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for lazy_lists.
-/

import category.traversable.equiv category.traversable.instances data.lazy_list

namespace lazy_list

open function

def list_equiv_lazy_list (α : Type*) : list α ≃ lazy_list α :=
{ to_fun := lazy_list.of_list,
  inv_fun := lazy_list.to_list,
  right_inv := by { intro, induction x, refl, simp! [*],
                    ext, cases x, refl },
  left_inv := by { intro, induction x, refl, simp! [*] } }

universes u
def thunk.mk {α} (x : α) : thunk α := λ _, x

protected def traverse {m : Type u → Type u} [applicative m] {α β : Type u}
    (f : α → m β) : lazy_list α → m (lazy_list β)
| lazy_list.nil := pure lazy_list.nil
| (lazy_list.cons x xs):= lazy_list.cons <$> f x <*> (thunk.mk <$> traverse (xs ()))

instance : traversable lazy_list :=
{ map := @lazy_list.traverse id _,
  traverse := @lazy_list.traverse }

instance : is_lawful_traversable lazy_list :=
begin
  apply equiv.is_lawful_traversable' list_equiv_lazy_list;
  intros ; resetI; ext,
  { induction x, refl,
    simp! [equiv.map,functor.map] at *,
    simp [*], refl, },
  { induction x, refl,
    simp! [equiv.map,functor.map_const] at *,
    simp [*], refl, },
  { induction x,
    { simp! [traversable.traverse,equiv.traverse] with functor_norm, refl },
    simp! [equiv.map,functor.map_const,traversable.traverse] at *, rw x_ih,
    dsimp [list_equiv_lazy_list,equiv.traverse,to_list,traversable.traverse,list.traverse],
    simp! with functor_norm, refl },
end

end lazy_list
