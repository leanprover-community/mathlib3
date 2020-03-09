/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for lazy_lists.
-/
import control.traversable.equiv
import control.traversable.instances
import data.lazy_list

universes u

namespace thunk

/-- Creates a thunk with a (non-lazy) constant value. -/
def mk {α} (x : α) : thunk α := λ _, x

instance {α : Type u} [decidable_eq α] : decidable_eq (thunk α) | a b :=
have a = b ↔ a () = b (), from ⟨by cc, by intro; ext x; cases x; assumption⟩,
by rw this; apply_instance

end thunk

namespace lazy_list

open function

def list_equiv_lazy_list (α : Type*) : list α ≃ lazy_list α :=
{ to_fun := lazy_list.of_list,
  inv_fun := lazy_list.to_list,
  right_inv := by { intro, induction x, refl, simp! [*],
                    ext, cases x, refl },
  left_inv := by { intro, induction x, refl, simp! [*] } }

instance {α : Type u} : inhabited (lazy_list α) := ⟨nil⟩

instance {α : Type u} [decidable_eq α] : decidable_eq (lazy_list α)
| nil nil := is_true rfl
| (cons x xs) (cons y ys) :=
  if h : x = y then
    match decidable_eq (xs ()) (ys ()) with
    | is_false h2 := is_false (by intro; cc)
    | is_true h2 :=
      have xs = ys, by ext u; cases u; assumption,
      is_true (by cc)
    end
  else
    is_false (by intro; cc)
| nil (cons _ _) := is_false (by cc)
| (cons _ _) nil := is_false (by cc)

protected def traverse {m : Type u → Type u} [applicative m] {α β : Type u}
    (f : α → m β) : lazy_list α → m (lazy_list β)
| lazy_list.nil := pure lazy_list.nil
| (lazy_list.cons x xs) := lazy_list.cons <$> f x <*> (thunk.mk <$> traverse (xs ()))

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

/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list -/
def init {α} : lazy_list α → lazy_list α
| lazy_list.nil := lazy_list.nil
| (lazy_list.cons x xs) :=
  let xs' := xs () in
  match xs' with
  | lazy_list.nil := lazy_list.nil
  | (lazy_list.cons _ _) := lazy_list.cons x (init xs')
  end

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate -/
def interleave {α} : lazy_list α → lazy_list α → lazy_list α
| lazy_list.nil xs := xs
| a@(lazy_list.cons x xs) lazy_list.nil := a
| (lazy_list.cons x xs) (lazy_list.cons y ys) :=
  lazy_list.cons x (lazy_list.cons y (interleave (xs ()) (ys ())))

/-- `interleave_all (xs::ys::zs::xss)` creates an empty list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on   -/
def interleave_all {α} : list (lazy_list α) → lazy_list α
| [] := lazy_list.nil
| (x :: xs) := interleave x (interleave_all xs)

/-- apply `f` to combine every element of the first list with every element
of the second list and interleave the resulting lists -/
def lseq {α β γ} (f : α → β → γ) : lazy_list α → lazy_list β → lazy_list γ
| lazy_list.nil xs := lazy_list.nil
| (lazy_list.cons x xs) lazy_list.nil := lazy_list.nil
| (lazy_list.cons x xs) ys := interleave (ys.map $ f x) (lseq (xs ()) ys)


end lazy_list
