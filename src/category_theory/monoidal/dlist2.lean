/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
universes u
/--
A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure dlist2 (α : Type u) :=
(apply     : list α → list α)
(invariant : ∀ l, apply l = apply [] ++ l)

namespace dlist2
open function
variables {α : Type u}

local notation `♯`:max := by abstract { intros, simp }

/-- Convert a list to a dlist -/
def of_list (l : list α) : dlist2 α :=
⟨append l, ♯⟩

/-- Convert a lazily-evaluated list to a dlist -/
def lazy_of_list (l : thunk (list α)) : dlist2 α :=
⟨λ xs, l () ++ xs, ♯⟩

/-- Convert a dlist to a list -/
def to_list : dlist2 α → list α
| ⟨xs, _⟩ := xs []

/--  Create a dlist containing no elements -/
def empty : dlist2 α :=
⟨id, ♯⟩

local notation a `::_`:max := list.cons a

/-- Create dlist with a single element -/
def singleton (x : α) : dlist2 α :=
⟨x::_, ♯⟩

local attribute [simp] function.comp

/-- `O(1)` Prepend a single element to a dlist -/
def cons (x : α) : dlist2 α →  dlist2 α
| ⟨xs, h⟩ := ⟨x::_ ∘ xs, by abstract { intros, simp, rw [←h] }⟩

/-- `O(1)` Append a single element to a dlist -/
def concat (x : α) : dlist2 α → dlist2 α
| ⟨xs, h⟩ := ⟨xs ∘ x::_, by abstract { intros, simp, rw [h, h [x]], simp }⟩

/-- `O(1)` Append dlists -/
protected def append (L M : dlist2 α) : dlist2 α:=
⟨L.apply ∘ M.apply, by { intros, simp, rw [M.invariant, L.invariant, L.invariant (M.apply list.nil)], simp } ⟩

instance : has_append (dlist2 α) :=
⟨dlist2.append⟩

lemma append_assoc (L M N : dlist2 α) : (L ++ M) ++ N = L ++ (M ++ N) := rfl

local attribute [simp] of_list to_list empty singleton cons concat dlist2.append

lemma to_list_of_list (l : list α) : to_list (of_list l) = l :=
by cases l; simp

lemma of_list_to_list (l : dlist2 α) : of_list (to_list l) = l :=
begin
   cases l with xs,
   have h : append (xs []) = xs,
   { intros, funext x, simp [l_invariant x] },
   simp [h]
end

lemma to_list_empty : to_list (@empty α) = [] :=
by simp

lemma to_list_singleton (x : α) : to_list (singleton x) = [x] :=
by simp

lemma to_list_append (l₁ l₂ : dlist2 α) : to_list (l₁ ++ l₂) = to_list l₁ ++ to_list l₂ :=
show to_list (dlist2.append l₁ l₂) = to_list l₁ ++ to_list l₂, from
by cases l₁; cases l₂; simp; rw l₁_invariant

lemma to_list_cons (x : α) (l : dlist2 α) : to_list (cons x l) = x :: to_list l :=
by cases l; simp

lemma to_list_concat (x : α) (l : dlist2 α) : to_list (concat x l) = to_list l ++ [x] :=
by cases l; simp; rw [l_invariant]

end dlist2
