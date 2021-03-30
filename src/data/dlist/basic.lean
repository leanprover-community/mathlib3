/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.dlist

/-- Concatenates a list of difference lists to form a single
difference list.  Similar to `list.join`. -/
def dlist.join {α : Type*} : list (dlist α) → dlist α
 | [] := dlist.empty
 | (x :: xs) := x ++ dlist.join xs

@[simp] lemma dlist_singleton {α : Type*} {a : α} :
  dlist.singleton a = dlist.lazy_of_list ([a]) := rfl

@[simp] lemma dlist_lazy {α : Type*} {l : list α} :
  dlist.lazy_of_list l = dlist.of_list l := rfl
