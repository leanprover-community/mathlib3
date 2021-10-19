/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for dlists.
-/
import data.dlist
import control.traversable.equiv
import control.traversable.instances

namespace dlist

variables (α : Type*)

open function equiv

/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def list_equiv_dlist : list α ≃ dlist α :=
by refine { to_fun := dlist.of_list, inv_fun := dlist.to_list, .. };
   simp [function.right_inverse,left_inverse,to_list_of_list,of_list_to_list]

instance : traversable dlist :=
equiv.traversable list_equiv_dlist

instance : is_lawful_traversable dlist :=
equiv.is_lawful_traversable list_equiv_dlist

instance {α} : inhabited (dlist α) := ⟨dlist.empty⟩

end dlist
