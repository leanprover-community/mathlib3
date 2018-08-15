/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for buffers.
-/

import data.buffer data.array.lemmas
import category.traversable.instances data.equiv.basic
       tactic.ext

namespace buffer

open function

variables {α : Type*}
variables {buf buf' : buffer α}
variables {xs : list α}

@[extensionality]
lemma ext
  (h : to_list buf = to_list buf') :
  buf = buf' :=
begin
  cases buf with n buf, cases buf' with n' buf', simp [to_list,to_array] at h,
  have : n = n',
  { rw [← array.to_list_length buf,← array.to_list_length buf',h] },
  subst n',
  have := array.to_list_to_array buf,
  have := array.to_list_to_array buf',
  rw h at *, congr, apply eq_of_heq, transitivity;
  [ symmetry, skip ]; assumption,
end

@[simp]
lemma to_list_append_list  :
  to_list (append_list buf xs) = to_list buf ++ xs :=
by induction xs generalizing buf; simp! [*];
   cases buf; simp! [to_list,to_array]

@[simp]
lemma append_list_mk_buffer  :
  append_list mk_buffer xs = array.to_buffer (list.to_array xs) :=
by ext x : 1; simp [array.to_buffer,to_list,to_list_append_list];
   induction xs; [refl,skip]; simp [to_array]; refl

def list_equiv_buffer (α : Type*) : list α ≃ buffer α :=
begin
  refine { to_fun := list.to_buffer, inv_fun := buffer.to_list, .. };
  simp [left_inverse,function.right_inverse],
  { intro x, induction x, refl,
    simp [list.to_buffer,append_list],
    rw ← x_ih, refl },
  { intro x, cases x,
    simp [to_list,to_array,list.to_buffer],
    congr, simp, refl, apply array.to_list_to_array }
end

instance : traversable buffer :=
equiv.traversable list_equiv_buffer

instance : is_lawful_traversable buffer :=
equiv.is_lawful_traversable list_equiv_buffer

end buffer
