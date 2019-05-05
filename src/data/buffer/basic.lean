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

variables {α : Type*} {xs : list α}

@[extensionality]
lemma ext : ∀ {b₁ b₂ : buffer α}, to_list b₁ = to_list b₂ → b₁ = b₂
| ⟨n₁, a₁⟩ ⟨n₂, a₂⟩ h := begin
  simp [to_list, to_array] at h,
  have e : n₁ = n₂ :=
    by rw [←array.to_list_length a₁, ←array.to_list_length a₂, h],
  subst e,
  have h : a₁ == a₂.to_list.to_array := h ▸ a₁.to_list_to_array.symm,
  rw eq_of_heq (h.trans a₂.to_list_to_array)
end

instance (α) [decidable_eq α] : decidable_eq (buffer α) :=
by tactic.mk_dec_eq_instance

@[simp]
lemma to_list_append_list {b : buffer α} :
  to_list (append_list b xs) = to_list b ++ xs :=
by induction xs generalizing b; simp! [*]; cases b; simp! [to_list,to_array]

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
