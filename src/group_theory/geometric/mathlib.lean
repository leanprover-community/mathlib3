import group_theory.free_group

/-!
# To move
-/

alias list.length_le_of_sublist ← list.sublist.length

attribute [protected] list.sublist.length

namespace free_group
variables {α : Type*} [decidable_eq α]

open list

@[simp] lemma to_word_inv (x : free_group α) : x⁻¹.to_word = x.to_word.reverse := sorry

lemma to_word_mul_sublist (x y : free_group α) : (x * y).to_word <+ x.to_word ++ y.to_word :=
begin
  refine red.sublist _,
  have : x * y = free_group.mk (x.to_word ++ y.to_word),
  { rw [←free_group.mul_mk, free_group.to_word.mk, free_group.to_word.mk] },
  rw this,
  exact free_group.reduce.red,
end

end free_group
