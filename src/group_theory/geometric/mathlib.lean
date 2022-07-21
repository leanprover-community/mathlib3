import group_theory.free_group
import topology.metric_space.hausdorff_distance

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

section
variables {α : Type*} [pseudo_metric_space α] {s : set α} {ε : ℝ}

open metric

lemma diam_cthickening_le (hε : 0 ≤ ε) : diam (cthickening ε s) ≤ 2 * ε + diam s := sorry
lemma diam_thickening_le (hε : 0 ≤ ε) : diam (cthickening ε s) ≤ 2 * ε + diam s := sorry

end
