import group_theory.free_group
import topology.metric_space.hausdorff_distance

/-!
# To move
-/

alias list.length_le_of_sublist ← list.sublist.length

attribute [protected] list.sublist.length

namespace free_group
variable {α : Type*}

open list

/-
Similar to `free_group.of`, but includes generators as well as their inverses into the free group.
-/
def of_gen (a : α) (sgn : bool) : free_group α := free_group.mk [(a, sgn)]

@[simp] lemma of_gen_to_of (a : α) : free_group.of_gen a tt = free_group.of a := rfl

@[simp] lemma of_gen_false_inv (a : α) : of_gen a ff = (of_gen a tt)⁻¹ :=
begin
  rw [of_gen, of_gen, inv_mk], refl
end


lemma cons_mk {a : α} {sgn : bool} (l : list (α × bool)): free_group.mk ((a, sgn) :: l) = (of_gen a sgn) * (free_group.mk l) :=
begin
  show mk ([(a, sgn)] ++ l) = _, rw [← mul_mk], refl,
end

variable [decidable_eq α]

@[simp] lemma to_word_inv (x : free_group α) : x⁻¹.to_word = list.map (λ (x : α × bool), (x.fst, !x.snd)) x.to_word.reverse := sorry

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

lemma diam_cthickening_le (hε : 0 ≤ ε) : diam (cthickening ε s) ≤ 2 * ε + diam s :=
begin
  apply metric.diam_le_of_forall_dist_le,
  { have : 0 ≤ diam s := diam_nonneg, linarith },
  intros x hx y hy,
  rw [mem_cthickening_iff, emetric.inf_edist] at hx hy,
  -- it seems like an additional hypothesis of `s` being closed might be required to finish the proof
  -- without a strict inequality, one cannot pick elements from `s` sufficiently close to `x` or `y`
  sorry,
end


lemma diam_thickening_le (hε : 0 ≤ ε) : diam (thickening ε s) ≤ 2 * ε + diam s := sorry

end
