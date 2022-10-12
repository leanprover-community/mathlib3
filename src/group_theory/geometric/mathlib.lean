import group_theory.free_group
import topology.metric_space.hausdorff_distance

/-!
# To move
-/

alias list.length_le_of_sublist ← list.sublist.length

attribute [protected] list.sublist.length

attribute [simp] free_group.to_word_inv

namespace free_group
variable {α : Type*}

open list

@[simp] lemma mk_cons {a : α} {sgn : bool} (l : list (α × bool)) :
  free_group.mk ((a, sgn) :: l) = mk [(a, sgn)] * free_group.mk l :=
by rw [←singleton_append, ←mul_mk]

variable [decidable_eq α]

lemma to_word_mul_sublist (x y : free_group α) : (x * y).to_word <+ x.to_word ++ y.to_word :=
begin
  refine red.sublist _,
  have : x * y = free_group.mk (x.to_word ++ y.to_word),
  { rw [←free_group.mul_mk, free_group.mk_to_word, free_group.mk_to_word] },
  rw this,
  exact free_group.reduce.red,
end

end free_group

section
variables {α : Type*} [pseudo_emetric_space α] {s : set α} {ε : ℝ}

open emetric metric (hiding diam)
open_locale ennreal nnreal

lemma ediam_cthickening_le (ε : ℝ≥0) : diam (cthickening ε s) ≤ diam s + 2 * ε :=
begin
  refine diam_le (λ x hx y hy, _),
  rw [mem_cthickening_iff, ennreal.of_real_coe_nnreal] at hx hy,
  refine ennreal.le_of_forall_pos_le_add (λ δ hδ _, _),
  have hε : (ε : ℝ≥0∞) < ε + ↑(δ / 2) := ennreal.coe_lt_coe.2 (lt_add_of_pos_right _ $ half_pos hδ),
  rw [ennreal.coe_div two_ne_zero, ennreal.coe_two] at hε,
  replace hx := hx.trans_lt hε,
  replace hy := hy.trans_lt hε,
  rw inf_edist_lt_iff at hx hy,
  obtain ⟨x', hx', hxx'⟩ := hx,
  obtain ⟨y', hy', hyy'⟩ := hy,
  refine (edist_triangle_right _ _ _).trans ((add_le_add hxx'.le $ (edist_triangle _ _ _).trans $
    add_le_add hyy'.le $ edist_le_diam_of_mem hy' hx').trans_eq _),
  -- Now we're done, but `ring` won't do it :(
  rw [←add_assoc, ←two_mul, mul_add,
    ennreal.mul_div_cancel' ennreal.two_ne_zero ennreal.two_ne_top],
  abel,
end

lemma ediam_thickening_le (ε : ℝ≥0) : diam (thickening ε s) ≤ diam s + 2 * ε :=
(emetric.diam_mono $ thickening_subset_cthickening _ _).trans $ ediam_cthickening_le _

end

section
variables {α : Type*} [pseudo_metric_space α] {s : set α} {ε : ℝ}

open metric
open_locale ennreal nnreal

lemma diam_cthickening_le (hε : 0 ≤ ε) : diam (cthickening ε s) ≤ diam s + 2 * ε :=
begin
  refine diam_le_of_forall_dist_le (by positivity) (λ x hx y hy, _),
  rw [mem_cthickening_iff, ennreal.of_real_coe_nnreal] at hx hy,
  refine ennreal.le_of_forall_pos_le_add (λ δ hδ _, _),
  have hε : (ε : ℝ≥0∞) < ε + ↑(δ / 2) := ennreal.coe_lt_coe.2 (lt_add_of_pos_right _ $ half_pos hδ),
  rw [ennreal.coe_div two_ne_zero, ennreal.coe_two] at hε,
  replace hx := hx.trans_lt hε,
  replace hy := hy.trans_lt hε,
  rw inf_edist_lt_iff at hx hy,
  obtain ⟨x', hx', hxx'⟩ := hx,
  obtain ⟨y', hy', hyy'⟩ := hy,
  refine (edist_triangle_right _ _ _).trans ((add_le_add hxx'.le $ (edist_triangle _ _ _).trans $
    add_le_add hyy'.le $ edist_le_diam_of_mem hy' hx').trans_eq _),
  -- Now we're done, but `ring` won't do it :(
  rw [←add_assoc, ←two_mul, mul_add,
    ennreal.mul_div_cancel' ennreal.two_ne_zero ennreal.two_ne_top],
  abel,
end

lemma diam_thickening_le (ε : ℝ≥0) : diam (thickening ε s) ≤ diam s + 2 * ε :=
(emetric.diam_mono $ thickening_subset_cthickening _ _).trans $ ediam_cthickening_le _

end
