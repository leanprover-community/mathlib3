/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed.group.add_torsor
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

open metric set
open_locale pointwise topological_space

section semi_normed_group

variables {E : Type*} [semi_normed_group E] {ε δ : ℝ} {s t : set E} {x y : E}

lemma bounded_iff_exists_norm_le : bounded s ↔ ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
by simp [subset_def, bounded_iff_subset_ball (0 : E)]

alias bounded_iff_exists_norm_le ↔ metric.bounded.exists_norm_le _

lemma metric.bounded.exists_pos_norm_le (hs : metric.bounded s) : ∃ R > 0, ∀ x ∈ s, ∥x∥ ≤ R :=
begin
  obtain ⟨R₀, hR₀⟩ := hs.exists_norm_le,
  refine ⟨max R₀ 1, _, _⟩,
  { exact (by norm_num : (0:ℝ) < 1).trans_le (le_max_right R₀ 1) },
  intros x hx,
  exact (hR₀ x hx).trans (le_max_left _ _),
end

lemma metric.bounded.add (hs : bounded s) (ht : bounded t) : bounded (s + t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ (R : ℝ), ∀ x ∈ s, ∥x∥ ≤ R := hs.exists_norm_le,
  obtain ⟨Rt, hRt⟩ : ∃ (R : ℝ), ∀ x ∈ t, ∥x∥ ≤ R := ht.exists_norm_le,
  refine (bounded_iff_exists_norm_le).2 ⟨Rs + Rt, _⟩,
  rintros z ⟨x, y, hx, hy, rfl⟩,
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ : norm_add_le _ _
  ... ≤ Rs + Rt : add_le_add (hRs x hx) (hRt y hy)
end

lemma metric.bounded.neg : bounded s → bounded (-s) :=
by { simp_rw [bounded_iff_exists_norm_le, ←image_neg, ball_image_iff, norm_neg], exact id }

lemma metric.bounded.sub (hs : bounded s) (ht : bounded t) : bounded (s - t) :=
(sub_eq_add_neg _ _).symm.subst $ hs.add ht.neg

section emetric
open emetric

lemma inf_edist_neg (x : E) (s : set E) : inf_edist (-x) s = inf_edist x (-s) :=
eq_of_forall_le_iff $ λ r, by simp_rw [le_inf_edist, ←image_neg, ball_image_iff, edist_neg]

@[simp] lemma inf_edist_neg_neg (x : E) (s : set E) : inf_edist (-x) (-s) = inf_edist x s :=
by rw [inf_edist_neg, neg_neg]

end emetric

variables (ε δ s t x y)

@[simp] lemma neg_thickening : -thickening δ s = thickening δ (-s) :=
by { unfold thickening, simp_rw ←inf_edist_neg, refl }

@[simp] lemma neg_cthickening : -cthickening δ s = cthickening δ (-s) :=
by { unfold cthickening, simp_rw ←inf_edist_neg, refl }

@[simp] lemma neg_ball : -ball x δ = ball (-x) δ :=
by { unfold metric.ball, simp_rw ←dist_neg, refl }

@[simp] lemma neg_closed_ball : -closed_ball x δ = closed_ball (-x) δ :=
by { unfold metric.closed_ball, simp_rw ←dist_neg, refl }

lemma singleton_add_ball : {x} + ball y δ = ball (x + y) δ :=
by simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_comm y x]

lemma singleton_sub_ball : {x} - ball y δ = ball (x - y) δ :=
by simp_rw [sub_eq_add_neg, neg_ball, singleton_add_ball]

lemma ball_add_singleton : ball x δ + {y} = ball (x + y) δ :=
by rw [add_comm, singleton_add_ball, add_comm y]

lemma ball_sub_singleton : ball x δ - {y} = ball (x - y) δ :=
by simp_rw [sub_eq_add_neg, neg_singleton, ball_add_singleton]

lemma singleton_add_ball_zero : {x} + ball 0 δ = ball x δ := by simp
lemma singleton_sub_ball_zero : {x} - ball 0 δ = ball x δ := by simp [singleton_sub_ball]
lemma ball_zero_add_singleton : ball 0 δ + {x} = ball x δ := by simp [ball_add_singleton]
lemma ball_zero_sub_singleton : ball 0 δ - {x} = ball (-x) δ := by simp [ball_sub_singleton]
lemma vadd_ball_zero : x +ᵥ ball 0 δ = ball x δ := by simp

@[simp] lemma singleton_add_closed_ball : {x} + closed_ball y δ = closed_ball (x + y) δ :=
by simp only [add_comm y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

@[simp] lemma singleton_sub_closed_ball : {x} - closed_ball y δ = closed_ball (x - y) δ :=
by simp_rw [sub_eq_add_neg, neg_closed_ball, singleton_add_closed_ball]

@[simp] lemma closed_ball_add_singleton : closed_ball x δ + {y} = closed_ball (x + y) δ :=
by simp [add_comm _ {y}, add_comm y]

@[simp] lemma closed_ball_sub_singleton : closed_ball x δ - {y} = closed_ball (x - y) δ :=
by simp [sub_eq_add_neg]

lemma singleton_add_closed_ball_zero : {x} + closed_ball 0 δ = closed_ball x δ := by simp
lemma singleton_sub_closed_ball_zero : {x} - closed_ball 0 δ = closed_ball x δ := by simp
lemma closed_ball_zero_add_singleton : closed_ball 0 δ + {x} = closed_ball x δ := by simp
lemma closed_ball_zero_sub_singleton : closed_ball 0 δ - {x} = closed_ball (-x) δ := by simp
@[simp] lemma vadd_closed_ball_zero : x +ᵥ closed_ball 0 δ = closed_ball x δ := by simp

lemma add_ball_zero : s + ball 0 δ = thickening δ s :=
begin
  rw thickening_eq_bUnion_ball,
  convert Union₂_add (λ x (_ : x ∈ s), {x}) (ball (0 : E) δ),
  exact s.bUnion_of_singleton.symm,
  ext x y,
  simp_rw [singleton_add_ball, add_zero],
end

lemma sub_ball_zero : s - ball 0 δ = thickening δ s := by simp [sub_eq_add_neg, add_ball_zero]
lemma ball_add_zero : ball 0 δ + s = thickening δ s := by rw [add_comm, add_ball_zero]
lemma ball_sub_zero : ball 0 δ - s = thickening δ (-s) := by simp [sub_eq_add_neg, ball_add_zero]

@[simp] lemma add_ball : s + ball x δ = x +ᵥ thickening δ s :=
by rw [←vadd_ball_zero, add_vadd_comm, add_ball_zero]

@[simp] lemma sub_ball : s - ball x δ = -x +ᵥ thickening δ s := by simp [sub_eq_add_neg]
@[simp] lemma ball_add : ball x δ + s = x +ᵥ thickening δ s := by rw [add_comm, add_ball]
@[simp] lemma ball_sub : ball x δ - s = x +ᵥ thickening δ (-s) := by simp [sub_eq_add_neg]

variables {ε δ s t x y}

lemma is_compact.add_closed_ball_zero (hs : is_compact s) (hδ : 0 ≤ δ) :
  s + closed_ball 0 δ = cthickening δ s :=
begin
  rw hs.cthickening_eq_bUnion_closed_ball hδ,
  ext x,
  simp only [mem_add, dist_eq_norm, exists_prop, mem_Union, mem_closed_ball,
    exists_and_distrib_left, mem_closed_ball_zero_iff, ← eq_sub_iff_add_eq', exists_eq_right],
end

lemma is_compact.sub_closed_ball_zero (hs : is_compact s) (hδ : 0 ≤ δ) :
  s - closed_ball 0 δ = cthickening δ s :=
by simp [sub_eq_add_neg, hs.add_closed_ball_zero hδ]

lemma is_compact.closed_ball_zero_add (hs : is_compact s) (hδ : 0 ≤ δ) :
  closed_ball 0 δ + s = cthickening δ s :=
by rw [add_comm, hs.add_closed_ball_zero hδ]

lemma is_compact.closed_ball_zero_sub (hs : is_compact s) (hδ : 0 ≤ δ) :
  closed_ball 0 δ - s = cthickening δ (-s) :=
by simp [sub_eq_add_neg, add_comm, hs.neg.add_closed_ball_zero hδ]

lemma is_compact.add_closed_ball (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  s + closed_ball x δ = x +ᵥ cthickening δ s :=
by rw [←vadd_closed_ball_zero, add_vadd_comm, hs.add_closed_ball_zero hδ]

lemma is_compact.sub_closed_ball (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  s - closed_ball x δ = -x +ᵥ cthickening δ s :=
by simp [sub_eq_add_neg, add_comm, hs.add_closed_ball hδ]

lemma is_compact.closed_ball_add (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  closed_ball x δ + s = x +ᵥ cthickening δ s :=
by rw [add_comm, hs.add_closed_ball hδ]

lemma is_compact.closed_ball_sub (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  closed_ball x δ + s = x +ᵥ cthickening δ s :=
by simp [sub_eq_add_neg, add_comm, hs.closed_ball_add hδ]

end semi_normed_group
