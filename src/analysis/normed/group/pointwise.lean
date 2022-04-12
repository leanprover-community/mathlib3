/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.convex.basic
import analysis.normed.group.add_torsor
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

section
variables {α : Type*} [ordered_semiring α] {a b : α}

lemma mul_lt_of_lt_one_left (hb : 0 < b) (ha : a < 1) : a * b < b :=
(mul_lt_mul_of_pos_right ha hb).trans_le (one_mul _).le

lemma mul_lt_of_lt_one_right (ha : 0 < a) (hb : b < 1) : a * b < a :=
(mul_lt_mul_of_pos_left hb ha).trans_le (mul_one _).le

end

namespace emetric
variables {α : Type*} [pseudo_emetric_space α] {δ ε : ℝ} {s : set α} {x y : α}

lemma inf_edist_le_edist_add_inf_edist : inf_edist x s ≤ edist x y + inf_edist y s :=
by { rw add_comm, exact inf_edist_le_inf_edist_add_edist }

end emetric

namespace metric
variables {α : Type*} [pseudo_emetric_space α] {δ ε : ℝ} {s : set α} {x : α}

open emetric set

alias ennreal.of_real_eq_zero ↔ _ ennreal.of_real_of_nonpos

lemma mem_cthickening_iff : x ∈ cthickening δ s ↔ inf_edist x s ≤ ennreal.of_real δ := iff.rfl

lemma thickening_of_nonpos (hδ : δ ≤ 0) (s : set α) : thickening δ s = ∅ :=
eq_empty_of_subset_empty $ λ x hx, (ennreal.of_real_of_nonpos hδ).not_gt $ bot_le.trans_lt hx

@[simp] lemma cthickening_closure : cthickening δ (closure s) = cthickening δ s :=
by simp_rw [cthickening, inf_edist_closure]

@[simp] lemma thickening_thickening_subset (ε δ : ℝ) (s : set α) :
  thickening ε (thickening δ s) ⊆ thickening (ε + δ) s :=
begin
  obtain hε | hε := le_total ε 0,
  { simp only [thickening_of_nonpos hε, empty_subset] },
  obtain hδ | hδ := le_total δ 0,
  { simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset] },
  intros x,
  simp_rw [mem_thickening_iff_exists_edist_lt, ennreal.of_real_add hε hδ],
  exact λ ⟨y, ⟨z, hz, hy⟩, hx⟩, ⟨z, hz, (edist_triangle _ _ _).trans_lt $ ennreal.add_lt_add hx hy⟩,
end

@[simp] lemma thickening_cthickening_subset (ε : ℝ) (hδ : 0 ≤ δ) (s : set α) :
  thickening ε (cthickening δ s) ⊆ thickening (ε + δ) s :=
begin
  obtain hε | hε := le_total ε 0,
  { simp only [thickening_of_nonpos hε, empty_subset] },
  intro x,
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ←inf_edist_lt_iff,
    ennreal.of_real_add hε hδ],
  rintro ⟨y, hy, hxy⟩,
  refine inf_edist_le_edist_add_inf_edist.trans_lt sorry,
  sorry -- done by `with_top.add_lt_add_of_lt_of_le`
end

lemma inf_edist_le_inf_edist_thickening_add :
  inf_edist x s ≤ inf_edist x (thickening δ s) + ennreal.of_real δ :=
begin
  refine le_of_forall_lt' (λ r h, _),
  simp_rw [←lt_tsub_iff_right, inf_edist_lt_iff, mem_thickening_iff_exists_edist_lt] at h,
  obtain ⟨y, ⟨z, hz, hyz⟩, hxy⟩ := h,
  rw inf_edist_lt_iff,
  refine ⟨z, hz, (edist_triangle _ _ _).trans_lt $ (ennreal.add_lt_add hxy hyz).trans_le
    (tsub_add_cancel_of_le (tsub_pos_iff_lt.1 $ bot_le.trans_lt hxy).le).le⟩,
end

lemma inf_edist_le_inf_edist_cthickening_add :
  inf_edist x s ≤ inf_edist x (cthickening δ s) + ennreal.of_real δ :=
begin
  refine le_of_forall_lt' (λ r h, _),
  simp_rw [←lt_tsub_iff_right, inf_edist_lt_iff, mem_cthickening_iff] at h,
  obtain ⟨y, hy, hxy⟩ := h,
  refine inf_edist_le_edist_add_inf_edist.trans_lt _,
  sorry, sorry -- done
end

@[simp] lemma cthickening_thickening_subset (hε : 0 ≤ ε) (δ : ℝ) (s : set α) :
  cthickening ε (thickening δ s) ⊆ cthickening (ε + δ) s :=
begin
  obtain hδ | hδ := le_total δ 0,
  { simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset] },
  intro x,
  simp_rw [mem_cthickening_iff, ennreal.of_real_add hε hδ],
  exact λ hx, inf_edist_le_inf_edist_thickening_add.trans (add_le_add_right hx _),
end

@[simp] lemma cthickening_cthickening_subset (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : set α) :
  cthickening ε (cthickening δ s) ⊆ cthickening (ε + δ) s :=
begin
  intro x,
  simp_rw [mem_cthickening_iff, ennreal.of_real_add hε hδ],
  exact λ hx, inf_edist_le_inf_edist_cthickening_add.trans (add_le_add_right hx _),
end

end metric

open metric set
open_locale pointwise topological_space

section semi_normed_group

variables {E : Type*} [semi_normed_group E]

lemma bounded_iff_exists_norm_le {s : set E} :
  bounded s ↔ ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
by simp [subset_def, bounded_iff_subset_ball (0 : E)]

alias bounded_iff_exists_norm_le ↔ metric.bounded.exists_norm_le _

lemma metric.bounded.exists_pos_norm_le {s : set E} (hs : metric.bounded s) :
  ∃ R > 0, ∀ x ∈ s, ∥x∥ ≤ R :=
begin
  obtain ⟨R₀, hR₀⟩ := hs.exists_norm_le,
  refine ⟨max R₀ 1, _, _⟩,
  { exact (by norm_num : (0:ℝ) < 1).trans_le (le_max_right R₀ 1) },
  intros x hx,
  exact (hR₀ x hx).trans (le_max_left _ _),
end

lemma metric.bounded.add {s t : set E} (hs : bounded s) (ht : bounded t) : bounded (s + t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ (R : ℝ), ∀ x ∈ s, ∥x∥ ≤ R := hs.exists_norm_le,
  obtain ⟨Rt, hRt⟩ : ∃ (R : ℝ), ∀ x ∈ t, ∥x∥ ≤ R := ht.exists_norm_le,
  refine (bounded_iff_exists_norm_le).2 ⟨Rs + Rt, _⟩,
  rintros z ⟨x, y, hx, hy, rfl⟩,
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ : norm_add_le _ _
  ... ≤ Rs + Rt : add_le_add (hRs x hx) (hRt y hy)
end

variables {ε δ : ℝ} {s : set E}

@[simp] lemma singleton_add_ball (x y : E) (δ : ℝ) : {x} + ball y δ = ball (x + y) δ :=
by simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_comm y x]

@[simp] lemma ball_add_singleton (x y : E) (δ : ℝ) : ball x δ + {y} = ball (x + y) δ :=
by rw [add_comm _ {y}, singleton_add_ball, add_comm y]

@[simp] lemma singleton_add_ball_zero (x : E) (δ : ℝ) : {x} + ball 0 δ = ball x δ := by simp
@[simp] lemma ball_zero_add_singleton (x : E) (δ : ℝ) : ball 0 δ + {x} = ball x δ := by simp
@[simp] lemma vadd_ball_zero (x : E) (δ : ℝ) : x +ᵥ ball 0 δ = ball x δ := by simp

@[simp] lemma singleton_add_closed_ball (x y : E) (δ : ℝ) :
  {x} + closed_ball y δ = closed_ball (x + y) δ :=
by simp only [add_comm y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

@[simp] lemma closed_ball_add_singleton (x y : E) (δ : ℝ) :
  closed_ball x δ + {y} = closed_ball (x + y) δ :=
by simp [add_comm _ {y}, add_comm y]

lemma singleton_add_closed_ball_zero (x : E) (δ : ℝ) : {x} + closed_ball 0 δ = closed_ball x δ :=
by simp

lemma closed_ball_zero_add_singleton (x : E) (δ : ℝ) : closed_ball 0 δ + {x} = closed_ball x δ :=
by simp

@[simp] lemma vadd_closed_ball_zero (x : E) (δ : ℝ) : x +ᵥ closed_ball 0 δ = closed_ball x δ :=
by simp

@[simp] lemma add_ball_zero (s : set E) (δ : ℝ) : s + ball 0 δ = thickening δ s :=
begin
  rw thickening_eq_bUnion_ball,
  convert Union₂_add (λ x (_ : x ∈ s), {x}) (ball (0 : E) δ),
  exact s.bUnion_of_singleton.symm,
  ext x y,
  simp_rw [singleton_add_ball, add_zero],
end

@[simp] lemma ball_add_zero (δ : ℝ) (s : set E) : ball 0 δ + s = thickening δ s :=
by rw [add_comm, add_ball_zero]

@[simp] lemma add_ball (δ : ℝ) (s : set E) (x : E) : s + ball x δ = x +ᵥ thickening δ s :=
by rw [←vadd_ball_zero, add_vadd_comm, add_ball_zero]

@[simp] lemma ball_add (δ : ℝ) (s : set E) (x : E) : ball x δ + s = x +ᵥ thickening δ s :=
by rw [add_comm, add_ball]

lemma is_compact.add_closed_ball_zero (hs : is_compact s)  (hδ : 0 ≤ δ) :
  s + closed_ball 0 δ = cthickening δ s :=
begin
  rw hs.cthickening_eq_bUnion_closed_ball hδ,
  ext x,
  simp only [mem_add, dist_eq_norm, exists_prop, mem_Union, mem_closed_ball,
    exists_and_distrib_left, mem_closed_ball_zero_iff, ← eq_sub_iff_add_eq', exists_eq_right],
end

lemma is_compact.closed_ball_zero_add (hs : is_compact s) (hδ : 0 ≤ δ) :
  closed_ball 0 δ + s = cthickening δ s :=
by rw [add_comm, hs.add_closed_ball_zero hδ]

lemma is_compact.add_closed_ball (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  s + closed_ball x δ = x +ᵥ cthickening δ s :=
by rw [←vadd_closed_ball_zero, add_vadd_comm, hs.add_closed_ball_zero hδ]

lemma is_compact.closed_ball_add (hs : is_compact s) (hδ : 0 ≤ δ) (x : E) :
  closed_ball x δ + s = x +ᵥ cthickening δ s :=
by rw [add_comm, hs.add_closed_ball hδ]

end semi_normed_group
