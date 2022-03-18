/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed.group.basic
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise addition of sets in normed groups.

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

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

lemma metric.bounded.add
  {s t : set E} (hs : bounded s) (ht : bounded t) :
  bounded (s + t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ (R : ℝ), ∀ x ∈ s, ∥x∥ ≤ R := hs.exists_norm_le,
  obtain ⟨Rt, hRt⟩ : ∃ (R : ℝ), ∀ x ∈ t, ∥x∥ ≤ R := ht.exists_norm_le,
  refine (bounded_iff_exists_norm_le).2 ⟨Rs + Rt, _⟩,
  rintros z ⟨x, y, hx, hy, rfl⟩,
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ : norm_add_le _ _
  ... ≤ Rs + Rt : add_le_add (hRs x hx) (hRt y hy)
end

variables {ε δ : ℝ} {s : set E}

lemma ennreal.of_real_of_nonpos {r : ℝ} (hr : r ≤ 0) : ennreal.of_real r = 0 :=
congr_arg coe $ real.to_nnreal_of_nonpos hr

lemma thickening_of_nonpos (hδ : δ ≤ 0) (s : set E) : thickening δ s = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx,
  (ennreal.of_real_of_nonpos hδ).not_gt $ bot_le.trans_lt hx

@[simp] lemma thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (s : set E) :
  thickening ε (thickening δ s) = thickening (ε + δ) s := sorry

@[simp] lemma thickening_cthickening (hε : 0 < ε) (hδ : 0 ≤ δ) (s : set E) :
  thickening ε (cthickening δ s) = thickening (ε + δ) s := sorry

@[simp] lemma cthickening_thickening (hε : 0 ≤ ε) (hδ : 0 < δ) (s : set E) :
  cthickening ε (thickening δ s) = cthickening (ε + δ) s := sorry

@[simp] lemma cthickening_cthickening (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : set E) :
  cthickening ε (cthickening δ s) = cthickening (ε + δ) s := sorry

@[simp] lemma thickening_ball (hε : 0 < ε) (hδ : 0 < δ) (x : E) :
  thickening ε (ball x δ) = ball x (ε + δ) :=
by rw [←thickening_singleton, thickening_thickening hε hδ, thickening_singleton]

@[simp] lemma thickening_closed_ball (hε : 0 < ε) (hδ : 0 ≤ δ) (x : E) :
  thickening ε (closed_ball x δ) = ball x (ε + δ) :=
by rw [←cthickening_singleton _ hδ, thickening_cthickening hε hδ, thickening_singleton]

@[simp] lemma cthickening_ball (hε : 0 ≤ ε) (hδ : 0 < δ) (x : E) :
  cthickening ε (ball x δ) = closed_ball x (ε + δ) :=
by rw [←thickening_singleton, cthickening_thickening hε hδ,
  cthickening_singleton _ (add_nonneg hε hδ.le)]

@[simp] lemma cthickening_closed_ball (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (x : E) :
  cthickening ε (closed_ball x δ) = closed_ball x (ε + δ) :=
by rw [←cthickening_singleton _ hδ, cthickening_cthickening hε hδ,
  cthickening_singleton _ (add_nonneg hε hδ)]

@[simp] lemma singleton_add_ball (x y : E) (δ : ℝ) : {x} + ball y δ = ball (x + y) δ :=
by simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_comm y x]

@[simp] lemma ball_add_singleton (x y : E) (δ : ℝ) : ball x δ + {y} = ball (x + y) δ :=
by simp [add_comm _ {y}, add_comm y]

@[simp] lemma vadd_ball (x y : E) (δ : ℝ) : x +ᵥ ball y δ = ball (x + y) δ :=
by { rw ←singleton_vadd, exact singleton_add_ball _ _ _ }

@[simp] lemma singleton_add_ball_zero (x : E) (δ : ℝ) : {x} + ball 0 δ = ball x δ := by simp
@[simp] lemma ball_zero_add_singleton (x : E) (δ : ℝ) : ball 0 δ + {x} = ball x δ := by simp
@[simp] lemma vadd_ball_zero (x : E) (δ : ℝ) : x +ᵥ ball 0 δ = ball x δ := by simp

@[simp] lemma singleton_add_closed_ball (x y : E) (δ : ℝ) :
  {x} + closed_ball y δ = closed_ball (x + y) δ :=
by simp only [add_comm y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

@[simp] lemma closed_ball_add_singleton (x y : E) (δ : ℝ) :
  closed_ball x δ + {y} = closed_ball (x + y) δ :=
by simp [add_comm _ {y}, add_comm y]

@[simp] lemma vadd_closed_ball (x y : E) (δ : ℝ) : x +ᵥ closed_ball y δ = closed_ball (x + y) δ :=
by { rw ←singleton_vadd, exact singleton_add_closed_ball _ _ _ }

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

@[simp] lemma ball_add_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) :
  ball a ε + ball b δ = ball (a + b) (ε + δ) :=
by rw [ball_add, thickening_ball hε hδ, vadd_ball]

@[simp] lemma ball_add_closed_ball (hε : 0 < ε) (hδ : 0 ≤ δ) (a b : E) :
  ball a ε + closed_ball b δ = ball (a + b) (ε + δ) :=
by rw [ball_add, thickening_closed_ball hε hδ, vadd_ball]

@[simp] lemma closed_ball_add_closed_ball (a b : E) (ε δ : ℝ) :
  closed_ball a ε + closed_ball b δ = closed_ball (a + b) (ε + δ) := sorry

end semi_normed_group
