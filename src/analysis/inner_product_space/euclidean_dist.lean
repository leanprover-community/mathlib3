/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.inner_product_space.calculus
import analysis.inner_product_space.pi_L2

/-!
# Euclidean distance on a finite dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `to_euclidean` to be
an equivalence between a finite dimensional normed space and the standard Euclidean space of the
same dimension. Then we define `euclidean.dist x y = dist (to_euclidean x) (to_euclidean y)` and
provide some definitions (`euclidean.ball`, `euclidean.closed_ball`) and simple lemmas about this
distance. This way we hide the usage of `to_euclidean` behind an API.
-/

open_locale topological_space
open set

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

noncomputable theory

/-- If `E` is a finite dimensional space over `ℝ`, then `to_euclidean` is a continuous `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension. -/
def to_euclidean : E ≃L[ℝ] euclidean_space ℝ (fin $ finite_dimensional.finrank ℝ E) :=
continuous_linear_equiv.of_finrank_eq finrank_euclidean_space_fin.symm

namespace euclidean

/-- If `x` and `y` are two points in a finite dimensional space over `ℝ`, then `euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
def dist (x y : E) : ℝ := dist (to_euclidean x) (to_euclidean y)

/-- Closed ball w.r.t. the euclidean distance. -/
def closed_ball (x : E) (r : ℝ) : set E := {y | dist y x ≤ r}

/-- Open ball w.r.t. the euclidean distance. -/
def ball (x : E) (r : ℝ) : set E := {y | dist y x < r}

lemma ball_eq_preimage (x : E) (r : ℝ) :
  ball x r = to_euclidean ⁻¹' (metric.ball (to_euclidean x) r) :=
rfl

lemma closed_ball_eq_preimage (x : E) (r : ℝ) :
  closed_ball x r = to_euclidean ⁻¹' (metric.closed_ball (to_euclidean x) r) :=
rfl

lemma ball_subset_closed_ball {x : E} {r : ℝ} : ball x r ⊆ closed_ball x r :=
λ y (hy : _ < _), le_of_lt hy

lemma is_open_ball {x : E} {r : ℝ} : is_open (ball x r) :=
metric.is_open_ball.preimage to_euclidean.continuous

lemma mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ ball x r := metric.mem_ball_self hr

lemma closed_ball_eq_image (x : E) (r : ℝ) :
  closed_ball x r = to_euclidean.symm '' metric.closed_ball (to_euclidean x) r :=
by rw [to_euclidean.image_symm_eq_preimage, closed_ball_eq_preimage]

lemma is_compact_closed_ball {x : E} {r : ℝ} : is_compact (closed_ball x r) :=
begin
  rw closed_ball_eq_image,
  exact (proper_space.is_compact_closed_ball _ _).image to_euclidean.symm.continuous
end

lemma is_closed_closed_ball {x : E} {r : ℝ} : is_closed (closed_ball x r) :=
is_compact_closed_ball.is_closed

lemma closure_ball (x : E) {r : ℝ} (h : 0 < r) : closure (ball x r) = closed_ball x r :=
by rw [ball_eq_preimage, ← to_euclidean.preimage_closure, closure_ball (to_euclidean x) h,
  closed_ball_eq_preimage]

lemma exists_pos_lt_subset_ball {R : ℝ} {s : set E} {x : E}
  (hR : 0 < R) (hs : is_closed s) (h : s ⊆ ball x R) :
  ∃ r ∈ Ioo 0 R, s ⊆ ball x r :=
begin
  rw [ball_eq_preimage, ← image_subset_iff] at h,
  rcases exists_pos_lt_subset_ball hR (to_euclidean.is_closed_image.2 hs) h with ⟨r, hr, hsr⟩,
  exact ⟨r, hr, image_subset_iff.1 hsr⟩
end

lemma nhds_basis_closed_ball {x : E} :
  (𝓝 x).has_basis (λ r : ℝ, 0 < r) (closed_ball x) :=
begin
  rw [to_euclidean.to_homeomorph.nhds_eq_comap],
  exact metric.nhds_basis_closed_ball.comap _
end

lemma closed_ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : closed_ball x r ∈ 𝓝 x :=
nhds_basis_closed_ball.mem_of_mem hr

lemma nhds_basis_ball {x : E} :
  (𝓝 x).has_basis (λ r : ℝ, 0 < r) (ball x) :=
begin
  rw [to_euclidean.to_homeomorph.nhds_eq_comap],
  exact metric.nhds_basis_ball.comap _
end

lemma ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ball x r ∈ 𝓝 x :=
nhds_basis_ball.mem_of_mem hr

end euclidean

variables {F : Type*} [normed_group F] [normed_space ℝ F] {f g : F → E} {n : with_top ℕ}

lemma times_cont_diff.euclidean_dist (hf : times_cont_diff ℝ n f) (hg : times_cont_diff ℝ n g)
  (h : ∀ x, f x ≠ g x) :
  times_cont_diff ℝ n (λ x, euclidean.dist (f x) (g x)) :=
begin
  simp only [euclidean.dist],
  apply @times_cont_diff.dist ℝ,
  exacts [(@to_euclidean E _ _ _).times_cont_diff.comp hf,
    (@to_euclidean E _ _ _).times_cont_diff.comp hg, λ x, to_euclidean.injective.ne (h x)]
end
