/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.normed_space.basic
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise addition and scalar multiplication of sets in normed spaces.

We explore the relationships between pointwise addition and scalar multiplication of sets in
vector spaces, and the norm. Notably, we express arbitrary balls as rescaling of other balls,
and we show that the sum or multiplication of bounded sets remain bounded.
-/

open metric set
open_locale pointwise topological_space

section semi_normed_group

variables {E : Type*} [semi_normed_group E]

lemma metric.bounded.add
  {s t : set E} (hs : bounded s) (ht : bounded t) :
  bounded (s + t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ (R : ℝ), s ⊆ closed_ball 0 R := hs.subset_ball 0,
  obtain ⟨Rt, hRt⟩ : ∃ (R : ℝ), t ⊆ closed_ball 0 R := ht.subset_ball 0,
  refine (bounded_iff_subset_ball 0).2 ⟨Rs + Rt, _⟩,
  rintros z ⟨x, y, hx, hy, rfl⟩,
  rw mem_closed_ball_zero_iff,
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ : norm_add_le _ _
  ... ≤ Rs + Rt :
    add_le_add (mem_closed_ball_zero_iff.1 (hRs hx)) (mem_closed_ball_zero_iff.1 (hRt hy))
end

@[simp] lemma singleton_add_ball (x y : E) (r : ℝ) :
  {x} + ball y r = ball (x + y) r :=
by simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_comm y x]

lemma singleton_add_ball_zero (x : E) (r : ℝ) :
  {x} + ball 0 r = ball x r :=
by simp

@[simp] lemma singleton_add_closed_ball (x y : E) (r : ℝ) :
  {x} + closed_ball y r = closed_ball (x + y) r :=
by simp only [add_comm y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

lemma singleton_add_closed_ball_zero (x : E) (r : ℝ) :
  {x} + closed_ball 0 r = closed_ball x r :=
by simp

end semi_normed_group

section semi_normed_space

variables {𝕜 : Type*} [normed_field 𝕜] {E : Type*} [semi_normed_group E] [semi_normed_space 𝕜 E]

theorem smul_ball {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • ball x r = ball (c • x) (∥c∥ * r) :=
begin
  ext y,
  rw mem_smul_set_iff_inv_smul_mem₀ hc,
  conv_lhs { rw ←inv_smul_smul₀ hc x },
  simp [← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hc), mul_comm _ r, dist_smul],
end

theorem smul_sphere' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • sphere x r = sphere (c • x) (∥c∥ * r) :=
begin
  ext y,
  rw mem_smul_set_iff_inv_smul_mem₀ hc,
  conv_lhs { rw ←inv_smul_smul₀ hc x },
  simp only [mem_sphere, dist_smul, normed_field.norm_inv, ← div_eq_inv_mul,
    div_eq_iff (norm_pos_iff.2 hc).ne', mul_comm r],
end

/-- In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp] theorem normed_space.sphere_nonempty {E : Type*} [normed_group E]
  [normed_space ℝ E] [nontrivial E] {x : E} {r : ℝ} :
  (sphere x r).nonempty ↔ 0 ≤ r :=
begin
  refine ⟨λ h, nonempty_closed_ball.1 (h.mono sphere_subset_closed_ball), λ hr, _⟩,
  rcases exists_ne x with ⟨y, hy⟩,
  have : ∥y - x∥ ≠ 0, by simpa [sub_eq_zero],
  use r • ∥y - x∥⁻¹ • (y - x) + x,
  simp [norm_smul, this, real.norm_of_nonneg hr]
end

theorem smul_sphere {E : Type*} [normed_group E] [normed_space 𝕜 E] [normed_space ℝ E]
  [nontrivial E] (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  c • sphere x r = sphere (c • x) (∥c∥ * r) :=
begin
  rcases eq_or_ne c 0 with rfl|hc,
  { simp [zero_smul_set, set.singleton_zero, hr] },
  { exact smul_sphere' hc x r }
end

theorem smul_closed_ball' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥ * r) :=
by simp only [← ball_union_sphere, set.smul_set_union, smul_ball hc, smul_sphere' hc]

lemma metric.bounded.smul {s : set E} (hs : bounded s) (c : 𝕜) :
  bounded (c • s) :=
begin
  obtain ⟨R, Rpos, hR⟩ : ∃ (R : ℝ), 0 < R ∧ s ⊆ closed_ball 0 R := hs.subset_ball_lt 0 0,
  refine (bounded_iff_subset_ball 0).2 ⟨∥c∥ * R, _⟩,
  assume z hz,
  obtain ⟨y, ys, rfl⟩ : ∃ (y : E), y ∈ s ∧ c • y = z := mem_smul_set.1 hz,
  simp only [mem_closed_ball_zero_iff],
  calc ∥c • y∥ = ∥c∥ * ∥y∥ : norm_smul _ _
  ... ≤ ∥c∥ * R : mul_le_mul_of_nonneg_left (mem_closed_ball_zero_iff.1 (hR ys)) (norm_nonneg _)
end

/-- If `s` is a bounded set, then for small enough `r`, the set `{x} + r • s` is contained in any
fixed neighborhood of `x`. -/
lemma eventually_singleton_add_smul_subset
  {x : E} {s : set E} (hs : bounded s) {u : set E} (hu : u ∈ 𝓝 x) :
  ∀ᶠ r in 𝓝 (0 : 𝕜), {x} + r • s ⊆ u :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ ε (hε : 0 < ε), closed_ball x ε ⊆ u :=
    nhds_basis_closed_ball.mem_iff.1 hu,
  obtain ⟨R, Rpos, hR⟩ : ∃ (R : ℝ), 0 < R ∧ s ⊆ closed_ball 0 R := hs.subset_ball_lt 0 0,
  have : metric.closed_ball (0 : 𝕜) (ε / R) ∈ 𝓝 (0 : 𝕜) :=
    closed_ball_mem_nhds _ (div_pos εpos Rpos),
  filter_upwards [this],
  assume r hr,
  simp only [image_add_left, singleton_add],
  assume y hy,
  obtain ⟨z, zs, hz⟩ : ∃ (z : E), z ∈ s ∧ r • z = -x + y, by simpa [mem_smul_set] using hy,
  have I : ∥r • z∥ ≤ ε := calc
    ∥r • z∥ = ∥r∥ * ∥z∥ : norm_smul _ _
    ... ≤ (ε / R) * R :
      mul_le_mul (mem_closed_ball_zero_iff.1 hr)
        (mem_closed_ball_zero_iff.1 (hR zs)) (norm_nonneg _) (div_pos εpos Rpos).le
    ... = ε : by field_simp [Rpos.ne'],
  have : y = x + r • z, by simp only [hz, add_neg_cancel_left],
  apply hε,
  simpa only [this, dist_eq_norm, add_sub_cancel', mem_closed_ball] using I,
end

lemma set_smul_mem_nhds_zero {s : set E} (hs : s ∈ 𝓝 (0 : E)) {c : 𝕜} (hc : c ≠ 0) :
  c • s ∈ 𝓝 (0 : E) :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : 0 < ε), ball 0 ε ⊆ s := metric.mem_nhds_iff.1 hs,
  have : c • ball (0 : E) ε ∈ 𝓝 (0 : E),
  { rw [smul_ball hc, smul_zero],
    exact ball_mem_nhds _ (mul_pos (by simpa using hc) εpos) },
  exact filter.mem_of_superset this ((set_smul_subset_set_smul_iff₀ hc).2 hε)
end

lemma set_smul_mem_nhds_zero_iff (s : set E) {c : 𝕜} (hc : c ≠ 0) :
  c • s ∈ 𝓝 (0 : E) ↔ s ∈ 𝓝(0 : E) :=
begin
  refine ⟨λ h, _, λ h, set_smul_mem_nhds_zero h hc⟩,
  convert set_smul_mem_nhds_zero h (inv_ne_zero hc),
  rw [smul_smul, inv_mul_cancel hc, one_smul],
end

end semi_normed_space

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]

theorem smul_closed_ball (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥ * r) :=
begin
  rcases eq_or_ne c 0 with rfl|hc,
  { simp [hr, zero_smul_set, set.singleton_zero, ← nonempty_closed_ball] },
  { exact smul_closed_ball' hc x r }
end

end normed_space
