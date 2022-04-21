/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
import analysis.normed.group.pointwise
import analysis.normed.group.add_torsor
import analysis.normed_space.basic
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise scalar multiplication of sets in normed spaces.

We explore the relationships between scalar multiplication of sets in vector spaces, and the norm.
Notably, we express arbitrary balls as rescaling of other balls, and we show that the
multiplication of bounded sets remain bounded.
-/

open metric set
open_locale pointwise topological_space

variables {𝕜 E : Type*} [normed_field 𝕜]

section semi_normed_group
variables [semi_normed_group E] [normed_space 𝕜 E]

theorem smul_ball {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • ball x r = ball (c • x) (∥c∥ * r) :=
begin
  ext y,
  rw mem_smul_set_iff_inv_smul_mem₀ hc,
  conv_lhs { rw ←inv_smul_smul₀ hc x },
  simp [← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hc), mul_comm _ r, dist_smul],
end

lemma smul_unit_ball {c : 𝕜} (hc : c ≠ 0) : c • ball (0 : E) (1 : ℝ) = ball (0 : E) (∥c∥) :=
by rw [smul_ball hc, smul_zero, mul_one]

theorem smul_sphere' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • sphere x r = sphere (c • x) (∥c∥ * r) :=
begin
  ext y,
  rw mem_smul_set_iff_inv_smul_mem₀ hc,
  conv_lhs { rw ←inv_smul_smul₀ hc x },
  simp only [mem_sphere, dist_smul, norm_inv, ← div_eq_inv_mul,
    div_eq_iff (norm_pos_iff.2 hc).ne', mul_comm r],
end

theorem smul_closed_ball' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥ * r) :=
by simp only [← ball_union_sphere, set.smul_set_union, smul_ball hc, smul_sphere' hc]

lemma metric.bounded.smul {s : set E} (hs : bounded s) (c : 𝕜) :
  bounded (c • s) :=
begin
  obtain ⟨R, hR⟩ : ∃ (R : ℝ), ∀ x ∈ s, ∥x∥ ≤ R := hs.exists_norm_le,
  refine (bounded_iff_exists_norm_le).2 ⟨∥c∥ * R, _⟩,
  assume z hz,
  obtain ⟨y, ys, rfl⟩ : ∃ (y : E), y ∈ s ∧ c • y = z := mem_smul_set.1 hz,
  calc ∥c • y∥ = ∥c∥ * ∥y∥ : norm_smul _ _
  ... ≤ ∥c∥ * R : mul_le_mul_of_nonneg_left (hR y ys) (norm_nonneg _)
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
  filter_upwards [this] with r hr,
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

/-- Any ball is the image of a ball centered at the origin under a shift. -/
lemma vadd_ball_zero (x : E) (r : ℝ) : x +ᵥ ball 0 r = ball x r :=
by rw [vadd_ball, vadd_eq_add, add_zero]

/-- Any closed ball is the image of a closed ball centered at the origin under a shift. -/
lemma vadd_closed_ball_zero (x : E) (r : ℝ) : x +ᵥ closed_ball 0 r = closed_ball x r :=
by rw [vadd_closed_ball, vadd_eq_add, add_zero]

variables [normed_space ℝ E] {x y z : E} {δ ε : ℝ}

/-- In a real normed space, the image of the unit ball under scalar multiplication by a positive
constant `r` is the ball of radius `r`. -/
lemma smul_unit_ball_of_pos {r : ℝ} (hr : 0 < r) : r • ball 0 1 = ball (0 : E) r :=
by rw [smul_unit_ball hr.ne', real.norm_of_nonneg hr.le]

-- This is also true for `ℚ`-normed spaces
lemma exists_dist_eq (x z : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  ∃ y, dist x y = b * dist x z ∧ dist y z = a * dist x z :=
begin
  use a • x + b • z,
  nth_rewrite 0 [←one_smul ℝ x],
  nth_rewrite 3 [←one_smul ℝ z],
  simp [dist_eq_norm, ←hab, add_smul, ←smul_sub, norm_smul_of_nonneg, ha, hb],
end

lemma exists_dist_le_le (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (h : dist x z ≤ ε + δ) :
  ∃ y, dist x y ≤ δ ∧ dist y z ≤ ε :=
begin
  obtain rfl | hε' := hε.eq_or_lt,
  { exact ⟨z, by rwa zero_add at h, (dist_self _).le⟩ },
  have hεδ := add_pos_of_pos_of_nonneg hε' hδ,
  refine (exists_dist_eq x z (div_nonneg hε $ add_nonneg hε hδ) (div_nonneg hδ $ add_nonneg hε hδ) $
    by rw [←add_div, div_self hεδ.ne']).imp (λ y hy, _),
  rw [hy.1, hy.2, div_mul_comm', div_mul_comm' ε],
  rw ←div_le_one hεδ at h,
  exact ⟨mul_le_of_le_one_left hδ h, mul_le_of_le_one_left hε h⟩,
end

-- This is also true for `ℚ`-normed spaces
lemma exists_dist_le_lt (hδ : 0 ≤ δ) (hε : 0 < ε) (h : dist x z < ε + δ) :
  ∃ y, dist x y ≤ δ ∧ dist y z < ε :=
begin
  refine (exists_dist_eq x z (div_nonneg hε.le $ add_nonneg hε.le hδ) (div_nonneg hδ $ add_nonneg
    hε.le hδ) $ by rw [←add_div, div_self (add_pos_of_pos_of_nonneg hε hδ).ne']).imp (λ y hy, _),
  rw [hy.1, hy.2, div_mul_comm', div_mul_comm' ε],
  rw ←div_lt_one (add_pos_of_pos_of_nonneg hε hδ) at h,
  exact ⟨mul_le_of_le_one_left hδ h.le, mul_lt_of_lt_one_left hε h⟩,
end

-- This is also true for `ℚ`-normed spaces
lemma exists_dist_lt_le (hδ : 0 < δ) (hε : 0 ≤ ε) (h : dist x z < ε + δ) :
  ∃ y, dist x y < δ ∧ dist y z ≤ ε :=
begin
  obtain ⟨y, yz, xy⟩ := exists_dist_le_lt hε hδ
    (show dist z x < δ + ε, by simpa only [dist_comm, add_comm] using h),
  exact ⟨y, by simp [dist_comm x y, dist_comm y z, *]⟩,
end

-- This is also true for `ℚ`-normed spaces
lemma exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ) :
  ∃ y, dist x y < δ ∧ dist y z < ε :=
begin
  refine (exists_dist_eq x z (div_nonneg hε.le $ add_nonneg hε.le hδ.le) (div_nonneg hδ.le $
    add_nonneg hε.le hδ.le) $ by rw [←add_div, div_self (add_pos hε hδ).ne']).imp (λ y hy, _),
  rw [hy.1, hy.2, div_mul_comm', div_mul_comm' ε],
  rw ←div_lt_one (add_pos hε hδ) at h,
  exact ⟨mul_lt_of_lt_one_left hδ h, mul_lt_of_lt_one_left hε h⟩,
end

-- This is also true for `ℚ`-normed spaces
lemma disjoint_ball_ball_iff (hδ : 0 < δ) (hε : 0 < ε) :
  disjoint (ball x δ) (ball y ε) ↔ δ + ε ≤ dist x y :=
begin
  refine ⟨λ h, le_of_not_lt $ λ hxy, _, ball_disjoint_ball⟩,
  rw add_comm at hxy,
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_lt hδ hε hxy,
  rw dist_comm at hxz,
  exact h ⟨hxz, hzy⟩,
end

-- This is also true for `ℚ`-normed spaces
lemma disjoint_ball_closed_ball_iff (hδ : 0 < δ) (hε : 0 ≤ ε) :
  disjoint (ball x δ) (closed_ball y ε) ↔ δ + ε ≤ dist x y :=
begin
  refine ⟨λ h, le_of_not_lt $ λ hxy, _, ball_disjoint_closed_ball⟩,
  rw add_comm at hxy,
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_le hδ hε hxy,
  rw dist_comm at hxz,
  exact h ⟨hxz, hzy⟩,
end

-- This is also true for `ℚ`-normed spaces
lemma disjoint_closed_ball_ball_iff (hδ : 0 ≤ δ) (hε : 0 < ε) :
  disjoint (closed_ball x δ) (ball y ε) ↔ δ + ε ≤ dist x y :=
by rw [disjoint.comm, disjoint_ball_closed_ball_iff hε hδ, add_comm, dist_comm]; apply_instance

lemma disjoint_closed_ball_closed_ball_iff (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
  disjoint (closed_ball x δ) (closed_ball y ε) ↔ δ + ε < dist x y :=
begin
  refine ⟨λ h, lt_of_not_ge $ λ hxy, _, closed_ball_disjoint_closed_ball⟩,
  rw add_comm at hxy,
  obtain ⟨z, hxz, hzy⟩ := exists_dist_le_le hδ hε hxy,
  rw dist_comm at hxz,
  exact h ⟨hxz, hzy⟩,
end

end semi_normed_group

section normed_group
variables [normed_group E] [normed_space 𝕜 E]

theorem smul_closed_ball (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  c • closed_ball x r = closed_ball (c • x) (∥c∥ * r) :=
begin
  rcases eq_or_ne c 0 with rfl|hc,
  { simp [hr, zero_smul_set, set.singleton_zero, ← nonempty_closed_ball] },
  { exact smul_closed_ball' hc x r }
end

lemma smul_closed_unit_ball (c : 𝕜) : c • closed_ball (0 : E) (1 : ℝ) = closed_ball (0 : E) (∥c∥) :=
by rw [smul_closed_ball _ _ zero_le_one, smul_zero, mul_one]

variables [normed_space ℝ E]

/-- In a real normed space, the image of the unit closed ball under multiplication by a nonnegative
number `r` is the closed ball of radius `r` with center at the origin. -/
lemma smul_closed_unit_ball_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
  r • closed_ball 0 1 = closed_ball (0 : E) r :=
by rw [smul_closed_unit_ball, real.norm_of_nonneg hr]

/-- In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp] lemma normed_space.sphere_nonempty [nontrivial E] {x : E} {r : ℝ} :
  (sphere x r).nonempty ↔ 0 ≤ r :=
begin
  obtain ⟨y, hy⟩ := exists_ne x,
  refine ⟨λ h, nonempty_closed_ball.1 (h.mono sphere_subset_closed_ball), λ hr,
    ⟨r • ∥y - x∥⁻¹ • (y - x) + x, _⟩⟩,
  have : ∥y - x∥ ≠ 0, by simpa [sub_eq_zero],
  simp [norm_smul, this, real.norm_of_nonneg hr],
end

lemma smul_sphere [nontrivial E] (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) :
  c • sphere x r = sphere (c • x) (∥c∥ * r) :=
begin
  rcases eq_or_ne c 0 with rfl|hc,
  { simp [zero_smul_set, set.singleton_zero, hr] },
  { exact smul_sphere' hc x r }
end

/-- Any ball `metric.ball x r`, `0 < r` is the image of the unit ball under `λ y, x + r • y`. -/
lemma affinity_unit_ball {r : ℝ} (hr : 0 < r) (x : E) : x +ᵥ r • ball 0 1 = ball x r :=
by rw [smul_unit_ball_of_pos hr, vadd_ball_zero]

/-- Any closed ball `metric.closed_ball x r`, `0 ≤ r` is the image of the unit closed ball under
`λ y, x + r • y`. -/
lemma affinity_unit_closed_ball {r : ℝ} (hr : 0 ≤ r) (x : E) :
  x +ᵥ r • closed_ball 0 1 = closed_ball x r :=
by rw [smul_closed_unit_ball, real.norm_of_nonneg hr, vadd_closed_ball_zero]

end normed_group
