/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import measure_theory.measure.haar
import linear_algebra.finite_dimensional
import analysis.normed_space.pointwise

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`measure_theory.add_haar_measure_eq_volume` and `measure_theory.add_haar_measure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linear_map_add_haar_eq_smul_add_haar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `add_haar_preimage_linear_map` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `add_haar_image_linear_map` :  when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `add_haar_submodule` : a strict submodule has measure `0`.
* `add_haar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `add_haar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_closed_ball`: the measure of `closed_ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_sphere`: spheres have zero measure.

-/

open topological_space set filter metric
open_locale ennreal pointwise topological_space

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.Icc01 : positive_compacts ℝ :=
⟨Icc 0 1, is_compact_Icc, by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.pi_Icc01 (ι : Type*) [fintype ι] :
  positive_compacts (ι → ℝ) :=
⟨set.pi set.univ (λ i, Icc 0 1), is_compact_univ_pi (λ i, is_compact_Icc),
by simp only [interior_pi_set, finite.of_fintype, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
  implies_true_iff, zero_lt_one]⟩

namespace measure_theory

open measure topological_space.positive_compacts finite_dimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/

lemma is_add_left_invariant_real_volume : is_add_left_invariant ⇑(volume : measure ℝ) :=
by simp [← map_add_left_eq_self, real.map_volume_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
lemma add_haar_measure_eq_volume : add_haar_measure Icc01 = volume :=
begin
  convert (add_haar_measure_unique _ Icc01).symm,
  { simp [Icc01] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume }
end

instance : is_add_haar_measure (volume : measure ℝ) :=
by { rw ← add_haar_measure_eq_volume, apply_instance }

lemma is_add_left_invariant_real_volume_pi (ι : Type*) [fintype ι] :
  is_add_left_invariant ⇑(volume : measure (ι → ℝ)) :=
by simp [← map_add_left_eq_self, real.map_volume_pi_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
lemma add_haar_measure_eq_volume_pi (ι : Type*) [fintype ι] :
  add_haar_measure (pi_Icc01 ι) = volume :=
begin
  convert (add_haar_measure_unique _ (pi_Icc01 ι)).symm,
  { simp only [pi_Icc01, volume_pi_pi (λ i, Icc (0 : ℝ) 1),
      finset.prod_const_one, ennreal.of_real_one, real.volume_Icc, one_smul, sub_zero] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume_pi ι }
end

instance is_add_haar_measure_volume_pi (ι : Type*) [fintype ι] :
  is_add_haar_measure (volume : measure (ι → ℝ)) :=
by { rw ← add_haar_measure_eq_volume_pi, apply_instance }

namespace measure

/-!
### Strict subspaces have zero measure
-/

/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bounded. -/
lemma add_haar_eq_zero_of_disjoint_translates_aux
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {s : set E} (u : ℕ → E) (sb : bounded s) (hu : bounded (range u))
  (hs : pairwise (disjoint on (λ n, {u n} + s))) (h's : measurable_set s) :
  μ s = 0 :=
begin
  by_contra h,
  apply lt_irrefl ∞,
  calc
  ∞ = ∑' (n : ℕ), μ s : (ennreal.tsum_const_eq_top_of_ne_zero h).symm
  ... = ∑' (n : ℕ), μ ({u n} + s) :
    by { congr' 1, ext1 n, simp only [image_add_left, add_haar_preimage_add, singleton_add] }
  ... = μ (⋃ n, {u n} + s) :
    by rw measure_Union hs
      (λ n, by simpa only [image_add_left, singleton_add] using measurable_id.const_add _ h's)
  ... = μ (range u + s) : by rw [← Union_add, Union_singleton_eq_range]
  ... < ∞ : bounded.measure_lt_top (hu.add sb)
end

/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. -/
lemma add_haar_eq_zero_of_disjoint_translates
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {s : set E} (u : ℕ → E) (hu : bounded (range u))
  (hs : pairwise (disjoint on (λ n, {u n} + s))) (h's : measurable_set s) :
  μ s = 0 :=
begin
  suffices H : ∀ R, μ (s ∩ closed_ball 0 R) = 0,
  { apply le_antisymm _ (zero_le _),
    have : s ⊆ ⋃ (n : ℕ), s ∩ closed_ball 0 n,
    { assume x hx,
      obtain ⟨n, hn⟩ : ∃ (n : ℕ), ∥x∥ ≤ n := exists_nat_ge (∥x∥),
      exact mem_Union.2 ⟨n, ⟨hx, mem_closed_ball_zero_iff.2 hn⟩⟩ },
    calc μ s ≤ μ (⋃ (n : ℕ), s ∩ closed_ball 0 n) : measure_mono this
    ... ≤ ∑' (n : ℕ), μ (s ∩ closed_ball 0 n) : measure_Union_le _
    ... = 0 : by simp only [H, tsum_zero] },
  assume R,
  apply add_haar_eq_zero_of_disjoint_translates_aux μ u
    (bounded.mono (inter_subset_right _ _) bounded_closed_ball) hu _
    (h's.inter (measurable_set_closed_ball)),
  rw ← pairwise_univ at ⊢ hs,
  apply pairwise_disjoint.mono hs (λ n, _),
  exact add_subset_add (subset.refl _) (inter_subset_left _ _)
end

/-- A strict vector subspace has measure zero. -/
lemma add_haar_submodule
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  (s : submodule ℝ E) (hs : s ≠ ⊤) : μ s = 0 :=
begin
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s,
    by simpa only [submodule.eq_top_iff', not_exists, ne.def, not_forall] using hs,
  obtain ⟨c, cpos, cone⟩ : ∃ (c : ℝ), 0 < c ∧ c < 1 := ⟨1/2, by norm_num, by norm_num⟩,
  have A : bounded (range (λ (n : ℕ), (c ^ n) • x)),
  { have : tendsto (λ (n : ℕ), (c ^ n) • x) at_top (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_at_top_nhds_0_of_lt_1 cpos.le cone).smul_const x,
    exact bounded_range_of_tendsto _ this },
  apply add_haar_eq_zero_of_disjoint_translates μ _ A _
    (submodule.closed_of_finite_dimensional s).measurable_set,
  assume m n hmn,
  simp only [function.on_fun, image_add_left, singleton_add, disjoint_left, mem_preimage,
             set_like.mem_coe],
  assume y hym hyn,
  have A : (c ^ n - c ^ m) • x ∈ s,
  { convert s.sub_mem hym hyn,
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub] },
  have H : c ^ n - c ^ m ≠ 0,
    by simpa only [sub_eq_zero, ne.def] using (strict_anti_pow cpos cone).injective.ne hmn.symm,
  have : x ∈ s,
  { convert s.smul_mem (c ^ n - c ^ m)⁻¹ A,
    rw [smul_smul, inv_mul_cancel H, one_smul] },
  exact hx this
end

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/

lemma map_linear_map_add_haar_pi_eq_smul_add_haar
  {ι : Type*} [fintype ι] {f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hf : f.det ≠ 0)
  (μ : measure (ι → ℝ)) [is_add_haar_measure μ] :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  /- We have already proved the result for the Lebesgue product measure, using matrices.
  We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := add_haar_measure_unique (is_add_left_invariant_add_haar μ) (pi_Icc01 ι),
  rw this,
  simp [add_haar_measure_eq_volume_pi, real.map_linear_map_volume_pi_eq_smul_volume_pi hf,
    smul_smul, mul_comm],
end

lemma map_linear_map_add_haar_eq_smul_add_haar
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linear_map_add_haar_pi_eq_smul_add_haar`.
  let ι := fin (finrank ℝ E),
  haveI : finite_dimensional ℝ (ι → ℝ) := by apply_instance,
  have : finrank ℝ E = finrank ℝ (ι → ℝ), by simp,
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this,
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] (ι → ℝ)).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) :=
    ⟨_, rfl⟩,
  have gdet : g.det = f.det, by { rw [hg], exact linear_map.det_conj f e },
  rw ← gdet at hf ⊢,
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] (ι → ℝ))),
  { ext x,
    simp only [linear_equiv.coe_coe, function.comp_app, linear_map.coe_comp,
      linear_equiv.symm_apply_apply, hg] },
  simp only [fg, linear_equiv.coe_coe, linear_map.coe_comp],
  have Ce : continuous e := (e : E →ₗ[ℝ] (ι → ℝ)).continuous_of_finite_dimensional,
  have Cg : continuous g := linear_map.continuous_of_finite_dimensional g,
  have Cesymm : continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finite_dimensional,
  rw [← map_map Cesymm.measurable (Cg.comp Ce).measurable, ← map_map Cg.measurable Ce.measurable],
  haveI : is_add_haar_measure (map e μ) := is_add_haar_measure_map μ e.to_add_equiv Ce Cesymm,
  have ecomp : (e.symm) ∘ e = id,
    by { ext x, simp only [id.def, function.comp_app, linear_equiv.symm_apply_apply] },
  rw [map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), linear_map.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, measure.map_id]
end

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp] lemma add_haar_preimage_linear_map
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : set E) :
  μ (f ⁻¹' s) = ennreal.of_real (abs (f.det)⁻¹) * μ s :=
calc μ (f ⁻¹' s) = measure.map f μ s :
  ((f.equiv_of_det_ne_zero hf).to_continuous_linear_equiv.to_homeomorph
    .to_measurable_equiv.map_apply s).symm
... = ennreal.of_real (abs (f.det)⁻¹) * μ s :
  by { rw map_linear_map_add_haar_eq_smul_add_haar μ hf, refl }

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp] lemma add_haar_preimage_continuous_linear_map
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {f : E →L[ℝ] E} (hf : linear_map.det (f : E →ₗ[ℝ] E) ≠ 0) (s : set E) :
  μ (f ⁻¹' s) = ennreal.of_real (abs (linear_map.det (f : E →ₗ[ℝ] E))⁻¹) * μ s :=
add_haar_preimage_linear_map μ hf s

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp] lemma add_haar_preimage_linear_equiv
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  (f : E ≃ₗ[ℝ] E) (s : set E) :
  μ (f ⁻¹' s) = ennreal.of_real (abs (f.symm : E →ₗ[ℝ] E).det) * μ s :=
begin
  have A : (f : E →ₗ[ℝ] E).det ≠ 0 := (linear_equiv.is_unit_det' f).ne_zero,
  convert add_haar_preimage_linear_map μ A s,
  simp only [linear_equiv.det_coe_symm]
end

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp] lemma add_haar_preimage_continuous_linear_equiv
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  (f : E ≃L[ℝ] E) (s : set E) :
  μ (f ⁻¹' s) = ennreal.of_real (abs (f.symm : E →ₗ[ℝ] E).det) * μ s :=
add_haar_preimage_linear_equiv μ _ s

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp] lemma add_haar_image_linear_map
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  (f : E →ₗ[ℝ] E) (s : set E) :
  μ (f '' s) = ennreal.of_real (abs f.det) * μ s :=
begin
  rcases ne_or_eq f.det 0 with hf|hf,
  { let g := (f.equiv_of_det_ne_zero hf).to_continuous_linear_equiv,
    change μ (g '' s) = _,
    rw [continuous_linear_equiv.image_eq_preimage g s, add_haar_preimage_continuous_linear_equiv],
    congr,
    ext x,
    simp only [linear_equiv.of_is_unit_det_apply, linear_equiv.to_continuous_linear_equiv_apply,
      continuous_linear_equiv.symm_symm, continuous_linear_equiv.coe_coe,
      continuous_linear_map.coe_coe, linear_equiv.to_fun_eq_coe, coe_coe] },
  { simp only [hf, zero_mul, ennreal.of_real_zero, abs_zero],
    have : μ f.range = 0 :=
      add_haar_submodule μ _ (linear_map.range_lt_top_of_det_eq_zero hf).ne,
    exact le_antisymm (le_trans (measure_mono (image_subset_range _ _)) this.le) (zero_le _) }
end

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp] lemma add_haar_image_continuous_linear_map
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  (f : E →L[ℝ] E) (s : set E) :
  μ (f '' s) = ennreal.of_real (abs (f : E →ₗ[ℝ] E).det) * μ s :=
add_haar_image_linear_map μ _ s

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp] lemma add_haar_image_continuous_linear_equiv
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  (f : E ≃L[ℝ] E) (s : set E) :
  μ (f '' s) = ennreal.of_real (abs (f : E →ₗ[ℝ] E).det) * μ s :=
add_haar_image_linear_map μ _ s

/-!
### Basic properties of Haar measures on real vector spaces
-/

variables {E : Type*} [normed_group E] [measurable_space E] [normed_space ℝ E]
  [finite_dimensional ℝ E] [borel_space E] (μ : measure E) [is_add_haar_measure μ]

lemma map_add_haar_smul {r : ℝ} (hr : r ≠ 0) :
  measure.map ((•) r) μ = ennreal.of_real (abs (r ^ (finrank ℝ E))⁻¹) • μ :=
begin
  let f : E →ₗ[ℝ] E := r • 1,
  change measure.map f μ = _,
  have hf : f.det ≠ 0,
  { simp only [mul_one, linear_map.det_smul, ne.def, monoid_hom.map_one],
    assume h,
    exact hr (pow_eq_zero h) },
  simp only [map_linear_map_add_haar_eq_smul_add_haar μ hf, mul_one, linear_map.det_smul,
    monoid_hom.map_one],
end

@[simp] lemma add_haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : set E) :
  μ (((•) r) ⁻¹' s) = ennreal.of_real (abs (r ^ (finrank ℝ E))⁻¹) * μ s :=
calc μ (((•) r) ⁻¹' s) = measure.map ((•) r) μ s :
  ((homeomorph.smul (is_unit_iff_ne_zero.2 hr).unit).to_measurable_equiv.map_apply s).symm
... = ennreal.of_real (abs (r^(finrank ℝ E))⁻¹) * μ s : by { rw map_add_haar_smul μ hr, refl }

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp] lemma add_haar_smul (r : ℝ) (s : set E) :
  μ (r • s) = ennreal.of_real (abs (r ^ (finrank ℝ E))) * μ s :=
begin
  rcases ne_or_eq r 0 with h|rfl,
  { rw [← preimage_smul_inv₀ h, add_haar_preimage_smul μ (inv_ne_zero h), inv_pow₀, inv_inv₀] },
  rcases eq_empty_or_nonempty s with rfl|hs,
  { simp only [measure_empty, mul_zero, smul_set_empty] },
  rw [zero_smul_set hs, ← singleton_zero],
  by_cases h : finrank ℝ E = 0,
  { haveI : subsingleton E := finrank_zero_iff.1 h,
    simp only [h, one_mul, ennreal.of_real_one, abs_one, subsingleton.eq_univ_of_nonempty hs,
      pow_zero, subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))] },
  { haveI : nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h),
    simp only [h, zero_mul, ennreal.of_real_zero, abs_zero, ne.def, not_false_iff, zero_pow',
      measure_singleton] }
end

/-! We don't need to state `map_add_haar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/

/-! ### Measure of balls -/

lemma add_haar_ball_center
  {E : Type*} [normed_group E] [measurable_space E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ] (x : E) (r : ℝ) :
  μ (ball x r) = μ (ball (0 : E) r) :=
begin
  have : ball (0 : E) r = ((+) x) ⁻¹' (ball x r), by simp [preimage_add_ball],
  rw [this, add_haar_preimage_add]
end

lemma add_haar_closed_ball_center
  {E : Type*} [normed_group E] [measurable_space E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ] (x : E) (r : ℝ) :
  μ (closed_ball x r) = μ (closed_ball (0 : E) r) :=
begin
  have : closed_ball (0 : E) r = ((+) x) ⁻¹' (closed_ball x r), by simp [preimage_add_closed_ball],
  rw [this, add_haar_preimage_add]
end

lemma add_haar_ball_pos {E : Type*} [normed_group E] [measurable_space E]
  (μ : measure E) [is_add_haar_measure μ] (x : E) {r : ℝ} (hr : 0 < r) :
  0 < μ (ball x r) :=
is_open_ball.add_haar_pos μ (nonempty_ball.2 hr)

lemma add_haar_closed_ball_pos {E : Type*} [normed_group E] [measurable_space E]
  (μ : measure E) [is_add_haar_measure μ] (x : E) {r : ℝ} (hr : 0 < r) :
  0 < μ (closed_ball x r) :=
lt_of_lt_of_le (add_haar_ball_pos μ x hr) (measure_mono ball_subset_closed_ball)

lemma add_haar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
  μ (ball x r) = ennreal.of_real (r ^ (finrank ℝ E)) * μ (ball 0 1) :=
begin
  have : ball (0 : E) r = r • ball 0 1,
    by simp [smul_ball hr.ne' (0 : E) 1, real.norm_eq_abs, abs_of_nonneg hr.le],
  simp [this, add_haar_smul, abs_of_nonneg hr.le, add_haar_ball_center],
end

lemma add_haar_ball [nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
  μ (ball x r) = ennreal.of_real (r ^ (finrank ℝ E)) * μ (ball 0 1) :=
begin
  rcases has_le.le.eq_or_lt hr with h|h,
  { simp [← h, zero_pow finrank_pos] },
  { exact add_haar_ball_of_pos μ x h }
end

/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `add_haar_closed_ball`, which uses the measure of the open unit ball as a standard
form. -/
lemma add_haar_closed_ball' (x : E) {r : ℝ} (hr : 0 ≤ r) :
  μ (closed_ball x r) = ennreal.of_real (r ^ (finrank ℝ E)) * μ (closed_ball 0 1) :=
begin
  have : closed_ball (0 : E) r = r • closed_ball 0 1,
    by simp [smul_closed_ball r (0 : E) zero_le_one, real.norm_eq_abs, abs_of_nonneg hr],
  simp [this, add_haar_smul, abs_of_nonneg hr, add_haar_closed_ball_center],
end

lemma add_haar_closed_unit_ball_eq_add_haar_unit_ball :
  μ (closed_ball (0 : E) 1) = μ (ball 0 1) :=
begin
  apply le_antisymm _ (measure_mono ball_subset_closed_ball),
  have A : tendsto (λ (r : ℝ), ennreal.of_real (r ^ (finrank ℝ E)) * μ (closed_ball (0 : E) 1))
    (𝓝[<] 1) (𝓝 (ennreal.of_real (1 ^ (finrank ℝ E)) * μ (closed_ball (0 : E) 1))),
  { refine ennreal.tendsto.mul _ (by simp) tendsto_const_nhds (by simp),
    exact ennreal.tendsto_of_real ((tendsto_id' nhds_within_le_nhds).pow _) },
  simp only [one_pow, one_mul, ennreal.of_real_one] at A,
  refine le_of_tendsto A _,
  refine mem_nhds_within_Iio_iff_exists_Ioo_subset.2 ⟨(0 : ℝ), by simp, λ r hr, _⟩,
  dsimp,
  rw ← add_haar_closed_ball' μ (0 : E) hr.1.le,
  exact measure_mono (closed_ball_subset_ball hr.2)
end

lemma add_haar_closed_ball (x : E) {r : ℝ} (hr : 0 ≤ r) :
  μ (closed_ball x r) = ennreal.of_real (r ^ (finrank ℝ E)) * μ (ball 0 1) :=
by rw [add_haar_closed_ball' μ x hr, add_haar_closed_unit_ball_eq_add_haar_unit_ball]

lemma add_haar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) :
  μ (sphere x r) = 0 :=
begin
  rcases lt_trichotomy r 0 with h|rfl|h,
  { simp only [empty_diff, measure_empty, ← closed_ball_diff_ball, closed_ball_eq_empty.2 h] },
  { exact (hr rfl).elim },
  { rw [← closed_ball_diff_ball,
        measure_diff ball_subset_closed_ball measurable_set_closed_ball measurable_set_ball
          measure_ball_lt_top.ne,
        add_haar_ball_of_pos μ _ h, add_haar_closed_ball μ _ h.le, tsub_self];
    apply_instance }
end

lemma add_haar_sphere [nontrivial E] (x : E) (r : ℝ) :
  μ (sphere x r) = 0 :=
begin
  rcases eq_or_ne r 0 with rfl|h,
  { simp only [← closed_ball_diff_ball, diff_empty, closed_ball_zero,
               ball_zero, measure_singleton] },
  { exact add_haar_sphere_of_ne_zero μ x h }
end

end measure

end measure_theory
