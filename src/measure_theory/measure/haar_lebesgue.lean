/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure.lebesgue
import measure_theory.measure.haar
import linear_algebra.finite_dimensional

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`.
-/

open topological_space set
open_locale ennreal

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.Icc01 : positive_compacts ℝ :=
⟨Icc 0 1, is_compact_Icc, by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

universe u

/-- The set `[0,1]^n` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.pi_Icc01 (ι : Type*) [fintype ι] :
  positive_compacts (ι → ℝ) :=
⟨set.pi set.univ (λ i, Icc 0 1), is_compact_univ_pi (λ i, is_compact_Icc),
begin
  rw interior_pi_set,
  simp only [interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo, implies_true_iff, zero_lt_one],
end⟩

namespace measure_theory

open measure topological_space.positive_compacts finite_dimensional

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
  { simp only [pi_Icc01, volume_pi_pi (λ i, Icc (0 : ℝ) 1) (λ (i : ι), measurable_set_Icc),
      finset.prod_const_one, ennreal.of_real_one, real.volume_Icc, one_smul, sub_zero] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume_pi ι }
end

instance is_add_haar_measure_volume_pi (ι : Type*) [fintype ι] :
  is_add_haar_measure (volume : measure (ι → ℝ)) :=
by { rw ← add_haar_measure_eq_volume_pi, apply_instance }

lemma map_linear_map_add_haar_pi_eq_smul_haar
  {ι : Type*} [fintype ι] {f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hf : f.det ≠ 0)
  (μ : measure (ι → ℝ)) [is_add_haar_measure μ] :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  /- We have already proved the result for the Lebesgue product measure, using matrices.
  We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := add_haar_measure_unique (is_add_left_invariant_add_haar μ) (pi_Icc01 ι),
  conv_lhs { rw this }, conv_rhs { rw this },
  simp [add_haar_measure_eq_volume_pi, real.map_linear_map_volume_pi_eq_smul_volume hf, smul_smul,
    mul_comm],
end

@[simp] lemma add_haar_ball
  {E : Type*} [normed_group E] [measurable_space E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ] (x : E) (r : ℝ) :
  μ (metric.ball x r) = μ (metric.ball (0 : E) r) :=
begin
  have : metric.ball (0 : E) r = ((+) x) ⁻¹' (metric.ball x r), by { ext y, simp [dist_eq_norm] },
  rw [this, add_haar_preimage_add]
end

lemma finite_dimensional_of_haar_measure
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [measurable_space E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ] :
  finite_dimensional 𝕜 E :=
begin
  by_contradiction h,
  obtain ⟨c, hc⟩ : ∃c:𝕜, 1<∥c∥ := normed_field.exists_one_lt_norm 𝕜,
  have cpos : 0 < ∥c∥ := zero_lt_one.trans hc,
  set R := ∥c∥^2 with hR,
  have hR : ∥c∥ < R, by { rw [← one_mul (∥c∥), hR, pow_two], exact (mul_lt_mul_right cpos).2 hc },
  obtain ⟨f, hf⟩ : ∃ f : ℕ → E, (∀ n, ∥f n∥ ≤ R) ∧ (∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥) :=
    exists_seq_norm_le_one_le_norm_sub hc hR h,
  have : ∀ (a : 𝕜), (0 < ∥a∥) → μ (metric.ball (0 : E) ∥a∥) = ∞, sorry,
  /-{ assume a ha,
    apply le_antisymm le_top,
    let g := λ n, (a / c^3) • f n,
    let r : ℝ := min (∥a∥/(2 * ∥c∥^3)) (∥a∥ * (1 - 1/∥c∥)),
    have hr : ∥a∥ / ∥c∥ + r ≤ ∥a∥ := calc
      ∥a∥ / ∥c∥ + r ≤ ∥a∥ / ∥c∥ + ∥a∥ * (1 - 1/∥c∥) : add_le_add le_rfl (min_le_right _ _)
      ... = ∥a∥ : by { field_simp [cpos.ne'], ring },
    have h'r : r + r ≤ (∥a∥/∥c∥^3) * 1 := calc
      r + r ≤ ∥a∥/(2 * ∥c∥^3) + ∥a∥/(2 * ∥c∥^3) : add_le_add (min_le_left _ _) (min_le_left _ _)
      ... = (∥a∥/∥c∥^3) * 1 : by { field_simp [cpos.ne'], ring },
    have rpos : 0 < r,
    { simp only [one_div, lt_min_iff],
      refine ⟨div_pos ha (mul_pos zero_lt_two (pow_pos cpos 3)), _⟩,
      apply mul_pos ha (sub_pos.2 _),
      rw inv_lt cpos zero_lt_one,
      simpa using hc },
    have μpos : 0 < μ (metric.ball 0 r) :=
      metric.is_open_ball.add_haar_pos μ (metric.nonempty_ball.2 rpos),
    have subset : ∀ n, metric.ball (g n) r ⊆ metric.ball (0 : E) (∥a∥),
    { assume n y hy,
      rw mem_ball_0_iff,
      calc ∥y∥ < ∥g n∥ + r : norm_lt_of_mem_ball hy
      ... ≤ ∥a∥ / ∥c∥ ^ 3 * ∥f n∥ + r : add_le_add (by simp [g, norm_smul]) le_rfl
      ... ≤ ∥a∥/∥c∥^3 * ∥c∥^2 + r :
      begin
        refine add_le_add _ le_rfl,
        refine mul_le_mul_of_nonneg_left (hf.1 n) _,
        exact div_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _),
      end
      ... = ∥a∥/∥c∥ + r : by { field_simp [cpos.ne'], ring }
      ... ≤ ∥a∥ : hr },
    have disj : pairwise (disjoint on (λ (n : ℕ), metric.ball (g n) r)),
    { assume m n hmn,
      apply metric.ball_disjoint_ball,
      simp only [dist_eq_norm, ←smul_sub, norm_smul, normed_field.norm_pow, normed_field.norm_div],
      apply h'r.trans (mul_le_mul_of_nonneg_left (hf.2 m n hmn) _),
      exact (div_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) },
    have : ∑' n, μ (metric.ball (g n) r) ≤ μ (metric.ball (0 : E) (∥a∥)) := calc
      ∑' n, μ (metric.ball (g n) r) = μ (⋃ n, metric.ball (g n) r) :
        (measure_Union disj (λ n, measurable_set_ball)).symm
      ... ≤ μ (metric.ball (0 : E) (∥a∥)) : measure_mono (Union_subset subset),
    simp only [add_haar_ball] at this,
    rwa ennreal.tsum_const_eq_top_of_ne_zero μpos.ne' at this,
    apply_instance } -/
  have : {(0 : E)} = ⋂ (n : ℕ), metric.ball (0 : E) (∥c^n∥) := sorry,
  have Z := measure_Inter
end

#exit

pairwise (disjoint on ?m_3) → (∀ (i : ?m_1), measurable_set (?m_3 i)) → ⇑?m_5 (⋃ (i : ?m_1), ?m_3 i) = ∑' (i : ?m_1), ⇑?m_5 (?m_3 i)

lemma map_linear_map_haar_eq_smul_haar
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  (μ : measure E) [is_add_haar_measure μ]
  {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  haveI : finite_dimensional ℝ E := finite_dimensional_of_haar_measure μ,
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linear_map_haar_pi_eq_smul_haar`.
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
  rw [map_linear_map_haar_pi_eq_smul_haar hf (map e μ), linear_map.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, map_id]
end


end measure_theory
