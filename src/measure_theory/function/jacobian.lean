/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.covering.besicovitch_vector_space
import measure_theory.measure.haar_lebesgue
import analysis.normed_space.pointwise

/-!
# Change of variables in higher-dimensional integrals
-/

open measure_theory measure_theory.measure metric filter set finite_dimensional
open_locale nnreal ennreal topological_space pointwise

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E] (μ : measure E) [is_add_haar_measure μ]

/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at most `m` for any `m > det A`. -/
lemma measure_image_le_mul_of_det_lt
  (A : E →L[ℝ] E) {m : ℝ≥0} (hm : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m) :
  ∀ᶠ δ in 𝓝 (0 : ℝ≥0), ∀ (s : set E) (f : E → E) (hf : approximates_linear_on f A s δ),
  μ (f '' s) ≤ m * μ s :=
begin
  let d := ennreal.of_real (abs (A : E →ₗ[ℝ] E).det),
  -- construct a small neighborhood of `A '' (closed_ball 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ : ∃ (ε : ℝ),
    μ (closed_ball 0 ε + A '' (closed_ball 0 1)) < m * μ (closed_ball 0 1) ∧ 0 < ε,
  { have HC : is_compact (A '' closed_ball 0 1) :=
      (proper_space.is_compact_closed_ball _ _).image A.continuous,
    have L0 : tendsto (λ ε, μ (cthickening ε (A '' (closed_ball 0 1))))
      (𝓝[>] 0) (𝓝 (μ (A '' (closed_ball 0 1)))),
    { apply tendsto.mono_left _ nhds_within_le_nhds,
      exact tendsto_measure_cthickening_of_is_compact HC },
    have L1 : tendsto (λ ε, μ (closed_ball 0 ε + A '' (closed_ball 0 1)))
      (𝓝[>] 0) (𝓝 (μ (A '' (closed_ball 0 1)))),
    { apply L0.congr' _,
      filter_upwards [self_mem_nhds_within],
      assume r hr,
      rw [HC.cthickening_eq_add_closed_ball (le_of_lt hr), add_comm] },
    have L2 : tendsto (λ ε, μ (closed_ball 0 ε + A '' (closed_ball 0 1)))
      (𝓝[>] 0) (𝓝 (d * μ (closed_ball 0 1))),
    { convert L1,
      exact (add_haar_image_continuous_linear_map _ _ _).symm },
    have I : d * μ (closed_ball 0 1) < m * μ (closed_ball 0 1) :=
      (ennreal.mul_lt_mul_right ((add_haar_closed_ball_pos μ _ zero_lt_one).ne')
        measure_closed_ball_lt_top.ne).2 hm,
    have H : ∀ᶠ (b : ℝ) in 𝓝[>] 0,
      μ (closed_ball 0 b + A '' closed_ball 0 1) < m * μ (closed_ball 0 1) :=
        (tendsto_order.1 L2).2 _ I,
    exact (H.and self_mem_nhds_within).exists },
  have : Iio (⟨ε, εpos.le⟩ : ℝ≥0) ∈ 𝓝 (0 : ℝ≥0), { apply Iio_mem_nhds, exact εpos },
  filter_upwards [this],
  -- fix a function `f` which is close enough to `A`.
  assume δ hδ s f hf,
  -- This function expands the volume of any ball by at most `m`
  have I : ∀ x r, x ∈ s → 0 ≤ r → μ (f '' (s ∩ closed_ball x r)) ≤ m * μ (closed_ball x r),
  { assume x r xs r0,
    have K : f '' (s ∩ closed_ball x r) ⊆ A '' (closed_ball 0 r) + closed_ball (f x) (ε * r),
    { rintros y ⟨z, ⟨zs, zr⟩, rfl⟩,
      apply set.mem_add.2 ⟨A (z - x), f z - f x - A (z - x) + f x, _, _, _⟩,
      { apply mem_image_of_mem,
        simpa only [dist_eq_norm, mem_closed_ball, mem_closed_ball_zero_iff] using zr },
      { rw [mem_closed_ball_iff_norm, add_sub_cancel],
        calc ∥f z - f x - A (z - x)∥
            ≤ δ * ∥z - x∥ : hf _ zs _ xs
        ... ≤ ε * r :
          mul_le_mul (le_of_lt hδ) (mem_closed_ball_iff_norm.1 zr) (norm_nonneg _) εpos.le },
      { simp only [map_sub, pi.sub_apply],
        abel } },
    have : A '' (closed_ball 0 r) + closed_ball (f x) (ε * r)
      = {f x} + r • (A '' (closed_ball 0 1) + closed_ball 0 ε),
      by rw [smul_add_set, ← add_assoc, add_comm ({f x}), add_assoc, smul_closed_ball _ _ εpos.le,
        smul_zero, singleton_add_closed_ball_zero, ← A.image_smul_set,
        smul_closed_ball _ _ zero_le_one, smul_zero, real.norm_eq_abs, abs_of_nonneg r0, mul_one,
        mul_comm],
    rw this at K,
    calc μ (f '' (s ∩ closed_ball x r))
        ≤ μ ({f x} + r • (A '' (closed_ball 0 1) + closed_ball 0 ε)) : measure_mono K
    ... = ennreal.of_real (r ^ finrank ℝ E) * μ (A '' closed_ball 0 1 + closed_ball 0 ε) :
      by simp only [abs_of_nonneg r0, add_haar_smul, image_add_left, add_haar_preimage_add,
                    abs_pow, singleton_add]
    ... ≤ ennreal.of_real (r ^ finrank ℝ E) * (m * μ (closed_ball 0 1)) :
      by { rw add_comm, exact ennreal.mul_le_mul le_rfl hε.le }
    ... = m * μ (closed_ball x r) :
      by { simp only [add_haar_closed_ball' _ _ r0], ring } },
  -- covering `s` by closed balls with total measure very close to `μ s`, one deduces that the
  -- measure of `f '' s` is at most `m * (μ s + a)` for any positive `a`.
  have J : ∀ᶠ a in 𝓝[>] (0 : ℝ≥0∞), μ (f '' s) ≤ m * (μ s + a),
  { filter_upwards [self_mem_nhds_within],
    assume a ha,
    change 0 < a at ha,
    obtain ⟨t, r, t_count, ts, rpos, st, μt⟩ : ∃ (t : set E) (r : E → ℝ), t.countable ∧ t ⊆ s
      ∧ (∀ (x : E), x ∈ t → 0 < r x) ∧ (s ⊆ ⋃ (x ∈ t), closed_ball x (r x))
      ∧ ∑' (x : ↥t), μ (closed_ball ↑x (r ↑x)) ≤ μ s + a :=
        besicovitch.exists_closed_ball_covering_tsum_measure_le μ ha.ne' (λ x, Ioi 0) s
        (λ x xs δ δpos, ⟨δ/2, by simp [half_pos δpos, half_lt_self δpos]⟩),
    haveI : encodable t := t_count.to_encodable,
    calc μ (f '' s)
        ≤ μ (⋃ (x : t), f '' (s ∩ closed_ball x (r x))) :
      begin
        rw bUnion_eq_Union at st,
        apply measure_mono,
        rw [← image_Union, ← inter_Union],
        exact image_subset _ (subset_inter (subset.refl _) st)
      end
    ... ≤ ∑' (x : t), μ (f '' (s ∩ closed_ball x (r x))) : measure_Union_le _
    ... ≤ ∑' (x : t), m * μ (closed_ball x (r x)) :
      ennreal.tsum_le_tsum (λ x, I x (r x) (ts x.2) (rpos x x.2).le)
    ... ≤ m * (μ s + a) :
      by { rw ennreal.tsum_mul_left, exact ennreal.mul_le_mul le_rfl μt } },
  -- taking the limit in `a`, one obtains the conclusion
  have L : tendsto (λ a, (m : ℝ≥0∞) * (μ s + a)) (𝓝[>] 0) (𝓝 (m * (μ s + 0))),
  { apply tendsto.mono_left _ nhds_within_le_nhds,
    apply ennreal.tendsto.const_mul (tendsto_const_nhds.add tendsto_id),
    simp only [ennreal.coe_ne_top, ne.def, or_true, not_false_iff] },
  rw add_zero at L,
  exact ge_of_tendsto L J,
end

/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at least `m` for any `m < det A`. -/
lemma mul_le_measure_image_of_lt_det
  (A : E →L[ℝ] E) {m : ℝ≥0} (hm : (m : ℝ≥0∞) < ennreal.of_real (abs (A : E →ₗ[ℝ] E).det)) :
  ∀ᶠ δ in 𝓝 (0 : ℝ≥0), ∀ (s : set E) (f : E → E) (hf : approximates_linear_on f A s δ),
  (m : ℝ≥0∞) * μ s ≤ μ (f '' s) :=
begin
  -- The assumption `hm` implies that `A` is invertible. If `f` is close enough to `A`, it is also
  -- invertible. One can then pass to the inverses, and deduce the estimate from
  -- `measure_image_le_mul_of_det_lt` applied to `f⁻¹` and `A⁻¹`.
  -- exclude first the trivial case where `m = 0`.
  rcases eq_or_lt_of_le (zero_le m) with rfl|mpos,
  { apply eventually_of_forall,
    simp only [forall_const, zero_mul, implies_true_iff, zero_le, ennreal.coe_zero] },
  have hA : (A : E →ₗ[ℝ] E).det ≠ 0,
  { assume h, simpa only [h, ennreal.not_lt_zero, ennreal.of_real_zero, abs_zero] using hm },
  -- let `B` be the continuous linear equiv version of `A`.
  let B := ((A : E →ₗ[ℝ] E).equiv_of_det_ne_zero hA).to_continuous_linear_equiv,
  have : (B : E →L[ℝ] E) = A,
  { ext x,
    simp only [linear_equiv.of_is_unit_det_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_map.coe_coe, linear_equiv.coe_to_continuous_linear_equiv'] },
  -- the determinant of `B.symm` is bounded by `m⁻¹`
  have I : ennreal.of_real (abs (B.symm : E →ₗ[ℝ] E).det) < (m⁻¹ : ℝ≥0),
  { simp only [linear_equiv.coe_to_continuous_linear_equiv_symm, linear_equiv.det_coe_symm, abs_inv,
               linear_equiv.coe_of_is_unit_det, ennreal.of_real, ennreal.coe_lt_coe,
               real.to_nnreal_inv] at ⊢ hm,
    exact nnreal.inv_lt_inv mpos.ne' hm },
  -- therefore, we may apply `measure_image_le_mul_of_det_lt` to `B.symm` and `m⁻¹`.
  obtain ⟨δ₀, δ₀pos, hδ₀⟩ : ∃ (δ : ℝ≥0), 0 < δ ∧ ∀ (t : set E) (g : E → E),
    approximates_linear_on g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t,
  { have : ∀ᶠ (δ : ℝ≥0) in 𝓝 0, ∀ (t : set E) (g : E → E),
      approximates_linear_on g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t :=
        measure_image_le_mul_of_det_lt μ B.symm I,
    rcases exists_Ico_subset_of_mem_nhds this ⟨1, zero_lt_one⟩ with ⟨δ₁, δ₁pos, h₁⟩,
    exact ⟨δ₁/2, nnreal.half_pos δ₁pos, h₁ ⟨bot_le, nnreal.half_lt_self δ₁pos.ne'⟩⟩ },
  -- record smallness conditions for `δ` that will be needed to apply `hδ₀` below.
  have L1 : ∀ᶠ δ in 𝓝 (0 : ℝ≥0), subsingleton E ∨ δ < ∥(B.symm : E →L[ℝ] E)∥₊⁻¹,
  { by_cases (subsingleton E),
    { simp only [h, true_or, eventually_const] },
    simp only [h, false_or],
    apply Iio_mem_nhds,
    simpa only [h, false_or, nnreal.inv_pos] using B.subsingleton_or_nnnorm_symm_pos },
  have L2 : ∀ᶠ δ in 𝓝 (0 : ℝ≥0),
    ∥(B.symm : E →L[ℝ] E)∥₊ * (∥(B.symm : E →L[ℝ] E)∥₊⁻¹ - δ)⁻¹ * δ < δ₀,
  { have : tendsto (λ δ, ∥(B.symm : E →L[ℝ] E)∥₊ * (∥(B.symm : E →L[ℝ] E)∥₊⁻¹ - δ)⁻¹ * δ)
      (𝓝 0) (𝓝 (∥(B.symm : E →L[ℝ] E)∥₊ * (∥(B.symm : E →L[ℝ] E)∥₊⁻¹ - 0)⁻¹ * 0)),
    { rcases eq_or_ne (∥(B.symm : E →L[ℝ] E)∥₊) 0 with H|H,
      { simpa only [H, zero_mul] using tendsto_const_nhds },
      refine tendsto.mul (tendsto_const_nhds.mul _) tendsto_id,
      refine (tendsto.sub tendsto_const_nhds tendsto_id).inv₀ _,
      simpa only [tsub_zero, inv_eq_zero, ne.def] using H },
    simp only [mul_zero] at this,
    exact (tendsto_order.1 this).2 δ₀ δ₀pos },
  -- let `δ` be small enough, and `f` approximated by `B` up to `δ`.
  filter_upwards [L1, L2],
  assume δ h1δ h2δ s f hf,
  have hf' : approximates_linear_on f (B : E →L[ℝ] E) s δ, by convert hf,
  let F := hf'.to_local_equiv h1δ,
  -- the condition to be checked can be reformulated in terms of the inverse maps
  suffices H : μ ((F.symm) '' F.target) ≤ (m⁻¹ : ℝ≥0) * μ F.target,
  { change (m : ℝ≥0∞) * μ (F.source) ≤ μ (F.target),
    rwa [← F.symm_image_target_eq_source, mul_comm, ← ennreal.le_div_iff_mul_le, div_eq_mul_inv,
         mul_comm, ← ennreal.coe_inv (mpos.ne')],
    { apply or.inl,
      simpa only [ennreal.coe_eq_zero, ne.def] using mpos.ne'},
    { simp only [ennreal.coe_ne_top, true_or, ne.def, not_false_iff] } },
  -- as `f⁻¹` is well approximated by `B⁻¹`, the conclusion follows from `hδ₀`
  -- and our choice of `δ`.
  exact hδ₀ _ _ ((hf'.to_inv h1δ).mono_num h2δ.le),
end
