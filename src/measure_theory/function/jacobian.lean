/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.covering.besicovitch_vector_space
import measure_theory.measure.haar_lebesgue
import analysis.normed_space.pointwise
import measure_theory.covering.differentiation

/-!
# Change of variables in higher-dimensional integrals
-/

open measure_theory measure_theory.measure metric filter set finite_dimensional asymptotics
open_locale nnreal ennreal topological_space pointwise

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E] (μ : measure E) [is_add_haar_measure μ]

/-- Let `f` be a function which is sufficiently close (in the Lipschitz sense) to a given linear
map `A`. Then it expands the volume of any set by at most `m` for any `m > det A`. -/
lemma measure_image_le_mul_of_det_lt
  (A : E →L[ℝ] E) {m : ℝ≥0} (hm : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m) :
  ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : set E) (f : E → E) (hf : approximates_linear_on f A s δ),
  μ (f '' s) ≤ m * μ s :=
begin
  apply nhds_within_le_nhds,
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
  ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : set E) (f : E → E) (hf : approximates_linear_on f A s δ),
  (m : ℝ≥0∞) * μ s ≤ μ (f '' s) :=
begin
  apply nhds_within_le_nhds,
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
  { have : ∀ᶠ (δ : ℝ≥0) in 𝓝[>] 0, ∀ (t : set E) (g : E → E),
      approximates_linear_on g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t :=
        measure_image_le_mul_of_det_lt μ B.symm I,
    rcases (this.and self_mem_nhds_within).exists with ⟨δ₀, h, h'⟩,
    exact ⟨δ₀, h', h⟩, },
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

/-- Assume that a function `f` has a derivative at every point of a set `s`. Then one may cover `s`
with countably many closed sets `t n` on which `f` is well approximated by linear maps `A n`. -/
lemma exists_closed_cover_approximates_linear_on_of_has_fderiv_within_at
  (f : E → E) (s : set E) (f' : E → E →L[ℝ] E)
  (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x)
  (r : (E →L[ℝ] E) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
  ∃ (t : ℕ → set E) (A : ℕ → (E →L[ℝ] E)), (∀ n, is_closed (t n)) ∧ (s ⊆ ⋃ n, t n)
  ∧ (∀ n, approximates_linear_on f (A n) (s ∩ t n) (r (A n)))
  ∧ (s.nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
begin
  /- Choose countably many linear maps `f' z`. For every such map, if `f` has a derivative at `x`
  close enough to `f' z`, then `f y - f x` is well approximated by `f' z (y - x)` for `y` close
  enough to `x`, say on a ball of radius `r` (or even `u n` for some sequence `u` tending to `0`).
  Let `M n z` be the points where this happends. Then this set is relatively closed inside `s`,
  and moreover in every closed ball of radius `u n / 3` inside it the map is well approximated by
  `f' z`. Using countably many closed balls to split `M n z` into small diameter subsets `K n z p`,
  one obtains the desired sets `t q` after reindexing.
  -/
  -- exclude the trivial case where `s` is empty
  rcases eq_empty_or_nonempty s with rfl|hs,
  { refine ⟨λ n, ∅, λ n, 0, _, _, _, _⟩;
    simp },
  -- we will use countably many linear maps. Select these from all the derivatives since the
  -- space of linear maps is second-countable
  obtain ⟨T, T_count, hT⟩ : ∃ T : set s, countable T ∧
    (⋃ x ∈ T, ball (f' (x : E)) (r (f' x))) = ⋃ (x : s), ball (f' x) (r (f' x)) :=
    topological_space.is_open_Union_countable _ (λ x, is_open_ball),
  -- fix a sequence `u` of positive reals tending to zero.
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ (u : ℕ → ℝ), strict_anti u ∧ (∀ (n : ℕ), 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ),
  -- `M n z` is the set of points `x` such that `f y - f x` is close to `f' z (y - x)` for `y`
  -- in the ball of radius `u n` around `x`.
  let M : ℕ → T → set E := λ n z, {x | x ∈ s ∧
    ∀ y ∈ s ∩ ball x (u n), ∥f y - f x - f' z (y - x)∥ ≤ r (f' z) * ∥y - x∥},
  -- As `f` is differentiable everywhere on `s`, the sets `M n z` cover `s` by design.
  have s_subset : ∀ x ∈ s, ∃ (n : ℕ) (z : T), x ∈ M n z,
  { assume x xs,
    obtain ⟨z, zT, hz⟩ : ∃ z ∈ T, f' x ∈ ball (f' (z : E)) (r (f' z)),
    { have : f' x ∈ ⋃ (z ∈ T), ball (f' (z : E)) (r (f' z)),
      { rw hT,
        refine mem_Union.2 ⟨⟨x, xs⟩, _⟩,
        simpa only [mem_ball, subtype.coe_mk, dist_self] using (rpos (f' x)).bot_lt },
      rwa mem_bUnion_iff at this },
    obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ), 0 < ε ∧ ∥f' x - f' z∥ + ε ≤ r (f' z),
    { refine ⟨r (f' z) - ∥f' x - f' z∥, _, le_of_eq (by abel)⟩,
      simpa only [sub_pos] using mem_ball_iff_norm.mp hz },
    obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ) (H : 0 < δ),
      ball x δ ∩ s ⊆ {y | ∥f y - f x - (f' x) (y - x)∥ ≤ ε * ∥y - x∥} :=
        metric.mem_nhds_within_iff.1 (is_o.def (hf' x xs) εpos),
    obtain ⟨n, hn⟩ : ∃ n, u n < δ := ((tendsto_order.1 u_lim).2 _ δpos).exists,
    refine ⟨n, ⟨z, zT⟩, ⟨xs, _⟩⟩,
    assume y hy,
    calc ∥f y - f x - (f' z) (y - x)∥
        = ∥(f y - f x - (f' x) (y - x)) + (f' x - f' z) (y - x)∥ :
      begin
        congr' 1,
        simp only [continuous_linear_map.coe_sub', map_sub, pi.sub_apply],
        abel,
      end
    ... ≤ ∥f y - f x - (f' x) (y - x)∥ + ∥(f' x - f' z) (y - x)∥ : norm_add_le _ _
    ... ≤ ε * ∥y - x∥ + ∥f' x - f' z∥ * ∥y - x∥ :
      begin
        refine add_le_add (hδ _) (continuous_linear_map.le_op_norm _ _),
        rw inter_comm,
        exact inter_subset_inter_right _ (ball_subset_ball hn.le) hy,
      end
    ... ≤ r (f' z) * ∥y - x∥ :
      begin
        rw [← add_mul, add_comm],
        exact mul_le_mul_of_nonneg_right hε (norm_nonneg _),
      end },
  -- the sets `M n z` are relatively closed in `s`, as all the conditions defining it are clearly
  -- closed
  have closure_M_subset : ∀ n z, s ∩ closure (M n z) ⊆ M n z,
  { rintros n z x ⟨xs, hx⟩,
    refine ⟨xs, λ y hy, _⟩,
    obtain ⟨a, aM, a_lim⟩ : ∃ (a : ℕ → E), (∀ k, a k ∈ M n z) ∧ tendsto a at_top (𝓝 x) :=
      mem_closure_iff_seq_limit.1 hx,
    have L1 : tendsto (λ (k : ℕ), ∥f y - f (a k) - (f' z) (y - a k)∥) at_top
      (𝓝 ∥f y - f x - (f' z) (y - x)∥),
    { apply tendsto.norm,
      have L : tendsto (λ k, f (a k)) at_top (𝓝 (f x)),
      { apply (hf' x xs).continuous_within_at.tendsto.comp,
        apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ a_lim,
        exact eventually_of_forall (λ k, (aM k).1) },
      apply tendsto.sub (tendsto_const_nhds.sub L),
      exact ((f' z).continuous.tendsto _).comp (tendsto_const_nhds.sub a_lim) },
    have L2 : tendsto (λ (k : ℕ), (r (f' z) : ℝ) * ∥y - a k∥) at_top (𝓝 (r (f' z) * ∥y - x∥)) :=
      (tendsto_const_nhds.sub a_lim).norm.const_mul _,
    have I : ∀ᶠ k in at_top, ∥f y - f (a k) - (f' z) (y - a k)∥ ≤ r (f' z) * ∥y - a k∥,
    { have L : tendsto (λ k, dist y (a k)) at_top (𝓝 (dist y x)) := tendsto_const_nhds.dist a_lim,
      filter_upwards [(tendsto_order.1 L).2 _ hy.2],
      assume k hk,
      exact (aM k).2 y ⟨hy.1, hk⟩ },
    apply le_of_tendsto_of_tendsto L1 L2 I },
  -- choose a dense sequence `d p`
  rcases topological_space.exists_dense_seq E with ⟨d, hd⟩,
  -- split `M n z` into subsets `K n z p` of small diameters by intersecting with the ball
  -- `closed_ball (d p) (u n / 3)`.
  let K : ℕ → T → ℕ → set E := λ n z p, closure (M n z) ∩ closed_ball (d p) (u n / 3),
  -- on the sets `K n z p`, the map `f` is well approximated by `f' z` by design.
  have K_approx : ∀ n (z : T) p, approximates_linear_on f (f' z) (s ∩ K n z p) (r (f' z)),
  { assume n z p x hx y hy,
    have yM : y ∈ M n z := closure_M_subset _ _ ⟨hy.1, hy.2.1⟩,
    refine yM.2 _ ⟨hx.1, _⟩,
    calc dist x y ≤ dist x (d p) + dist y (d p) : dist_triangle_right _ _ _
    ... ≤ u n / 3 + u n / 3 : add_le_add hx.2.2 hy.2.2
    ... < u n : by linarith [u_pos n] },
  -- the sets `K n z p` are also closed, again by design.
  have K_closed : ∀ n (z : T) p, is_closed (K n z p) :=
    λ n z p, is_closed_closure.inter is_closed_ball,
  -- reindex the sets `K n z p`, to let them only depend on an integer parameter `q`.
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ × T × ℕ, function.surjective F,
  { haveI : encodable T := T_count.to_encodable,
    haveI : nonempty T,
    { unfreezingI { rcases eq_empty_or_nonempty T with rfl|hT },
      { rcases hs with ⟨x, xs⟩,
        rcases s_subset x xs with ⟨n, z, hnz⟩,
        exact false.elim z.2 },
      { exact (nonempty_coe_sort _).2 hT } },
    inhabit (ℕ × T × ℕ),
    exact ⟨_, encodable.surjective_decode_iget _⟩ },
  -- these sets `t q = K n z p` will do
  refine ⟨λ q, K (F q).1 (F q).2.1 (F q).2.2, λ q, f' (F q).2.1, λ n, K_closed _ _ _, λ x xs, _,
    λ q, K_approx _ _ _, λ h's q, ⟨(F q).2.1, (F q).2.1.1.2, rfl⟩⟩,
  -- the only fact that needs further checking is that they cover `s`.
  -- we already know that any point `x ∈ s` belongs to a set `M n z`.
  obtain ⟨n, z, hnz⟩ : ∃ (n : ℕ) (z : T), x ∈ M n z := s_subset x xs,
  -- by density, it also belongs to a ball `closed_ball (d p) (u n / 3)`.
  obtain ⟨p, hp⟩ : ∃ (p : ℕ), x ∈ closed_ball (d p) (u n / 3),
  { have : set.nonempty (ball x (u n / 3)),
    { simp only [nonempty_ball], linarith [u_pos n] },
    obtain ⟨p, hp⟩ : ∃ (p : ℕ), d p ∈ ball x (u n / 3) := hd.exists_mem_open is_open_ball this,
    exact ⟨p, (mem_ball'.1 hp).le⟩ },
  -- choose `q` for which `t q = K n z p`.
  obtain ⟨q, hq⟩ : ∃ q, F q = (n, z, p) := hF _,
  -- then `x` belongs to `t q`.
  apply mem_Union.2 ⟨q, _⟩,
  simp only [hq, subset_closure hnz, hp, mem_inter_eq, and_self],
end

/-- Assume that a function `f` has a derivative at every point of a set `s`. Then one may
partition `s` into countably many relatively measurable sets `t n` on which `f` is well
approximated by linear maps `A n`. -/
lemma exists_partition_approximates_linear_on_of_has_fderiv_within_at
  (f : E → E) (s : set E) (f' : E → E →L[ℝ] E)
  (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x)
  (r : (E →L[ℝ] E) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
  ∃ (t : ℕ → set E) (A : ℕ → (E →L[ℝ] E)), pairwise (disjoint on t)
  ∧ (∀ n, measurable_set (t n)) ∧ (s ⊆ ⋃ n, t n)
  ∧ (∀ n, approximates_linear_on f (A n) (s ∩ t n) (r (A n)))
  ∧ (s.nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
begin
  rcases exists_closed_cover_approximates_linear_on_of_has_fderiv_within_at f s f' hf' r rpos
    with ⟨t, A, t_closed, st, t_approx, ht⟩,
  refine ⟨disjointed t, A, disjoint_disjointed _,
          measurable_set.disjointed (λ n, (t_closed n).measurable_set), _, _, ht⟩,
  { rw Union_disjointed, exact st },
  { assume n, exact (t_approx n).mono_set (inter_subset_inter_right _ (disjointed_subset _ _)) },
end

/-- A differentiable function maps sets of measure zero to sets of measure zero. -/
lemma add_haar_image_zero_of_differentiable_on_of_add_haar_zero
  (f : E → E) (s : set E) (hf : differentiable_on ℝ f s) (hs : μ s = 0) :
  μ (f '' s) = 0 :=
begin
  refine le_antisymm _ (zero_le _),
  have : ∀ (A : E →L[ℝ] E), ∃ (δ : ℝ≥0), 0 < δ ∧
    ∀ (t : set E) (g : E → E) (hf : approximates_linear_on g A t δ),
     μ (g '' t) ≤ (real.to_nnreal ((abs (A : E →ₗ[ℝ] E).det)) + 1 : ℝ≥0) * μ t,
  { assume A,
    let m : ℝ≥0 := real.to_nnreal ((abs (A : E →ₗ[ℝ] E).det)) + 1,
    have I : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m,
      by simp only [ennreal.of_real, m, lt_add_iff_pos_right, zero_lt_one, ennreal.coe_lt_coe],
    rcases ((measure_image_le_mul_of_det_lt μ A I).and self_mem_nhds_within).exists with ⟨δ, h, h'⟩,
    exact ⟨δ, h', h⟩ },
  choose δ hδ using this,
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ : ∃ (t : ℕ → set E) (A : ℕ → (E →L[ℝ] E)),
    pairwise (disjoint on t) ∧ (∀ (n : ℕ), measurable_set (t n)) ∧ (s ⊆ ⋃ (n : ℕ), t n)
    ∧ (∀ (n : ℕ), approximates_linear_on f (A n) (s ∩ t n) (δ (A n)))
    ∧ (s.nonempty → ∀ n, ∃ y ∈ s, A n = fderiv_within ℝ f s y) :=
        exists_partition_approximates_linear_on_of_has_fderiv_within_at f s
        (fderiv_within ℝ f s) (λ x xs, (hf x xs).has_fderiv_within_at) δ (λ A, (hδ A).1.ne'),
  calc μ (f '' s)
      ≤ μ (⋃ n, f '' (s ∩ (t n))) :
    begin
      apply measure_mono,
      rw [← image_Union, ← inter_Union],
      exact image_subset f (subset_inter subset.rfl t_cover)
    end
  ... ≤ ∑' n, μ (f '' (s ∩ (t n))) : measure_Union_le _
  ... ≤ ∑' n, (real.to_nnreal ((abs (A n : E →ₗ[ℝ] E).det)) + 1 : ℝ≥0) * μ (s ∩ (t n)) :
    begin
      apply ennreal.tsum_le_tsum (λ n, _),
      apply (hδ (A n)).2,
      exact ht n,
    end
  ... ≤ ∑' n, (real.to_nnreal ((abs (A n : E →ₗ[ℝ] E).det)) + 1 : ℝ≥0) * 0 :
    begin
      refine ennreal.tsum_le_tsum (λ n, ennreal.mul_le_mul le_rfl _),
      exact le_trans (measure_mono (inter_subset_left _ _)) (le_of_eq hs),
    end
  ... = 0 : by simp only [tsum_zero, mul_zero]
end

/-- A version of Sard lemma in fixed dimension: given a differentiable function from `E` to `E` and
a set where the differential is not invertible, then the image of this set has zero measure.
Here, we give an auxiliary statement towards this result. -/
lemma add_haar_image_zero_of_fderiv_not_onto_aux
  (f : E → E) (s : set E) (f' : E → (E →L[ℝ] E)) (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x)
  (R : ℝ) (hs : s ⊆ closed_ball 0 R) (ε : ℝ≥0) (εpos : 0 < ε)
  (h'f' : ∀ x ∈ s, (f' x : E →ₗ[ℝ] E).det = 0) :
  μ (f '' s) ≤ ε * μ (closed_ball 0 R) :=
begin
  rcases eq_empty_or_nonempty s with rfl|h's, { simp only [measure_empty, zero_le, image_empty] },
  have : ∀ (A : E →L[ℝ] E), ∃ (δ : ℝ≥0), 0 < δ ∧
    ∀ (t : set E) (g : E → E) (hf : approximates_linear_on g A t δ),
     μ (g '' t) ≤ (real.to_nnreal ((abs (A : E →ₗ[ℝ] E).det)) + ε : ℝ≥0) * μ t,
  { assume A,
    let m : ℝ≥0 := real.to_nnreal ((abs (A : E →ₗ[ℝ] E).det)) + ε,
    have I : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m,
      by simp only [ennreal.of_real, m, lt_add_iff_pos_right, εpos, ennreal.coe_lt_coe],
    rcases ((measure_image_le_mul_of_det_lt μ A I).and self_mem_nhds_within).exists with ⟨δ, h, h'⟩,
    exact ⟨δ, h', h⟩ },
  choose δ hδ using this,
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ : ∃ (t : ℕ → set E) (A : ℕ → (E →L[ℝ] E)),
    pairwise (disjoint on t) ∧ (∀ (n : ℕ), measurable_set (t n)) ∧ (s ⊆ ⋃ (n : ℕ), t n)
    ∧ (∀ (n : ℕ), approximates_linear_on f (A n) (s ∩ t n) (δ (A n)))
    ∧  (s.nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
      exists_partition_approximates_linear_on_of_has_fderiv_within_at f s
      f' hf' δ (λ A, (hδ A).1.ne'),
  calc μ (f '' s)
      ≤ μ (⋃ n, f '' (s ∩ t n)) :
    begin
      apply measure_mono,
      rw [← image_Union, ← inter_Union],
      exact image_subset f (subset_inter subset.rfl t_cover)
    end
  ... ≤ ∑' n, μ (f '' (s ∩ t n)) : measure_Union_le _
  ... ≤ ∑' n, (real.to_nnreal ((abs (A n : E →ₗ[ℝ] E).det)) + ε : ℝ≥0) * μ (s ∩ t n) :
    begin
      apply ennreal.tsum_le_tsum (λ n, _),
      apply (hδ (A n)).2,
      exact ht n,
    end
  ... = ∑' n, ε * μ (s ∩ t n) :
    begin
      congr,
      ext1 n,
      congr,
      rcases Af' h's n with ⟨y, ys, hy⟩,
      simp only [hy, h'f' y ys, real.to_nnreal_zero, abs_zero, zero_add]
    end
  ... ≤ ε * ∑' n, μ (closed_ball 0 R ∩ t n) :
    begin
      rw ennreal.tsum_mul_left,
      refine ennreal.mul_le_mul le_rfl (ennreal.tsum_le_tsum (λ n, measure_mono _)),
      exact inter_subset_inter_left _ hs,
    end
  ... = ε * μ (⋃ n, closed_ball 0 R ∩ t n) :
    begin
      rw measure_Union,
      { exact pairwise_disjoint.mono t_disj (λ n, inter_subset_right _ _) },
      { assume n,
        exact measurable_set_closed_ball.inter (t_meas n) }
    end
  ... ≤ ε * μ (closed_ball 0 R) :
    begin
      rw ← inter_Union,
      exact ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_left _ _)),
    end
end

/-- A version of Sard lemma in fixed dimension: given a differentiable function from `E` to `E` and
a set where the differential is not invertible, then the image of this set has zero measure. -/
lemma add_haar_image_zero_of_fderiv_not_onto
  (f : E → E) (s : set E) (f' : E → (E →L[ℝ] E)) (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x)
  (h'f' : ∀ x ∈ s, (f' x : E →ₗ[ℝ] E).det = 0) :
  μ (f '' s) = 0 :=
begin
  suffices H : ∀ R, μ (f '' (s ∩ closed_ball 0 R)) = 0,
  { apply le_antisymm _ (zero_le _),
    rw ← Union_inter_closed_ball_nat s 0,
    calc μ (f '' ⋃ (n : ℕ), s ∩ closed_ball 0 n) ≤ ∑' (n : ℕ), μ (f '' (s ∩ closed_ball 0 n)) :
      by { rw image_Union, exact measure_Union_le _ }
    ... ≤ 0 : by simp only [H, tsum_zero, nonpos_iff_eq_zero] },
  assume R,
  have A : ∀ (ε : ℝ≥0) (εpos : 0 < ε), μ (f '' (s ∩ closed_ball 0 R)) ≤ ε * μ (closed_ball 0 R) :=
    λ ε εpos, add_haar_image_zero_of_fderiv_not_onto_aux μ _ _ f'
      (λ x hx, (hf' x hx.1).mono (inter_subset_left _ _)) R (inter_subset_right _ _) ε εpos
      (λ x hx, h'f' x hx.1),
  have B : tendsto (λ (ε : ℝ≥0), (ε : ℝ≥0∞) * μ (closed_ball 0 R)) (𝓝[>] 0) (𝓝 0),
  { have : tendsto (λ (ε : ℝ≥0), (ε : ℝ≥0∞) * μ (closed_ball 0 R))
      (𝓝 0) (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * μ (closed_ball 0 R))) :=
        ennreal.tendsto.mul_const (ennreal.tendsto_coe.2 tendsto_id)
          (or.inr ((measure_closed_ball_lt_top).ne)),
    simp only [zero_mul, ennreal.coe_zero] at this,
    exact tendsto.mono_left this nhds_within_le_nhds },
  apply le_antisymm _ (zero_le _),
  apply ge_of_tendsto B,
  filter_upwards [self_mem_nhds_within],
  exact A,
end

/-- If a differentiable function `f` is approximated by a linear map `A` on a set `s`, up to `δ`,
then at almost every `x` in `s` one has `∥f' x - A∥ ≤ δ`. -/
lemma approximates_linear_on.norm_fderiv_sub_le {f : E → E} {A : E →L[ℝ] E} {s : set E} {δ : ℝ≥0}
  (hf : approximates_linear_on f A s δ) (hs : measurable_set s)
  (f' : E → E →L[ℝ] E) (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) :
  ∀ᵐ x ∂ (μ.restrict s), ∥f' x - A∥₊ ≤ δ :=
begin
  /- The conclusion will hold at the Lebesgue density points of `s` (which have full measure).
  at such a point `x`, for any `z` and any `ε > 0` one has for small `r`
  that `{x} + r • closed_ball z ε` intersects `s`. At a point `y` in the intersection,
  `f y - f x` is close both to `f' x (r z)` (by differentiability) and to `A (r z)`
  (by linear approximation), so these two quantities are close, i.e., `(f' x - A) z` is small. -/
  filter_upwards [besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs],
  -- start from a Lebesgue density point `x`, belonging to `s`.
  assume x hx xs,
  -- consider an arbitrary vector `z`.
  apply continuous_linear_map.op_norm_le_bound _ δ.2 (λ z, _),
  -- to show that `∥(f' x - A) z∥ ≤ δ ∥z∥`, it suffices to do it up to some error that vanishes
  -- asymptotically in terms of `ε > 0`.
  suffices H : ∀ ε, 0 < ε → ∥(f' x - A) z∥ ≤ (δ + ε) * (∥z∥ + ε) + ∥(f' x - A)∥ * ε,
  { have : tendsto (λ (ε : ℝ), ((δ : ℝ) + ε) * (∥z∥ + ε) + ∥(f' x - A)∥ * ε) (𝓝[>] 0)
      (𝓝 ((δ + 0) * (∥z∥ + 0) + ∥(f' x - A)∥ * 0)) :=
        tendsto.mono_left (continuous.tendsto (by continuity) 0) nhds_within_le_nhds,
    simp only [add_zero, mul_zero] at this,
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this,
    filter_upwards [self_mem_nhds_within],
    exact H },
  -- fix a positive `ε`.
  assume ε εpos,
  -- for small enough `r`, the rescaled ball `r • closed_ball z ε` intersects `s`, as `x` is a
  -- density point
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closed_ball z ε)).nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx
      _ measurable_set_closed_ball (add_haar_closed_ball_pos μ z εpos).ne',
  obtain ⟨ρ, ρpos, hρ⟩ :
    ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ∥f y - f x - (f' x) (y - x)∥ ≤ ε * ∥y - x∥} :=
      mem_nhds_within_iff.1 (is_o.def (hf' x xs) εpos),
  -- for small enough `r`, the rescaled ball `r • closed_ball z ε` is included in the set where
  -- `f y - f x` is well approximated by `f' x (y - x)`.
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closed_ball z ε ⊆ ball x ρ := nhds_within_le_nhds
    (eventually_singleton_add_smul_subset bounded_closed_ball (ball_mem_nhds x ρpos)),
  -- fix a small positive `r` satisfying the above properties, as well as a corresponding `y`.
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ : ∃ (r : ℝ), (s ∩ ({x} + r • closed_ball z ε)).nonempty ∧
    {x} + r • closed_ball z ε ⊆ ball x ρ ∧ 0 < r := (B₁.and (B₂.and self_mem_nhds_within)).exists,
  -- write `y = x + r a` with `a ∈ closed_ball z ε`.
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closed_ball z ε ∧ y = x + r • a,
  { simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy,
    rcases hy with ⟨a, az, ha⟩,
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩ },
  have norm_a : ∥a∥ ≤ ∥z∥ + ε := calc
    ∥a∥ = ∥z + (a - z)∥ : by simp only [add_sub_cancel'_right]
    ... ≤ ∥z∥ + ∥a - z∥ : norm_add_le _ _
    ... ≤ ∥z∥ + ε : add_le_add_left (mem_closed_ball_iff_norm.1 az) _,
  -- use the approximation properties to control `(f' x - A) a`, and then `(f' x - A) z` as `z` is
  -- close to `a`.
  have I : r * ∥(f' x - A) a∥ ≤ r * (δ + ε) * (∥z∥ + ε) := calc
    r * ∥(f' x - A) a∥ = ∥(f' x - A) (r • a)∥ :
      by simp only [continuous_linear_map.map_smul, norm_smul, real.norm_eq_abs,
                    abs_of_nonneg rpos.le]
    ... = ∥(f y - f x - A (y - x)) -
            (f y - f x - (f' x) (y - x))∥ :
      begin
        congr' 1,
        simp only [ya, add_sub_cancel', sub_sub_sub_cancel_left, continuous_linear_map.coe_sub',
          eq_self_iff_true, sub_left_inj, pi.sub_apply, continuous_linear_map.map_smul, smul_sub],
      end
    ... ≤ ∥f y - f x - A (y - x)∥ +
             ∥f y - f x - (f' x) (y - x)∥ : norm_sub_le _ _
    ... ≤ δ * ∥y - x∥ + ε * ∥y - x∥ :
      add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
    ... = r * (δ + ε) * ∥a∥ :
      by { simp only [ya, add_sub_cancel', norm_smul, real.norm_eq_abs, abs_of_nonneg rpos.le],
           ring }
    ... ≤ r * (δ + ε) * (∥z∥ + ε) :
      mul_le_mul_of_nonneg_left norm_a (mul_nonneg rpos.le (add_nonneg δ.2 εpos.le)),
  show ∥(f' x - A) z∥ ≤ (δ + ε) * (∥z∥ + ε) + ∥(f' x - A)∥ * ε, from calc
    ∥(f' x - A) z∥ = ∥(f' x - A) a + (f' x - A) (z - a)∥ :
      begin
        congr' 1,
        simp only [continuous_linear_map.coe_sub', map_sub, pi.sub_apply],
        abel
      end
    ... ≤ ∥(f' x - A) a∥ + ∥(f' x - A) (z - a)∥ : norm_add_le _ _
    ... ≤ (δ + ε) * (∥z∥ + ε) + ∥f' x - A∥ * ∥z - a∥ :
      begin
        apply add_le_add,
        { rw mul_assoc at I, exact (mul_le_mul_left rpos).1 I },
        { apply continuous_linear_map.le_op_norm }
      end
    ... ≤ (δ + ε) * (∥z∥ + ε) + ∥f' x - A∥ * ε : add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (mem_closed_ball_iff_norm'.1 az) (norm_nonneg _)),
end

/-- The derivative of a function on a measurable set is almost everywhere measurable on this set
with respect to Lebesgue measure. Note that, in general, it is not genuinely measurable there,
as `f'` is not unique (but only on a set of measure `0`, as the argument shows). -/
lemma ae_measurable_fderiv_within
  (f : E → E) (s : set E) (hs : measurable_set s) (f' : E → (E →L[ℝ] E))
  (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) :
  ae_measurable f' (μ.restrict s) :=
begin
  /- It suffices to show that `f'` can be uniformly approximated by a measurable function.
  Fix `ε > 0`. Thanks to `exists_partition_approximates_linear_on_of_has_fderiv_within_at`, one
  can find a countable measurable partition of `s` into sets `s ∩ t n` on which `f` is well
  approximated by linear maps `A n`. On almost all of `s ∩ t n`, it follows from
  `approximates_linear_on.norm_fderiv_sub_le` that `f'` is uniformly approximated by `A n`, which
  gives the conclusion. -/
  -- fix a precision `ε`
  refine ae_measurable_of_unif_approx (λ ε εpos, _),
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩,
  have δpos : 0 < δ := εpos,
  -- partition `s` into sets `s ∩ t n` on which `f` is approximated by linear maps `A n`.
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ : ∃ (t : ℕ → set E) (A : ℕ → (E →L[ℝ] E)),
    pairwise (disjoint on t) ∧ (∀ (n : ℕ), measurable_set (t n)) ∧ (s ⊆ ⋃ (n : ℕ), t n)
    ∧ (∀ (n : ℕ), approximates_linear_on f (A n) (s ∩ t n) δ)
    ∧ (s.nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
      exists_partition_approximates_linear_on_of_has_fderiv_within_at f s
      f' hf' (λ A, δ) (λ A, δpos.ne'),
  -- define a measurable function `g` which coincides with `A n` on `t n`.
  obtain ⟨g, g_meas, hg⟩ : ∃ g : E → (E →L[ℝ] E), measurable g ∧
    ∀ (n : ℕ) (x : E), x ∈ t n → g x = A n :=
      exists_measurable_piecewise_nat t t_meas t_disj (λ n x, A n) (λ n, measurable_const),
  refine ⟨g, g_meas.ae_measurable, _⟩,
  -- reduce to checking that `f'` and `g` are close on almost all of `s ∩ t n`, for all `n`.
  suffices H : ∀ᵐ (x : E) ∂(sum (λ n, μ.restrict (s ∩ t n))), dist (g x) (f' x) ≤ ε,
  { have : μ.restrict s ≤ sum (λ n, μ.restrict (s ∩ t n)),
    { have : s = ⋃ n, s ∩ t n,
      { rw ← inter_Union,
        exact subset.antisymm (subset_inter subset.rfl t_cover) (inter_subset_left _ _) },
      conv_lhs { rw this },
      exact restrict_Union_le },
    exact ae_mono this H },
  -- fix such an `n`.
  refine ae_sum_iff.2 (λ n, _),
  -- on almost all `s ∩ t n`, `f' x` is close to `A n` thanks to
  -- `approximates_linear_on.norm_fderiv_sub_le`.
  have E₁ : ∀ᵐ (x : E) ∂μ.restrict (s ∩ t n), ∥f' x - A n∥₊ ≤ δ :=
    (ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f'
      (λ x hx, (hf' x hx.1).mono (inter_subset_left _ _)),
  -- moreover, `g x` is equal to `A n` there.
  have E₂ : ∀ᵐ (x : E) ∂μ.restrict (s ∩ t n), g x = A n,
  { suffices H : ∀ᵐ (x : E) ∂μ.restrict (t n), g x = A n,
      from ae_mono (restrict_mono (inter_subset_right _ _) le_rfl) H,
    filter_upwards [ae_restrict_mem (t_meas n)],
    exact hg n },
  -- putting these two properties together gives the conclusion.
  filter_upwards [E₁, E₂],
  assume x hx1 hx2,
  rw ← nndist_eq_nnnorm at hx1,
  rw [hx2, dist_comm],
  exact hx1,
end

lemma add_haar_image_le_of_fderiv (f : E → E) (s : set E) (f' : E → (E →L[ℝ] E))
  (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x)
  (R : ℝ) (hs : s ⊆ closed_ball 0 R) (ε : ℝ≥0) (εpos : 0 < ε) :
  μ (f '' s) ≤ ∫⁻ x in s, ennreal.of_real (abs (f' x : E →ₗ[ℝ] E).det) ∂μ
                + ε * μ (closed_ball 0 R) :=
begin
  rcases eq_empty_or_nonempty s with rfl|h's, { simp only [measure_empty, zero_le, image_empty] },
  have : ∀ (A : E →L[ℝ] E), ∃ (δ : ℝ≥0), 0 < δ ∧
    ∀ (t : set E) (g : E → E) (hf : approximates_linear_on g A t δ),
     μ (g '' t) ≤ (real.to_nnreal ((abs (A : E →ₗ[ℝ] E).det)) + ε : ℝ≥0) * μ t,
  { assume A,
    let m : ℝ≥0 := real.to_nnreal ((abs (A : E →ₗ[ℝ] E).det)) + ε,
    have I : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m,
      by simp only [ennreal.of_real, m, lt_add_iff_pos_right, εpos, ennreal.coe_lt_coe],
    rcases ((measure_image_le_mul_of_det_lt μ A I).and self_mem_nhds_within).exists with ⟨δ, h, h'⟩,
    exact ⟨δ, h', h⟩ },
  choose δ hδ using this,
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ : ∃ (t : ℕ → set E) (A : ℕ → (E →L[ℝ] E)),
    pairwise (disjoint on t) ∧ (∀ (n : ℕ), measurable_set (t n)) ∧ (s ⊆ ⋃ (n : ℕ), t n)
    ∧ (∀ (n : ℕ), approximates_linear_on f (A n) (s ∩ t n) (δ (A n)))
    ∧  (s.nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
      exists_partition_approximates_linear_on_of_has_fderiv_within_at f s
      f' hf' δ (λ A, (hδ A).1.ne'),
  calc μ (f '' s)
      ≤ μ (⋃ n, f '' (s ∩ t n)) :
    begin
      apply measure_mono,
      rw [← image_Union, ← inter_Union],
      exact image_subset f (subset_inter subset.rfl t_cover)
    end
  ... ≤ ∑' n, μ (f '' (s ∩ t n)) : measure_Union_le _
  ... ≤ ∑' n, (real.to_nnreal ((abs (A n : E →ₗ[ℝ] E).det)) + ε : ℝ≥0) * μ (s ∩ t n) :
    begin
      apply ennreal.tsum_le_tsum (λ n, _),
      apply (hδ (A n)).2,
      exact ht n,
    end
  ... = ∑' n, ∫⁻ x in s ∩ t n, ↑(real.to_nnreal ((abs (A n : E →ₗ[ℝ] E).det)) + ε : ℝ≥0) ∂μ :
    by simp only [lintegral_const, measurable_set.univ, measure.restrict_apply, univ_inter]
  ... ≤ ∑' n, ∫⁻ x in s ∩ t n, (ennreal.of_real (abs (f' x : E →ₗ[ℝ] E).det) + 2 * ε) ∂μ :
    begin
      apply ennreal.tsum_le_tsum (λ n, _),
      apply lintegral_mono_ae,
      have Z := (ht n).norm_fderiv_sub_le μ f' (λ x hx, (hf' x hx.1).mono (inter_subset_left _ _)),
      have : ∀ᵐ (x : E) ∂μ.restrict (s ∩ t n),
        abs ((f' x : E →ₗ[ℝ] E).det - (A n : E →ₗ[ℝ] E).det) ≤ ε, sorry,
      filter_upwards [this],
      assume x hx,
      rw [ennreal.of_real],
      sorry,


    end
/-  ... ≤ ε * ∑' n, μ (closed_ball 0 R ∩ t n) :
    begin
      rw ennreal.tsum_mul_left,
      refine ennreal.mul_le_mul le_rfl (ennreal.tsum_le_tsum (λ n, measure_mono _)),
      exact inter_subset_inter_left _ hs,
    end
  ... = ε * μ (⋃ n, closed_ball 0 R ∩ t n) :
    begin
      rw measure_Union,
      { rw ← pairwise_univ at ⊢ t_disj,
        refine pairwise_disjoint.mono t_disj (λ n, inter_subset_right _ _) },
      { assume n,
        exact measurable_set_closed_ball.inter (t_meas n) }
    end -/
  ... ≤ ∫⁻ x in s, ennreal.of_real (abs (f' x : E →ₗ[ℝ] E).det) ∂μ
                + ε * μ (closed_ball 0 R) : sorry
end
