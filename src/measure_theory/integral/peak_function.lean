/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.integral.set_integral
import measure_theory.function.locally_integrable

/-!
# Integrals against peak functions

A sequence of peak functions is a sequence of functions with average one concentrating around
a point `x₀`. Given such a sequence `φₙ`, then `∫ φₙ g` tends to `g x₀` in many situations, with
a whole zoo of possible assumptions on `φₙ` and `g`. This file is devoted to such results.

## Main results

* `tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at`: If a sequence of peak
  functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
  `g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `g x₀`.
* `tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_continuous_on`:
  If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
  then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
  concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀`
  if `g` is continuous on `s`.

Note that there are related results about convolution with respect to peak functions in the file
`analysis.convolution`, such as `convolution_tendsto_right` there.
-/

open set filter measure_theory measure_theory.measure topological_space metric
open_locale topology ennreal

/-- This lemma exists for finsets, but not for sets currently. porting note: move to
data.set.basic after the port. -/
lemma set.disjoint_sdiff_inter {α : Type*} (s t : set α) : disjoint (s \ t) (s ∩ t) :=
disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left

open set

variables {α E ι : Type*} {hm : measurable_space α} {μ : measure α}
  [topological_space α] [borel_space α]
  [normed_add_comm_group E] [normed_space ℝ E]
  {g : α → E} {l : filter ι} {x₀ : α} {s : set α} {φ : ι → α → ℝ}

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `φᵢ • g` is eventually integrable. -/
lemma integrable_on_peak_smul_of_integrable_on_of_continuous_within_at
  (hs : measurable_set s)
  (hlφ : ∀ (u : set α), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 l (s \ u))
  (hiφ : ∀ᶠ i in l, ∫ x in s, φ i x ∂μ = 1)
  (hmg : integrable_on g s μ)
  (hcg : continuous_within_at g s x₀) :
  ∀ᶠ i in l, integrable_on (λ x, φ i x • g x) s μ :=
begin
  obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, is_open u ∧ x₀ ∈ u ∧ ∀ x ∈ u ∩ s, g x ∈ ball (g x₀) 1,
    from mem_nhds_within.1 (hcg (ball_mem_nhds _ zero_lt_one)),
  filter_upwards [tendsto_uniformly_on_iff.1 (hlφ u u_open x₀u) 1 zero_lt_one, hiφ]
    with i hi h'i,
  have A : integrable_on (λ x, φ i x • g x) (s \ u) μ,
  { apply integrable.smul_of_top_right (hmg.mono (diff_subset _ _) le_rfl),
    apply mem_ℒp_top_of_bound
      ((integrable_of_integral_eq_one h'i).ae_strongly_measurable.mono_set ((diff_subset _ _))) 1,
    filter_upwards [self_mem_ae_restrict (hs.diff u_open.measurable_set)] with x hx,
    simpa only [pi.zero_apply, dist_zero_left] using (hi x hx).le },
  have B : integrable_on (λ x, φ i x • g x) (s ∩ u) μ,
  { apply integrable.smul_of_top_left,
    { exact integrable_on.mono_set (integrable_of_integral_eq_one h'i) (inter_subset_left _ _) },
    { apply mem_ℒp_top_of_bound (hmg.mono_set (inter_subset_left _ _)).ae_strongly_measurable
        (‖g x₀‖ + 1),
      filter_upwards [self_mem_ae_restrict (hs.inter u_open.measurable_set)] with x hx,
      rw inter_comm at hx,
      exact (norm_lt_of_mem_ball (hu x hx)).le } },
  convert A.union B,
  simp only [diff_union_inter],
end

variables [complete_space E]

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`. Auxiliary lemma
where one assumes additionally `g x₀ = 0`. -/
lemma tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at_aux
  (hs : measurable_set s)
  (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
  (hlφ : ∀ (u : set α), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 l (s \ u))
  (hiφ : ∀ᶠ i in l, ∫ x in s, φ i x ∂μ = 1)
  (hmg : integrable_on g s μ) (h'g : g x₀ = 0)
  (hcg : continuous_within_at g s x₀) :
  tendsto (λ i : ι, ∫ x in s, φ i x • g x ∂μ) l (𝓝 0) :=
begin
  refine metric.tendsto_nhds.2 (λ ε εpos, _),
  obtain ⟨δ, hδ, δpos⟩ : ∃ δ, δ * ∫ x in s, ‖g x‖ ∂μ + δ < ε ∧ 0 < δ,
  { have A : tendsto (λ δ, δ * ∫ x in s, ‖g x‖ ∂μ + δ) (𝓝[>] 0) (𝓝 (0 * ∫ x in s, ‖g x‖ ∂μ + 0)),
    { apply tendsto.mono_left _ nhds_within_le_nhds,
      exact (tendsto_id.mul tendsto_const_nhds).add tendsto_id },
    rw [zero_mul, zero_add] at A,
    exact (((tendsto_order.1 A).2 ε εpos).and self_mem_nhds_within).exists },
  suffices : ∀ᶠ i in l, ‖∫ x in s, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ + δ,
  { filter_upwards [this] with i hi,
    simp only [dist_zero_right],
    exact hi.trans_lt hδ },
  obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, is_open u ∧ x₀ ∈ u ∧ ∀ x ∈ u ∩ s, g x ∈ ball (g x₀) δ,
    from mem_nhds_within.1 (hcg (ball_mem_nhds _ δpos)),
  filter_upwards [tendsto_uniformly_on_iff.1 (hlφ u u_open x₀u) δ δpos, hiφ, hnφ,
    integrable_on_peak_smul_of_integrable_on_of_continuous_within_at hs hlφ hiφ hmg hcg]
      with i hi h'i hφpos h''i,
  have B : ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ δ, from calc
    ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ ∫ x in s ∩ u, ‖φ i x • g x‖ ∂μ :
      norm_integral_le_integral_norm _
    ... ≤ ∫ x in s ∩ u, ‖φ i x‖ * δ ∂μ :
      begin
        refine set_integral_mono_on _ _ (hs.inter u_open.measurable_set) (λ x hx, _),
        { exact integrable_on.mono_set h''i.norm (inter_subset_left _ _) },
        { exact integrable_on.mono_set ((integrable_of_integral_eq_one h'i).norm.mul_const _)
            (inter_subset_left _ _) },
        rw norm_smul,
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
        rw [inter_comm, h'g] at hu,
        exact (mem_ball_zero_iff.1 (hu x hx)).le,
      end
    ... ≤ ∫ x in s, ‖φ i x‖ * δ ∂μ :
      begin
        apply set_integral_mono_set,
        { exact ((integrable_of_integral_eq_one h'i).norm.mul_const _) },
        { exact eventually_of_forall (λ x, mul_nonneg (norm_nonneg _) δpos.le) },
        { apply eventually_of_forall, exact inter_subset_left s u }
      end
    ... = ∫ x in s, φ i x * δ ∂μ :
      begin
        apply set_integral_congr hs (λ x hx, _),
        rw real.norm_of_nonneg (hφpos _ hx),
      end
    ... = δ : by rw [integral_mul_right, h'i, one_mul],
  have C : ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ, from calc
    ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ ∫ x in s \ u, ‖φ i x • g x‖ ∂μ :
      norm_integral_le_integral_norm _
    ... ≤ ∫ x in s \ u, δ * ‖g x‖ ∂μ :
      begin
        refine set_integral_mono_on _ _ (hs.diff u_open.measurable_set) (λ x hx, _),
        { exact integrable_on.mono_set h''i.norm (diff_subset _ _) },
        { exact integrable_on.mono_set (hmg.norm.const_mul _) (diff_subset _ _) },
        rw norm_smul,
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
        simpa only [pi.zero_apply, dist_zero_left] using (hi x hx).le,
      end
    ... ≤ δ * ∫ x in s, ‖g x‖ ∂μ :
      begin
        rw integral_mul_left,
        apply mul_le_mul_of_nonneg_left (set_integral_mono_set hmg.norm _ _) δpos.le,
        { exact eventually_of_forall (λ x, norm_nonneg _) },
        { apply eventually_of_forall, exact diff_subset s u }
      end,
  calc
  ‖∫ x in s, φ i x • g x ∂μ‖ = ‖∫ x in s \ u, φ i x • g x ∂μ + ∫ x in s ∩ u, φ i x • g x ∂μ‖ :
    begin
      conv_lhs { rw ← diff_union_inter s u },
      rw integral_union (disjoint_sdiff_inter _ _) (hs.inter u_open.measurable_set)
        (h''i.mono_set (diff_subset _ _)) (h''i.mono_set (inter_subset_left _ _))
    end
  ... ≤ ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ : norm_add_le _ _
  ... ≤ δ * ∫ x in s, ‖g x‖ ∂μ + δ : add_le_add C B
end

/- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `x₀`. -/
lemma tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at
  (hs : measurable_set s) (h's : μ s ≠ ∞)
  (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
  (hlφ : ∀ (u : set α), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 l (s \ u))
  (hiφ : (λ i, ∫ x in s, φ i x ∂μ) =ᶠ[l] 1)
  (hmg : integrable_on g s μ)
  (hcg : continuous_within_at g s x₀) :
  tendsto (λ i : ι, ∫ x in s, φ i x • g x ∂μ) l (𝓝 (g x₀)) :=
begin
  let h := g - (λ y, g x₀),
  have A : tendsto (λ i : ι, ∫ x in s, φ i x • h x ∂μ + (∫ x in s, φ i x ∂μ) • g x₀) l
    (𝓝 (0 + (1 : ℝ) • g x₀)),
  { refine tendsto.add _ (tendsto.smul (tendsto_const_nhds.congr' hiφ.symm) tendsto_const_nhds),
    apply tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at_aux
      hs hnφ hlφ hiφ,
    { apply integrable.sub hmg,
      apply integrable_on_const.2,
      simp only [h's.lt_top, or_true] },
    { simp only [h, pi.sub_apply, sub_self] },
    { exact hcg.sub continuous_within_at_const } },
  simp only [one_smul, zero_add] at A,
  refine tendsto.congr' _ A,
  filter_upwards [integrable_on_peak_smul_of_integrable_on_of_continuous_within_at
    hs hlφ hiφ hmg hcg, hiφ] with i hi h'i,
  simp only [h, pi.sub_apply, smul_sub],
  rw [integral_sub hi, integral_smul_const, sub_add_cancel],
  exact integrable.smul_const (integrable_of_integral_eq_one h'i) _,
end

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all neighborhoods of `x₀` within `s`.
For a less precise but more usable version, see
`tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_continuous_on`.
 -/
lemma tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_measure_nhds_within_pos
  [metrizable_space α] [is_locally_finite_measure μ] (hs : is_compact s)
  (hμ : ∀ u, is_open u → x₀ ∈ u → 0 < μ (u ∩ s))
  {c : α → ℝ} (hc : continuous_on c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
  (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ s)
  (hmg : integrable_on g s μ)
  (hcg : continuous_within_at g s x₀) :
  tendsto (λ (n : ℕ), (∫ x in s, (c x) ^ n ∂μ)⁻¹ • (∫ x in s, (c x) ^ n • g x ∂μ)) at_top
    (𝓝 (g x₀)) :=
begin
  /- We apply the general result
  `tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at` to the sequence of
  peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
  sequence converges uniformly to zero on any set `s \ u` away from `x₀`. By compactness, the
  function `c` is bounded by `t < c x₀` there. Consider `t' ∈ (t, c x₀)`, and a neighborhood `v`
  of `x₀` where `c x ≥ t'`, by continuity. Then `∫ (c x) ^ n` is bounded below by `t' ^ n μ v`.
  It follows that, on `s \ u`, then `φₙ x ≤ t ^ n / (t' ^ n μ v)`, which tends (exponentially fast)
  to zero with `n`. -/
  let φ : ℕ → α → ℝ := λ n x, (∫ x in s, (c x) ^ n ∂μ)⁻¹ * (c x) ^ n,
  have hnφ : ∀ n, ∀ x ∈ s, 0 ≤ φ n x,
  { assume n x hx,
    apply mul_nonneg (inv_nonneg.2 _) (pow_nonneg (hnc x hx) _),
    exact set_integral_nonneg hs.measurable_set (λ x hx, pow_nonneg (hnc x hx) _) },
  have I : ∀ n, integrable_on (λ x, (c x)^n) s μ :=
    λ n, continuous_on.integrable_on_compact hs (hc.pow n),
  have J : ∀ n, 0 ≤ᵐ[μ.restrict s] λ (x : α), c x ^ n,
  { assume n,
    filter_upwards [ae_restrict_mem hs.measurable_set] with x hx,
    exact pow_nonneg (hnc x hx) n },
  have P : ∀ n, 0 < ∫ x in s, (c x) ^ n ∂μ,
  { assume n,
    refine (set_integral_pos_iff_support_of_nonneg_ae (J n) (I n)).2 _,
    obtain ⟨u, u_open, x₀_u, hu⟩ : ∃ (u : set α), is_open u ∧ x₀ ∈ u ∧ u ∩ s ⊆ c ⁻¹' Ioi 0 :=
      _root_.continuous_on_iff.1 hc x₀ h₀ (Ioi (0 : ℝ)) is_open_Ioi hnc₀,
    apply (hμ u u_open x₀_u).trans_le,
    exact measure_mono (λ x hx, ⟨ne_of_gt (pow_pos (hu hx) _), hx.2⟩) },
  have hiφ : ∀ n, ∫ x in s, φ n x ∂μ = 1 :=
    λ n, by rw [integral_mul_left, inv_mul_cancel (P n).ne'],
  have A : ∀ (u : set α), is_open u → x₀ ∈ u → tendsto_uniformly_on φ 0 at_top (s \ u),
  { assume u u_open x₀u,
    obtain ⟨t, t_pos, tx₀, ht⟩ : ∃ t, 0 ≤ t ∧ t < c x₀ ∧ (∀ x ∈ s \ u, c x ≤ t),
    { rcases eq_empty_or_nonempty (s \ u) with h|h,
      { exact ⟨0, le_rfl, hnc₀,
          by simp only [h, mem_empty_iff_false, is_empty.forall_iff, implies_true_iff]⟩ },
      obtain ⟨x, hx, h'x⟩ : ∃ x ∈ s \ u, ∀ y ∈ s \ u, c y ≤ c x :=
        is_compact.exists_forall_ge (hs.diff u_open) h (hc.mono (diff_subset _ _)),
      refine ⟨c x, hnc x hx.1, h'c x hx.1 _, h'x⟩,
      rintros rfl,
      exact hx.2 x₀u },
    obtain ⟨t', tt', t'x₀⟩ : ∃ t', t < t' ∧ t' < c x₀ := exists_between tx₀,
    have t'_pos : 0 < t' := t_pos.trans_lt tt',
    obtain ⟨v, v_open, x₀_v, hv⟩ : ∃ (v : set α), is_open v ∧ x₀ ∈ v ∧ v ∩ s ⊆ c ⁻¹' Ioi t' :=
      _root_.continuous_on_iff.1 hc x₀ h₀ (Ioi t') is_open_Ioi t'x₀,
    have M : ∀ n, ∀ x ∈ s \ u, φ n x ≤ (μ (v ∩ s)).to_real ⁻¹ * (t / t') ^ n,
    { assume n x hx,
      have B : t' ^ n * (μ (v ∩ s)).to_real ≤ ∫ y in s, (c y) ^ n ∂μ, from calc
        t' ^ n * (μ (v ∩ s)).to_real = ∫ y in v ∩ s, t' ^ n ∂μ :
          by simp only [integral_const, measure.restrict_apply, measurable_set.univ, univ_inter,
              algebra.id.smul_eq_mul, mul_comm]
        ... ≤ ∫ y in v ∩ s, (c y) ^ n ∂μ :
          begin
            apply set_integral_mono_on _ _ (v_open.measurable_set.inter hs.measurable_set) _,
            { apply integrable_on_const.2 (or.inr _),
              exact lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) hs.measure_lt_top },
            { exact (I n).mono (inter_subset_right _ _) le_rfl },
            { assume x hx,
              exact pow_le_pow_of_le_left t'_pos.le (le_of_lt (hv hx)) _ }
          end
        ... ≤ ∫ y in s, (c y) ^ n ∂μ :
          set_integral_mono_set (I n) (J n) (eventually_of_forall (inter_subset_right _ _)),
      simp_rw [φ, ← div_eq_inv_mul, div_pow, div_div],
      apply div_le_div (pow_nonneg t_pos n) _ _ B,
      { exact pow_le_pow_of_le_left (hnc _ hx.1) (ht x hx) _ },
      { apply mul_pos (pow_pos (t_pos.trans_lt tt') _)
          (ennreal.to_real_pos (hμ v v_open x₀_v).ne' _),
        have : μ (v ∩ s) ≤ μ s := measure_mono (inter_subset_right _ _),
        exact ne_of_lt (lt_of_le_of_lt this hs.measure_lt_top) } },
    have N : tendsto (λ n, (μ (v ∩ s)).to_real ⁻¹ * (t / t') ^ n) at_top
      (𝓝 ((μ (v ∩ s)).to_real ⁻¹ * 0)),
    { apply tendsto.mul tendsto_const_nhds _, { apply_instance },
      apply tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg t_pos t'_pos.le),
      exact (div_lt_one t'_pos).2 tt' },
    rw mul_zero at N,
    refine tendsto_uniformly_on_iff.2 (λ ε εpos, _),
    filter_upwards [(tendsto_order.1 N).2 ε εpos] with n hn x hx,
    simp only [pi.zero_apply, dist_zero_left, real.norm_of_nonneg (hnφ n x hx.1)],
    exact (M n x hx).trans_lt hn },
  have : tendsto (λ (i : ℕ), ∫ (x : α) in s, φ i x • g x ∂μ) at_top (𝓝 (g x₀)) :=
    tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at hs.measurable_set
      hs.measure_lt_top.ne (eventually_of_forall hnφ) A (eventually_of_forall hiφ) hmg hcg,
  convert this,
  simp_rw [← smul_smul, integral_smul],
end

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all open sets.
For a less precise but more usable version, see
`tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_continuous_on`.
-/
lemma tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_integrable_on
  [metrizable_space α] [is_locally_finite_measure μ] [is_open_pos_measure μ] (hs : is_compact s)
  {c : α → ℝ} (hc : continuous_on c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
  (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
  (hmg : integrable_on g s μ)
  (hcg : continuous_within_at g s x₀) :
  tendsto (λ (n : ℕ), (∫ x in s, (c x) ^ n ∂μ)⁻¹ • (∫ x in s, (c x) ^ n • g x ∂μ)) at_top
    (𝓝 (g x₀)) :=
begin
  have : x₀ ∈ s,
  { rw ← hs.is_closed.closure_eq, exact closure_mono interior_subset h₀ },
  apply tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_measure_nhds_within_pos
    hs _ hc h'c hnc hnc₀ this hmg hcg,
  assume u u_open x₀_u,
  calc 0 < μ (u ∩ interior s) :
    (u_open.inter is_open_interior).measure_pos μ (_root_.mem_closure_iff.1 h₀ u u_open x₀_u)
  ... ≤ μ (u ∩ s) : measure_mono (inter_subset_inter_right _ interior_subset)
end

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
continuous on `s`. -/
lemma tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_continuous_on
  [metrizable_space α] [is_locally_finite_measure μ] [is_open_pos_measure μ] (hs : is_compact s)
  {c : α → ℝ} (hc : continuous_on c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
  (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
  (hmg : continuous_on g s) :
  tendsto (λ (n : ℕ), (∫ x in s, (c x) ^ n ∂μ)⁻¹ • (∫ x in s, (c x) ^ n • g x ∂μ)) at_top
    (𝓝 (g x₀)) :=
begin
  have : x₀ ∈ s,
  { rw ← hs.is_closed.closure_eq, exact closure_mono interior_subset h₀ },
  exact tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_integrable_on
    hs hc h'c hnc hnc₀ h₀ (hmg.integrable_on_compact hs) (hmg x₀ this)
end
