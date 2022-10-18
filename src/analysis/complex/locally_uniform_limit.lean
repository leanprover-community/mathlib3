/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.complex.cauchy_integral
import analysis.complex.removable_singularity
import analysis.calculus.uniform_limits_deriv

/-!
# Locally uniform limits of holomorphic functions

## Main results

* `tendsto_locally_uniformly_on.differentiable_on`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `tendsto_locally_uniformly_on.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/

open set metric measure_theory filter complex interval_integral
open_locale real topological_space

section cauchy_deriv

variables {E : Type*} [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]
  {w₀ w c z : ℂ} {R M : ℝ} {f : ℂ → E} {U : set ℂ}

lemma diff_cont_on_cl.two_pi_I_inv_smul_circle_integral_sub_inv_smul
  (hf : diff_cont_on_cl ℂ f (metric.ball c R)) (hw : w ∈ metric.ball c R) :
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z = f w :=
begin
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (nonempty_of_mem hw).ne_empty),
  refine two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw _ _,
  { simpa only [closure_ball c hR.ne.symm] using hf.continuous_on },
  { simpa only [diff_empty] using λ z hz, hf.differentiable_at is_open_ball hz }
end

lemma two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable (hU : is_open U)
  (hc : closed_ball c R ⊆ U) (hf : differentiable_on ℂ f U) (hw₀ : w₀ ∈ ball c R) :
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • f z = deriv f w₀ :=
begin
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (nonempty_of_mem hw₀).ne_empty),
  have hf' : differentiable_on ℂ (dslope f w₀) U,
    from (differentiable_on_dslope (hU.mem_nhds ((ball_subset_closed_ball.trans hc) hw₀))).mpr hf,
  have h0 := (hf'.diff_cont_on_cl_ball hR hc).two_pi_I_inv_smul_circle_integral_sub_inv_smul hw₀,
  rw [← dslope_same, ← h0],
  congr' 1,
  transitivity ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • (f z - f w₀),
  { have h1 : continuous_on (λ (z : ℂ), ((z - w₀) ^ 2)⁻¹) (sphere c R),
    { refine ((continuous_id'.sub continuous_const).pow 2).continuous_on.inv₀ (λ w hw h, _),
      exact sphere_disjoint_ball.ne_of_mem hw hw₀ (sub_eq_zero.mp (sq_eq_zero_iff.mp h)) },
    have h2 : circle_integrable (λ (z : ℂ), ((z - w₀) ^ 2)⁻¹ • f z) c R,
    { refine continuous_on.circle_integrable (pos_of_mem_ball hw₀).le _,
      exact h1.smul (hf.continuous_on.mono (sphere_subset_closed_ball.trans hc)) },
    have h3 : circle_integrable (λ (z : ℂ), ((z - w₀) ^ 2)⁻¹ • f w₀) c R,
      from continuous_on.circle_integrable (pos_of_mem_ball hw₀).le (h1.smul continuous_on_const),
    have h4 : ∮ (z : ℂ) in C(c, R), ((z - w₀) ^ 2)⁻¹ = 0,
      by simpa using circle_integral.integral_sub_zpow_of_ne (dec_trivial : (-2 : ℤ) ≠ -1) c w₀ R,
    simp only [smul_sub, circle_integral.integral_sub h2 h3, h4,
      circle_integral.integral_smul_const, zero_smul, sub_zero] },
  { refine circle_integral.integral_congr (pos_of_mem_ball hw₀).le (λ z hz, _),
    simp only [dslope_of_ne, metric.sphere_disjoint_ball.ne_of_mem hz hw₀, slope, ← smul_assoc, sq,
      mul_inv, ne.def, not_false_iff, vsub_eq_sub, algebra.id.smul_eq_mul] }
end

end cauchy_deriv

section unif_compact

variables {α β γ ι : Type*} [topological_space α] [uniform_space β] [pseudo_metric_space γ]
  {φ : filter ι} {G H : ι → α → β} {g h : α → β} {F : ι → α → γ} {f : α → γ}
  {s t : set α} {a : α}

lemma tendsto_locally_uniformly_on_tfae [locally_compact_space α]
  (G : ι → α → β) (g : α → β) (φ : filter ι) (ht : is_open t) :
  [ (tendsto_locally_uniformly_on G g φ t),
    (∀ K ⊆ t, is_compact K → tendsto_uniformly_on G g φ K),
    (∀ x ∈ t, ∃ v ∈ 𝓝[t] x, tendsto_uniformly_on G g φ v) ].tfae :=
begin
  tfae_have : 1 → 2,
  { rintro h K hK1 hK2,
    exact (tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_of_compact hK2).mp (h.mono hK1) },
  tfae_have : 2 → 3,
  { rintro h x hx,
    obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp (ht.mem_nhds hx),
    refine ⟨K, nhds_within_le_nhds hK1, h K hK3 hK2⟩ },
  tfae_have : 3 → 1,
  { rintro h u hu x hx,
    obtain ⟨v, hv1, hv2⟩ := h x hx,
    exact ⟨v, hv1, hv2 u hu⟩ },
  tfae_finish
end

lemma tendsto_locally_uniformly_on_iff_forall_compact [locally_compact_space α] (ht : is_open t) :
  tendsto_locally_uniformly_on G g φ t ↔
  ∀ K ⊆ t, is_compact K → tendsto_uniformly_on G g φ K :=
(tendsto_locally_uniformly_on_tfae G g φ ht).out 0 1

lemma tendsto_locally_uniformly_on_iff_filter :
  tendsto_locally_uniformly_on G g φ t ↔
  ∀ x ∈ t, tendsto_uniformly_on_filter G g φ (𝓝[t] x) :=
begin
  simp only [tendsto_uniformly_on_filter, eventually_prod_iff],
  split,
  { rintro h x hx u hu,
    obtain ⟨s, hs1, hs2⟩ := h u hu x hx,
    exact ⟨_, hs2, _, eventually_of_mem hs1 (λ x, id), λ i hi y hy, hi y hy⟩ },
  { rintro h u hu x hx,
    obtain ⟨pa, hpa, pb, hpb, h⟩ := h x hx u hu,
    refine ⟨pb, hpb, eventually_of_mem hpa (λ i hi y hy, h hi hy)⟩ }
end

lemma tendsto_locally_uniformly_iff_filter :
  tendsto_locally_uniformly G g φ ↔
  ∀ x, tendsto_uniformly_on_filter G g φ (𝓝 x) :=
by simpa [← tendsto_locally_uniformly_on_univ, ← nhds_within_univ] using
  @tendsto_locally_uniformly_on_iff_filter _ _ _ _ _ _ _ _ univ

lemma tendsto_locally_uniformly_on.tendsto_at (hg : tendsto_locally_uniformly_on G g φ t)
  ⦃a : α⦄ (ha : a ∈ t) :
  tendsto (λ i, G i a) φ (𝓝 (g a)) :=
begin
  refine ((tendsto_locally_uniformly_on_iff_filter.mp hg) a ha).tendsto_at _,
  simpa only [filter.principal_singleton] using pure_le_nhds_within ha
end

lemma tendsto_locally_uniformly_on.unique [φ.ne_bot] [t2_space β]
  (hg : tendsto_locally_uniformly_on G g φ t) (hh : tendsto_locally_uniformly_on G h φ t) :
  t.eq_on g h :=
λ a ha, tendsto_nhds_unique (hg.tendsto_at ha) (hh.tendsto_at ha)

lemma tendsto_locally_uniformly_on.congr (hg : tendsto_locally_uniformly_on G g φ t)
  (hh : ∀ n, t.eq_on (G n) (H n)) :
  tendsto_locally_uniformly_on H g φ t :=
begin
  rintro u hu x hx,
  obtain ⟨t', ht', h⟩ := hg u hu x hx,
  refine ⟨t ∩ t', inter_mem self_mem_nhds_within ht', _⟩,
  filter_upwards [h] with i hi y hy using hh i hy.1 ▸ hi y hy.2
end

lemma tendsto_locally_uniformly_on.congr' (hg : tendsto_locally_uniformly_on G g φ t)
  (hh : t.eq_on g h) :
  tendsto_locally_uniformly_on G h φ t :=
begin
  rintro u hu x hx,
  obtain ⟨t', ht', h⟩ := hg u hu x hx,
  refine ⟨t ∩ t', inter_mem self_mem_nhds_within ht', _⟩,
  filter_upwards [h] with i hi y hy using hh hy.1 ▸ hi y hy.2
end

end unif_compact

section cderiv

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
  {ι : Type*} {φ : filter ι} {U K : set ℂ} {z : ℂ} {f g : ℂ → E} {F : ι → ℂ → E} {M r δ : ℝ}

noncomputable def cderiv (r : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  (2 * π * I : ℂ)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w

lemma norm_cderiv_le (hr : 0 < r) (hf : ∀ w ∈ sphere z r, ∥f w∥ ≤ M) :
  ∥cderiv r f z∥ ≤ M / r :=
begin
  have hM : 0 ≤ M,
  { obtain ⟨w, hw⟩ : ∃ w : ℂ, w ∈ sphere z r := normed_space.sphere_nonempty.mpr hr.le,
    exact (norm_nonneg _).trans (hf w hw) },
  have h1 : ∀ w ∈ sphere z r, ∥((w - z) ^ 2)⁻¹ • f w∥ ≤ M / r ^ 2,
  { intros w hw,
    simp only [mem_sphere_iff_norm, norm_eq_abs] at hw,
    simp only [norm_smul, inv_mul_eq_div, hw, norm_eq_abs, map_inv₀, complex.abs_pow],
    exact div_le_div hM (hf w hw) (sq_pos_of_pos hr) le_rfl },
  have h2 := circle_integral.norm_integral_le_of_norm_le_const hr.le h1,
  simp only [cderiv, norm_smul],
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq _),
  field_simp [_root_.abs_of_nonneg real.pi_pos.le, real.pi_pos.ne.symm, hr.ne.symm],
  ring
end

lemma cderiv_eq_deriv (hU : is_open U) (hf : differentiable_on ℂ f U) (hr : 0 < r)
  (hzr : closed_ball z r ⊆ U) :
  cderiv r f z = deriv f z :=
two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

lemma dist_cderiv_le (hr : 0 < r) (hzr : closed_ball z r ⊆ U)
  (hfg : ∀ w ∈ sphere z r, ∥f w - g w∥ < M)
  (hf : continuous_on f U) (hg : continuous_on g U) :
  dist (cderiv r f z) (cderiv r g z) < M / r :=
begin
  obtain ⟨L, hL1, hL2⟩ : ∃ L, L < M ∧ ∀ w ∈ sphere z r, ∥f w - g w∥ ≤ L,
  { have e0 : sphere z r ⊆ U := sphere_subset_closed_ball.trans hzr,
    have e1 : is_compact (sphere z r) := is_compact_sphere z r,
    have e2 : (sphere z r).nonempty := normed_space.sphere_nonempty.mpr hr.le,
    have e3 : continuous_on (λ w, ∥f w - g w∥) (sphere z r),
      from continuous_norm.comp_continuous_on ((hf.mono e0).sub (hg.mono e0)),
    obtain ⟨x, hx, hx'⟩ := is_compact.exists_forall_ge e1 e2 e3,
    refine ⟨∥f x - g x∥, hfg x hx, hx'⟩ },
  have h1 : L / r < M / r := (div_lt_div_right hr).mpr hL1,
  have h2 : continuous_on (λ (w : ℂ), ((w - z) ^ 2)⁻¹) (sphere z r),
  { refine ((continuous_id'.sub continuous_const).pow 2).continuous_on.inv₀ (λ w hw h, hr.ne _),
    simpa [sq_eq_zero_iff.mp h] using mem_sphere_iff_norm.mp hw },
  convert ← (norm_cderiv_le hr hL2).trans_lt h1 using 1,
  simp only [dist_eq_norm, cderiv, ← smul_sub],
  congr' 2,
  simp only [smul_sub],
  refine circle_integral.integral_sub _ _,
  { have e1 := (h2.smul (continuous_on.mono hf ((sphere_subset_closed_ball).trans hzr))),
    exact continuous_on.circle_integrable hr.le e1 },
  { have e1 := (h2.smul (continuous_on.mono hg ((sphere_subset_closed_ball).trans hzr))),
    exact continuous_on.circle_integrable hr.le e1 }
end

lemma tendsto_uniformly_on_cderiv (hU : is_open U) (hf : continuous_on f U) (hK2 : is_compact K)
  (hδ : 0 < δ) (hFn : ∀ n, continuous_on (F n) U) (hK3 : cthickening δ K ⊆ U)
  (hF : tendsto_uniformly_on F f φ (cthickening δ K)) :
  tendsto_uniformly_on (λ n, cderiv δ (F n)) (cderiv δ f) φ K :=
begin
  have hK1 : K ⊆ U := (self_subset_cthickening _).trans hK3,
  rw [tendsto_uniformly_on_iff] at hF ⊢,
  rintro ε hε,
  filter_upwards [hF (ε * δ) (mul_pos hε hδ)] with n h z hz,
  simp_rw [dist_eq_norm] at h,
  have h2 : ∀ w ∈ sphere z δ, ∥f w - F n w∥ < ε * δ,
    from λ w hw1, h w (closed_ball_subset_cthickening hz δ (sphere_subset_closed_ball hw1)),
  convert dist_cderiv_le hδ ((closed_ball_subset_cthickening hz δ).trans hK3) h2 hf (hFn n),
  field_simp [hδ.ne.symm]; ring
end

end cderiv

section deriv_limit

variables {𝕜 β ι : Type*} [is_R_or_C 𝕜] [normed_add_comm_group β] [normed_space 𝕜 β]
  {U : set 𝕜} {x : 𝕜} {F : ι → 𝕜 → β} {f g : 𝕜 → β} {φ : filter ι} [ne_bot φ]

lemma has_deriv_at_of_tendsto_localy_uniformly_on (hU : is_open U) (hx : x ∈ U)
  (hF : ∀ n, differentiable_on 𝕜 (F n) U) (hf : ∀ x ∈ U, tendsto (λ n, F n x) φ (𝓝 (f x)))
  (hg : tendsto_locally_uniformly_on (deriv ∘ F) g φ U) :
  has_deriv_at f (g x) x :=
begin
  have h1 : U ∈ 𝓝 x := hU.mem_nhds hx,
  have h2 : tendsto_uniformly_on_filter (deriv ∘ F) g φ (𝓝[U] x),
    from tendsto_locally_uniformly_on_iff_filter.mp hg x hx,
  rw [is_open.nhds_within_eq hU hx] at h2,
  have h3 : (univ ×ˢ U) ∈ φ.prod (𝓝 x) := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self],
  have h4 : ∀ᶠ (n : ι × 𝕜) in φ.prod (𝓝 x), has_deriv_at (F n.1) (deriv (F n.1) n.2) n.2,
    from eventually_of_mem h3 (λ ⟨n, z⟩ ⟨hn, hz⟩, (hF n).has_deriv_at (hU.mem_nhds hz)),
  exact has_deriv_at_of_tendsto_uniformly_on_filter h2 h4 (eventually_of_mem h1 hf),
end

end deriv_limit

section weierstrass

variables {ι E : Type*} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
  {φ : filter ι} [ne_bot φ] {U K : set ℂ} (hU : is_open U) {F : ι → ℂ → E} {f g : ℂ → E}
  (hF : ∀ n, differentiable_on ℂ (F n) U) (hf : tendsto_locally_uniformly_on F f φ U)
include hU hF hf

lemma tendsto_uniformly_on_deriv_of_cthickening_subset {δ : ℝ} (hδ: 0 < δ) (hK : is_compact K)
  (hKU: cthickening δ K ⊆ U) :
  tendsto_uniformly_on (deriv ∘ F) (cderiv δ f) φ K :=
begin
  have h1 : ∀ n, continuous_on (F n) U := λ n, (hF n).continuous_on,
  have h2 : continuous_on f U := hf.continuous_on (eventually_of_forall h1),
  have h3 : is_compact (cthickening δ K),
    from is_compact_of_is_closed_bounded is_closed_cthickening hK.bounded.cthickening,
  have h4 : tendsto_uniformly_on F f φ (cthickening δ K),
    from (tendsto_locally_uniformly_on_iff_forall_compact hU).mp hf (cthickening δ K) hKU h3,
  have h5 : tendsto_uniformly_on (cderiv δ ∘ F) (cderiv δ f) φ K,
    from tendsto_uniformly_on_cderiv hU h2 hK hδ h1 hKU h4,
  refine h5.congr (eventually_of_forall (λ n z hz, _)),
  exact cderiv_eq_deriv hU (hF n) hδ ((closed_ball_subset_cthickening hz δ).trans hKU)
end

lemma exists_cthickening_tendsto_uniformly_on (hK : is_compact K) (hKU : K ⊆ U) :
  ∃ δ > 0, cthickening δ K ⊆ U ∧ tendsto_uniformly_on (deriv ∘ F) (cderiv δ f) φ K :=
begin
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU,
  exact ⟨δ, hδ, hKδ, tendsto_uniformly_on_deriv_of_cthickening_subset hU hF hf hδ hK hKδ⟩
end

lemma tendsto_locally_uniformly_on.differentiable_on : differentiable_on ℂ f U :=
begin
  rintro x hx,
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx),
  obtain ⟨δ, hδ, -, h1⟩ := exists_cthickening_tendsto_uniformly_on hU hF hf hK hKU,
  have h2 : interior K ⊆ U := interior_subset.trans hKU,
  have h3 : ∀ n, differentiable_on ℂ (F n) (interior K) := λ n, (hF n).mono h2,
  have h4 : tendsto_locally_uniformly_on F f φ (interior K) := hf.mono h2,
  have h5 : tendsto_locally_uniformly_on (deriv ∘ F) (cderiv δ f) φ (interior K),
    from h1.tendsto_locally_uniformly_on.mono interior_subset,
  have h6 : ∀ x ∈ interior K, has_deriv_at f (cderiv δ f x) x,
    from λ x h, has_deriv_at_of_tendsto_localy_uniformly_on is_open_interior h h3 h4.tendsto_at h5,
  have h7 : differentiable_on ℂ f (interior K),
    from λ x hx, (h6 x hx).differentiable_at.differentiable_within_at,
  exact (h7.differentiable_at (interior_mem_nhds.mpr hKx)).differentiable_within_at
end

lemma tendsto_locally_uniformly_on.deriv :
  tendsto_locally_uniformly_on (deriv ∘ F) (deriv f) φ U :=
begin
  refine (tendsto_locally_uniformly_on_iff_forall_compact hU).mpr (λ K hKU hK, _),
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendsto_uniformly_on hU hF hf hK hKU,
  refine h.congr' (λ z hz, _),
  refine cderiv_eq_deriv hU _ hδ ((closed_ball_subset_cthickening hz δ).trans hK4),
  exact hf.differentiable_on hU hF
end

end weierstrass
