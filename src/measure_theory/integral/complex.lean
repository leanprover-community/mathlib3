import measure_theory.measure.complex_lebesgue
import measure_theory.integral.divergence_theorem
import analysis.calculus.parametric_interval_integral
import analysis.analytic.basic
--import measure_theory.integral.periodic

/-!
-/

open topological_space set measure_theory interval_integral metric filter function
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u v

variables {E : Type u} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

namespace complex

lemma integral_boundary_rect_of_has_fderiv_within_at_real_off_countable (f : ℂ → E)
  (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ) (s : set ℂ) (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x)
  (Hd : ∀ x ∈ (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) \ s, has_fderiv_within_at f (f' x)
    (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x)
  (Hi : integrable_on (λ z, I • f' z 1 - f' z I) (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im])) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
    ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
begin
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equiv_real_prodₗ.symm,
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y), from λ x y, (mk_eq_add_mul_I x y).symm,
  have he₁ : e (1, 0) = 1 := rfl, have he₂ : e (0, 1) = I := rfl,
  simp only [he] at *,
  set F : (ℝ × ℝ) → E := f ∘ e,
  set F' : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] E := λ p, (f' (e p)).comp (e : (ℝ × ℝ) →L[ℝ] ℂ),
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I),
  { rintro ⟨x, y⟩, simp [F', he₁, he₂, ← sub_eq_neg_add] },
  set R : set (ℝ × ℝ) := [z.re, w.re].prod [w.im, z.im],
  set t : set (ℝ × ℝ) := e ⁻¹' s,
  rw [interval_swap z.im] at Hc Hd Hi,
  have hR : e ⁻¹' (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [w.im, z.im]) = R := rfl,
  have htc : ∀ p ∈ t, continuous_within_at F R p,
    from λ p hp, (Hc (e p) hp).comp e.continuous_within_at hR.ge,
  have htd : ∀ p ∈ R \ t, has_fderiv_within_at F (F' p) R p,
    from λ p hp, (Hd (e p) hp).comp p e.has_fderiv_within_at hR.ge,
  simp_rw [← interval_integral.integral_smul, interval_integral.integral_symm w.im z.im,
    ← interval_integral.integral_neg, ← hF'],
  refine (integral2_divergence_prod_of_has_fderiv_within_at_off_countable
      (λ p, -(I • F p)) F (λ p, - (I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
      (λ p hp, (continuous_within_at_const.smul (htc p hp)).neg) htc
      (λ p hp, ((htd p hp).const_smul I).neg) htd _).symm,
  rw [← volume_preserving_equiv_real_prod.symm.integrable_on_comp_preimage
    (measurable_equiv.measurable_embedding _)] at Hi,
  simpa only [hF'] using Hi.neg
end

lemma integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E)
  (z w : ℂ) (s : set ℂ) (hs : countable s)
  (Hc : ∀ x ∈ s, continuous_within_at f (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x)
  (Hd : ∀ x ∈ (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) \ s, differentiable_within_at ℂ f
    (re ⁻¹' [z.re, w.re] ∩ im ⁻¹' [z.im, w.im]) x) :
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    (I • ∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) = 0 :=
by refine (integral_boundary_rect_of_has_fderiv_within_at_real_off_countable f
  (λ z, (fderiv_within ℂ f _ z).restrict_scalars ℝ) z w s hs Hc
  (λ x hx, (Hd x hx).has_fderiv_within_at.restrict_scalars ℝ) _).trans _;
    simp [← continuous_linear_map.map_smul]

lemma integral_circle_darg_eq_of_differentiable_on_annulus_off_countable
  {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : set ℂ} (hs : countable s)
  (hc : ∀ z ∈ s, continuous_within_at f (closed_ball 0 R \ ball 0 r) z)
  (hd : ∀ z ∈ (closed_ball 0 R \ ball 0 r) \ s,
    differentiable_within_at ℂ f (closed_ball 0 R \ ball 0 r) z) :
  ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = ∫ (θ : ℝ) in 0..2 * π, f (r * exp (θ * I)) :=
begin
  set A := closed_ball (0 : ℂ) R \ ball 0 r,
  obtain ⟨a, rfl⟩ : ∃ a, real.exp a = r, from ⟨real.log r, real.exp_log h0⟩,
  obtain ⟨b, rfl⟩ : ∃ b, real.exp b = R, from ⟨real.log R, real.exp_log (h0.trans_le hle)⟩,
  simp only [of_real_exp, ← exp_add], rw [real.exp_le_exp] at hle,
  replace hs : countable (exp ⁻¹' s) := hs.preimage_cexp,
  set R := re ⁻¹' [a, b] ∩ im ⁻¹' [0, 2 * π],
  have h_maps : maps_to exp R A,
  { rintro z ⟨h, -⟩, simpa [abs_exp, hle] using h.symm },
  replace hc : ∀ z ∈ exp ⁻¹' s, continuous_within_at (f ∘ exp) R z,
    from λ z hz, (hc (exp z) hz).comp continuous_within_at_id.cexp h_maps,
  replace hd : ∀ z ∈ R \ exp ⁻¹' s, differentiable_within_at ℂ (f ∘ exp) R z,
  { intros z hz,
    exact (hd (exp z) ⟨h_maps hz.1, hz.2⟩).comp z differentiable_within_at_id.cexp h_maps  },
  simpa [exp_periodic _, sub_eq_zero, (smul_right_injective E I_ne_zero).eq_iff]
    using integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩
      _ hs hc hd
end


-- These integrals are `∫ f z dz/iz`
lemma integral_circle_darg_of_differentiable_on_off_countable_of_tendsto
  {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : set ℂ} (hs : countable s)
  (hc : ∀ z ∈ s, continuous_within_at f (closed_ball 0 R \ {0}) z)
  (hd : ∀ z ∈ closed_ball 0 R \ {(0 : ℂ)} \ s,
    differentiable_within_at ℂ f (closed_ball 0 R \ {0}) z)
  (hy : tendsto f (𝓝[{0}ᶜ] 0) (𝓝 y)) :
  ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = (2 * π) • y :=
begin
  rw [← sub_eq_zero, ← norm_le_zero_iff],
  refine le_of_forall_le_of_dense (λ ε ε0, _),
  obtain ⟨δ, δ0, hδ⟩ :
    ∃ δ > (0 : ℝ), ∀ z ∈ closed_ball (0 : ℂ) δ \ {0}, dist (f z) y < ε / (2 * π),
    from ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 real.two_pi_pos),
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩,
  have hsub : closed_ball (0 : ℂ) R \ ball 0 r ⊆ closed_ball 0 R \ {(0 : ℂ)},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_ball_self hr0),
  have : ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = ∫ (θ : ℝ) in 0..2 * π, f (r * exp (θ * I)),
  { refine integral_circle_darg_eq_of_differentiable_on_annulus_off_countable hr0 hrR hs _ _,
    exacts [λ z hz, (hc z hz).mono hsub, λ z hz, (hd z ⟨hsub hz.1, hz.2⟩).mono hsub] },
  rw this,
  have hmem : ∀ y : ℝ, ↑r * exp (y * I) ∈ closed_ball (0 : ℂ) r \ {0},
  { intro x, simp [abs_of_nonneg hr0.le, hr0.ne', exp_ne_zero] },
  have : ∫ (θ : ℝ) in 0..2 * π, y = (2 * π) • y := by simp,
  rw [← this, ← interval_integral.integral_sub],
  { have : ∀ x : ℝ, ∥f (r * exp (x * I)) - y∥ ≤ ε / (2 * π),
    { intro x, rw ← dist_eq_norm,
      exact (hδ _ (diff_subset_diff_left (closed_ball_subset_closed_ball hrδ) (hmem x))).le },
    refine (interval_integral.norm_integral_le_of_norm_le_const (λ x _, this x)).trans_eq _,
    simp [real.two_pi_pos.ne', _root_.abs_of_nonneg real.two_pi_pos.le] },
  { refine continuous.interval_integrable _ _ _,
    have : continuous_on f (closed_ball 0 R \ {0}),
    { intros z hz, by_cases hzs : z ∈ s,
      exacts [hc z hzs, (hd z ⟨hz, hzs⟩).continuous_within_at] },
    refine this.comp_continuous _ _,
    { continuity },
    { exact λ y, ⟨closed_ball_subset_closed_ball hrR (hmem y).1, (hmem y).2⟩ } },
  { simp [interval_integrable, measure_lt_top] }
end

lemma integral_circle_darg_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {s : set ℂ} (hs : countable s) (hc : ∀ x ∈ s, continuous_within_at f (closed_ball 0 R) x)
  (hd : ∀ z ∈ closed_ball (0 : ℂ) R \ s, differentiable_within_at ℂ f (closed_ball 0 R) z) :
  ∫ (θ : ℝ) in 0..2 * π, f (R * exp (θ * I)) = (2 * π) • f 0 :=
begin
  rcases h0.eq_or_lt with (rfl|h0), { simp },
  refine integral_circle_darg_of_differentiable_on_off_countable_of_tendsto h0 hs
    (λ z hz, (hc z hz).mono $ diff_subset _ _)
    (λ z hz, (hd z ⟨hz.1.1, hz.2⟩).mono $ diff_subset _ _) _,
  suffices : continuous_within_at f (closed_ball 0 R) 0,
    from (this.continuous_at (closed_ball_mem_nhds _ h0)).continuous_within_at,
  by_cases h : (0 : ℂ) ∈ s,
  exacts [hc _ h, (hd _ ⟨mem_closed_ball_self h0.le, h⟩).continuous_within_at]
end

lemma integral_circle_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {s : set ℂ} (hs : countable s) (hc : ∀ x ∈ s, continuous_within_at f (closed_ball 0 R) x)
  (hd : ∀ z ∈ closed_ball (0 : ℂ) R \ s, differentiable_within_at ℂ f (closed_ball 0 R) z) :
  ∫ (θ : ℝ) in 0..2 * π, (R * exp (θ * I) * I : ℂ) • f (R * exp (θ * I)) = 0 :=
by simpa [mul_smul, smul_comm _ I, interval_integral.integral_smul, I_ne_zero]
  using integral_circle_darg_of_differentiable_on_off_countable h0 hs
    (λ z hz, continuous_within_at_id.smul (hc z hz))
    (λ z hz, differentiable_within_at_id.smul (hd z hz))

open_locale complex_order

lemma abs_eq_and_im_eq_iff {y R : ℝ} {z : ℂ} :
  abs z = R ∧ z.im = y ↔
    |y| ≤ R ∧ (z = -real.sqrt (R ^ 2 - y ^ 2) + y * I ∨ z = real.sqrt (R ^ 2 - y ^ 2) + y * I) :=
begin
  split,
  { rintro ⟨rfl, rfl⟩, use abs_im_le_abs z,
    have : z.re = -|z.re| ∨ z.re = |z.re|,
      from ((abs_eq $ _root_.abs_nonneg z.re).1 rfl).symm,
    simpa [complex.ext_iff, real.sqrt_sq_eq_abs] },
  { refine and_imp.2 (λ hy, _),
    have hR : 0 ≤ R := (_root_.abs_nonneg y).trans hy,
    have hyR : 0 ≤ R ^ 2 - y ^ 2,
      from sub_nonneg.2 (sq_le_sq $ (_root_.abs_of_nonneg hR).symm ▸ hy),
    rintro (rfl|rfl); simp only [← of_real_neg, abs, ← mk_eq_add_mul_I, norm_sq_mk, ← sq,
      neg_pow_bit0, real.sq_sqrt, real.sqrt_sq, sub_add_cancel, eq_self_iff_true, true_and, *] }
end

lemma mem_Ioo_of_abs_lt {z : ℂ} {R : ℝ} (h : abs z < R) :
  z ∈ (Ioo (- real.sqrt (R ^ 2 - z.im ^ 2) + z.im * I)
    (real.sqrt (R ^ 2 - z.im ^ 2) + z.im * I) : set ℂ) :=
begin
  simp only [mem_Ioo, lt_def, ← of_real_neg, ← mk_eq_add_mul_I, eq_self_iff_true, and_true,
    ← abs_lt],
  apply real.lt_sqrt_of_sq_lt,
  rwa [lt_sub_iff_add_lt, _root_.sq_abs, sq, sq, ← real.sqrt_lt_sqrt_iff, real.sqrt_sq],
  exacts [(abs_nonneg z).trans h.le, norm_sq_nonneg z]
end

lemma exists_mul_exp_mul_I_le_iff {z : ℂ} {R : ℝ} (hlt : abs z < R) :
  ∃ θ₀ ∈ Ioc (-π) π, ↑R * exp (↑θ₀ * I) < z ∧ ∀ θ ∈ Ioc (-π) π, ↑R * exp (↑θ * I) ≤ z → θ = θ₀ :=
begin
  generalize hw : (-real.sqrt (R ^ 2 - z.im ^ 2) + z.im * I : ℂ) = w,
  generalize hθ₀ : arg w = θ₀,
  refine ⟨θ₀, hθ₀ ▸ arg_mem_Ioc w, _, λ θ hθπ hθz, _⟩,
  { suffices : abs w = R,
    { convert (mem_Ioo_of_abs_lt hlt).1,
      rw [hw, ← abs_mul_exp_arg_mul_I w, hθ₀, this] },
    exact (abs_eq_and_im_eq_iff.2 ⟨z.abs_im_le_abs.trans hlt.le, or.inl hw.symm⟩).1 },
  { have hR : 0 < R, from (abs_nonneg z).trans_lt hlt,
    have habs : abs (R * exp (θ * I)) = R, by simp [_root_.abs_of_nonneg hR.le],
    have : ↑R * exp (θ * I) = w := hw ▸ (abs_eq_and_im_eq_iff.1 ⟨habs, hθz.2⟩).2.resolve_right
      (hθz.trans_lt (mem_Ioo_of_abs_lt hlt).2).ne,
    apply_fun arg at this,
    rwa [arg_real_mul _ hR, exp_mul_I, arg_cos_add_sin_mul_I hθπ, hθ₀] at this }
end

lemma integral_circle_zpow_sub_of_abs_lt {R : ℝ} {w : ℂ} (hw : abs w < R) {n : ℤ} (hn : n ≠ -1) :
  ∫ θ : ℝ in 0..2 * π, ↑R * exp (θ * I) * I * (R * exp (θ * I) - w) ^ n = 0 :=
begin
  have hR0 : 0 < R := (abs_nonneg w).trans_lt hw,
  have h0 : ∀ θ : ℝ, ↑R * exp (θ * I) - w ≠ 0,
  { refine λ θ, sub_ne_zero.2 (λ h₀, _),
    simpa [h₀.symm, _root_.abs_of_nonneg hR0.le] using hw },
  set f : ℝ → ℂ := λ θ, R * exp (θ * I) * I * (R * exp (θ * I) - w) ^ n,
  set F : ℝ → ℂ := λ θ, (R * exp (θ * I) - w) ^ (n + 1) / (n + 1),
  have : ∀ θ, has_deriv_at F (f θ) θ,
  { intro θ, simp only [F, div_eq_mul_inv],
    convert (((has_deriv_at_zpow (n + 1) _
      (or.inl $ h0 θ)).has_fderiv_at.restrict_scalars ℝ).comp_has_deriv_at θ
      (((of_real_clm.has_deriv_at.mul_const I).cexp_real.const_mul ↑R).sub_const w)).mul_const _,
    have : (n + 1 : ℂ) ≠ 0, by exact_mod_cast mt eq_neg_iff_add_eq_zero.2 hn,
    field_simp [f, this], ac_refl },
  have hfc : continuous f,
  { have : continuous (λ θ : ℝ, ↑R * exp (θ * I)) :=
      continuous_const.mul (continuous_of_real.mul continuous_const).cexp,
    exact (this.mul continuous_const).mul ((this.sub continuous_const).zpow _
      (λ θ, or.inl (h0 θ))) },
  calc ∫ θ in 0 .. 2 * π, f θ = F (2 * π) - F 0 :
    interval_integral.integral_eq_sub_of_has_deriv_at (λ θ _, this θ) (hfc.interval_integrable _ _)
  ... = 0 : by { simp only [F], simp }
end

def cauchy_power_series (f : ℝ → E) (R : ℝ) :
  formal_multilinear_series ℂ ℂ E :=
λ n, continuous_multilinear_map.mk_pi_field ℂ _ $
  ∫ θ : ℝ in 0..2*π, (↑R * exp (θ * I))⁻¹ ^ n • f θ

lemma cauchy_power_series_apply (f : ℝ → E) (R : ℝ) (n : ℕ) (z : ℂ) :
  cauchy_power_series f R n (λ _, z) =
    ∫ θ : ℝ in 0..2*π, (z / (R * exp (θ * I))) ^ n • f θ :=
by simp only [cauchy_power_series, continuous_multilinear_map.mk_pi_field_apply, fin.prod_const,
  ← interval_integral.integral_smul, div_eq_mul_inv, mul_pow, smul_smul]

lemma cauchy_power_series_partial_sum {f : ℝ → E} (hf : interval_integrable f volume 0 (2 * π))
  {z : ℂ} {R : ℝ} (hz : abs z ≠ |R|) (n : ℕ) :
  (cauchy_power_series f R).partial_sum n z =
    ∫ θ : ℝ in 0..2*π,
      (((z / (R * exp (θ * I))) ^ n - 1) / (z / (R * exp (θ * I)) - 1)) • f θ :=
begin
  simp only [formal_multilinear_series.partial_sum, cauchy_power_series_apply],
  rw [← interval_integral.integral_finset_sum],
  { have : ∀ θ : ℝ, z / (R * exp (θ * I)) ≠ 1,
    { refine λ θ hθ, hz _, simp [eq_of_div_eq_one hθ] },
    simp only [← finset.sum_smul, ← geom_sum_def, geom_sum_eq (this _)] },
  { rintro n -,
    rw interval_integrable_iff at hf ⊢,
    refine (hf.norm.const_mul ((abs z / |R|) ^ n)).mono' _ _,
    { exact ((((measurable_of_real.mul_const _).cexp.const_mul _).const_div _).pow_const
        _).ae_measurable.smul hf.ae_measurable },
    { simp [norm_smul] } }
end

lemma norm_cauchy_power_series_le (f : ℝ → E) (R : ℝ) (n : ℕ) :
  ∥cauchy_power_series f R n∥ ≤ (∫ θ : ℝ in 0..2*π, ∥f θ∥) * (|R|⁻¹) ^ n :=
begin
  simp only [cauchy_power_series, continuous_multilinear_map.norm_mk_pi_field],
  refine (interval_integral.norm_integral_le_integral_norm real.two_pi_pos.le).trans_eq _,
  conv_rhs { rw [mul_comm, ← interval_integral.integral_const_mul] },
  simp only [norm_smul, abs_of_real, mul_one, abs_mul, abs_exp_mul_I, abs_inv, abs_pow, norm_eq_abs]
end

lemma le_radius_cauchy_power_series (f : ℝ → E) (R : ℝ≥0) :
  ↑R ≤ (cauchy_power_series f R).radius :=
begin
  refine (cauchy_power_series f R).le_radius_of_bound (∫ θ : ℝ in 0..2*π, ∥f θ∥) (λ n, _),
  refine (mul_le_mul_of_nonneg_right (norm_cauchy_power_series_le _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans _,
  rw [_root_.abs_of_nonneg R.coe_nonneg],
  cases eq_or_ne (R ^ n : ℝ) 0 with hR hR,
  { rw [hR, mul_zero],
    exact interval_integral.integral_nonneg real.two_pi_pos.le (λ _ _, norm_nonneg _) },
  { rw [inv_pow₀, inv_mul_cancel_right₀ hR] }
end

lemma sum_cauchy_power_series_eq_integral {f : ℝ → E} {R : ℝ} {z : ℂ}
  (hf : interval_integrable f volume 0 (2 * π)) (hR : abs z < R) :
  (cauchy_power_series f R).sum z = ∫ θ : ℝ in 0..2*π, (↑R * exp (θ * I) - z)⁻¹ • f θ :=
begin
  have hR0 : 0 < R := (abs_nonneg z).trans_lt hR,
  have hz_ball : z ∈ emetric.ball (0 : ℂ) (cauchy_power_series f R).radius,
  { lift R to ℝ≥0 using hR0.le,
    refine mem_emetric_ball_zero_iff.2 (lt_of_lt_of_le _ $ le_radius_cauchy_power_series f R),
    rwa ennreal.coe_lt_coe },
  have := ((cauchy_power_series f R).has_sum hz_ball).tendsto_sum_nat,
end

/-

lemma has_deriv_at_integral_of_dominated_loc_of_deriv_le {F : 𝕜 → α → E} {F' : 𝕜 → α → E} {x₀ : 𝕜}
  {a b : α} {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) (μ.restrict (Ι a b)))
  (hF_int : interval_integrable (F x₀) μ a b)
  (hF'_meas : ae_measurable (F' x₀) (μ.restrict (Ι a b)))
  {bound : α → ℝ}
  (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ∥F' x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x t) (F' x t) x) :
  (interval_integrable (F' x₀) μ a b) ∧
    has_deriv_at (λ x, ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ :=
-/

lemma has_deriv_at_integral_circle_div_sub_of_abs_lt {R : ℝ} {w₀ : ℂ} (hw : abs w₀ < R) :
  has_deriv_at (λ w, ∫ θ : ℝ in 0..2 * π, (↑R * exp (θ * I) * I / (R * exp (θ * I) - w))) 0 w₀ :=
begin
  have hR : 0 < R := (abs_nonneg w₀).trans_lt hw,
  simp only [div_eq_mul_inv, ← zpow_neg_one],
  set F : ℂ → ℝ → ℂ := λ w θ, R * exp (θ * I) * I * (R * exp (θ * I) - w) ^ (-1 : ℤ),
  set F' : ℂ → ℝ → ℂ := λ w θ, R * exp (θ * I) * I * (R * exp (θ * I) - w) ^ (-2 : ℤ),
  set ε := (R - abs w₀) / 2,
  have ε_pos : 0 < ε := half_pos (sub_pos.2 hw),
  have habs : ∀ θ : ℝ, abs (R * exp (θ * I)) = R,
  { intro θ, simp [_root_.abs_of_nonneg hR.le, abs_exp] },
  have habs_lt : ∀ w ∈ ball w₀ ε, abs w < abs w₀ + ε,
  { intros w hw,
    rw [mem_ball, dist_eq] at hw,
    calc abs w = abs (w₀ + (w - w₀)) : by rw add_sub_cancel'_right
    ... ≤ abs w₀ + abs (w - w₀) : abs_add _ _
    ... < abs w₀ + ε : add_lt_add_left hw _ },
  have habs_denom : ∀ (w ∈ ball w₀ ε) (θ : ℝ), ε < abs (R * exp (θ * I) - w),
  { intros w hw θ,
    calc ε = abs (R * exp (θ * I)) - (abs w₀ + ε) : by field_simp [ε, habs, mul_two]
       ... < abs (R * exp (θ * I)) - abs w        : sub_lt_sub_left (habs_lt w hw) _
       ... ≤ abs (R * exp (θ * I) - w)            : norm_sub_norm_le (↑R * exp (θ * I)) w },
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ (w ∈ ball w₀ ε) θ, ∥F' w θ∥ ≤ C,
  { refine ⟨R * ε ^ (-2 : ℤ), λ w hw θ, _⟩,
    simp only [F', norm_eq_abs, abs_mul, habs, abs_I, abs_zpow], }
end

lemma integral_circle_div_sub_of_abs_lt {R : ℝ} {w : ℂ} (hw : abs w < R) :
  ∫ θ : ℝ in 0..2 * π, (↑R * exp (θ * I) * I / (R * exp (θ * I) - w)) = 2 • π • I :=
begin
  
end

lemma integral_circle_div_sub_of_abs_lt {R : ℝ} {w : ℂ} (hw : abs w < R) :
  ∫ θ : ℝ in 0..2 * π, (R * exp (θ * I) * I / (R * exp (θ * I) - w) : ℂ) = 2 • π • I :=
begin
  have hR0 : 0 < R := (abs_nonneg w).trans_lt hw,
  have hwimR : w.im / R ∈ Ioo (-1 : ℝ) 1,
  { rw [mem_Ioo, ← abs_lt, _root_.abs_div, div_lt_one],
    exacts [(abs_im_le_abs _).trans_lt (hw.trans_le (le_abs_self _)),
      hR0.trans_le (le_abs_self R)] },
  set f : ℝ → ℂ := λ θ, R * exp (θ * I) * I / (R * exp (θ * I) - w),
  have hfπ : periodic f (2 * π),
  { intro x, simp only [f], simp [add_mul, of_real_add, exp_periodic _] },
  have hd : ∀ θ : ℝ, has_deriv_at (λ θ : ℝ, ↑R * exp (θ * I)) (R * exp (θ * I) * I) θ,
  { simpa [mul_assoc] using λ _, (of_real_clm.has_deriv_at.mul_const I).cexp_real.const_mul ↑R },
  have hfc : continuous f,
  { have : continuous (λ θ : ℝ, ↑R * exp (θ * I)),
      from continuous_iff_continuous_at.2 (λ θ, (hd θ).continuous_at),
    refine (this.mul continuous_const).div (this.sub continuous_const) (λ hθ, _),
    rw sub_ne_zero, rintro rfl, simpa [abs_exp, (le_abs_self R).not_lt] using hw },
  obtain ⟨θ₀, hθ₀π, hlt, hθ₀⟩ := exists_mul_exp_mul_I_le_iff hw,
  rw ← sub_lt_zero at hlt,
  set F : ℝ → ℂ := λ θ, log (R * exp (θ * I) - w),
  have Hd : ∀ θ ∈ Ioo θ₀ (θ₀ + 2 * π), has_deriv_at F (f θ) θ,
  { rintro θ ⟨hθ₁, hθ₂⟩,
    refine ((hd θ).sub_const w).clog_real (not_le_zero_iff.1 (λ hle, _)),
    rw sub_nonpos at hle,
    cases le_or_lt θ π with hθπ hθπ,
    { exact hθ₁.ne' (hθ₀ _ ⟨hθ₀π.1.trans hθ₁, hθπ⟩ hle) },
    { refine (sub_lt_iff_lt_add.2 hθ₂).ne (hθ₀ _ _ _),
      { cases hθ₀π, split; linarith },
      { simpa [sub_mul, exp_periodic.sub_eq] } } },
  replace hd := λ θ, (hd θ).sub_const w,
  have hd₀ : im (R * exp (θ₀ * I) * I) < 0,
  {  },
  have Hlim₁ : tendsto F (𝓝[Ioi θ₀] θ₀) (𝓝 $ real.log (abs $ R • exp (θ₀ * I) - w) - π * I),
  { refine (tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero hlt.1 hlt.2).comp
      (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
        (hd _).continuous_at.continuous_within_at _),
    
 },
  have Hlim₂ : tendsto F (𝓝[Iio (θ₀ + 2 * π)] (θ₀ + 2 * π))
    (𝓝 $ real.log (abs $ R • exp (θ₀ * I) - w) + π * I),
  { sorry },
  calc ∫ θ in 0..2 * π, f θ = ∫ θ in 0..0 + 2 * π, f θ : by rw zero_add
  ... = ∫ θ in θ₀..θ₀ + 2 * π, f θ : hfπ.interval_integral_add_eq _ _
  ... = 2 • π • I :
    begin
      rw integral_eq_sub_of_has_deriv_at_of_tendsto (by simp [real.pi_pos]) Hd
        (hfc.interval_integrable _ _) Hlim₁ Hlim₂,
      simp [two_mul]
    end
end

lemma integral_circle_div_sub_of_differentiable_on {R : ℝ} {w : ℂ} (hw : abs w < R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball 0 R)) :
  ∫ (θ : ℝ) in 0..2 * π, ((R * exp (θ * I) * I) / (R * exp (θ * I) - w) : ℂ) • f (R * exp (θ * I)) =
    2 • π • I • f w :=
begin
  set F : ℂ → E := update (λ z, (z - w)⁻¹ • (f z - f w)) w (deriv f w),
  set s : set ℂ := {w},
  have hnhds : closed_ball (0 : ℂ) R ∈ 𝓝 w,
    from _root_.mem_nhds_iff.2 ⟨ball 0 R, ball_subset_closed_ball, is_open_ball, by simpa⟩,
  have hc : ∀ z ∈ s, continuous_within_at F (closed_ball 0 R) z,
  { rintro z (rfl|_),
    have := has_deriv_at_iff_tendsto_slope.1 (hd.has_deriv_at hnhds),
    rw [← continuous_within_at_diff_self, continuous_within_at],
    simp only [F, update_same],
    refine (this.congr' _).mono_left (nhds_within_mono _ (inter_subset_right _ _)),
    filter_upwards [self_mem_nhds_within] (λ z hz, (update_noteq hz _ _).symm) },
  have hd : ∀ z ∈ closed_ball (0 : ℂ) R \ s, differentiable_within_at ℂ F (closed_ball 0 R) z,
  { rintro z ⟨hzR, hzw : z ≠ w⟩,
    refine (((differentiable_within_at_id.sub_const w).inv $ sub_ne_zero.2 hzw).smul
      ((hd z hzR).sub_const (f w))).congr_of_eventually_eq _ _,
    { filter_upwards [mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds hzw)],
      exact λ x hx, update_noteq hx _ _ },
    { exact update_noteq hzw _ _ } },
  have HI := integral_circle_eq_zero_of_differentiable_on_off_countable ((abs_nonneg w).trans hw.le)
    (countable_singleton w) hc hd,
  have hF : ∀ θ : ℝ, F (↑R * exp (θ * I)) = (↑R * exp (θ * I) - w)⁻¹ • (f (R * exp (θ * I)) - f w),
  { refine λ θ, update_noteq _ _ _,
    rintro rfl, simpa [abs_exp, (le_abs_self R).not_lt] using hw },
  simp only [hF, smul_sub, div_eq_mul_inv, mul_smul] at HI ⊢,
  rw [interval_integral.integral_sub, sub_eq_zero] at HI,
  { refine HI.trans _,
    -- integral_eq_sub_of_has_deriv_at_of_le

 },
  { }
end

/-
lemma integral_circle_eq_zero_of_differentiable_on {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  (hd : differentiable_on ℂ f (closed_ball 0 R)) :
  ∫ (θ : ℝ) in 0..2 * π, (R * exp (θ * I) * I : ℂ) • f (R * exp (θ * I)) = 0 :=
by simpa [mul_smul, smul_comm _ I, interval_integral.integral_smul, I_ne_zero]
  using integral_circle_darg_of_differentiable_on h0 (differentiable_on_id.smul hd)
-/
/-
lemma integral_unit_circle_div_sub_of_differentiable_on {w : ℂ} (h : abs w < 1)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball (0 : ℂ) 1)) :
  ∫ (θ : ℝ) in 0..2 * π, ((exp (θ * I) * I) / (exp (θ * I) - w) : ℂ) •
    f (exp (θ * I)) = 2 • π • I • f w :=
begin
  set R : ℂ → ℂ := λ z, (z + w) / (conj w * z + 1),
  set D := closed_ball (0 : ℂ) 1,
  have Hdenom : ∀ z ∈ D, conj w * z + 1 ≠ 0,
  { intros z hz h0,
    rw [mem_closed_ball_iff_norm, sub_zero, norm_eq_abs] at hz,
    have : abs (conj w * z) < 1,
    { rw [abs_mul, abs_conj, mul_comm, ← one_mul (1 : ℝ)],
      exact mul_lt_mul' hz h (abs_nonneg _) zero_lt_one },
    rw [eq_neg_of_add_eq_zero h0, abs_neg, abs_one] at this,
    exact this.false },
  have Hd : ∀ z ∈ D, has_deriv_at R ((1 - w * conj w) / (conj w * z + 1) ^ 2) z,
  { intros z hz,
    have := ((has_deriv_at_id z).add_const w).div
      (((has_deriv_at_id z).const_mul (conj w)).add_const 1) (Hdenom z hz),
    simpa [add_mul, mul_comm z] using this },
  have H_norm_sq_sub :
    norm_sq (conj w * z + 1) - norm_sq (z + w) = (1 - norm_sq z) * (1 - norm_sq w),
  { simp, },
  have Hmaps : maps_to R D D,
  { intros z hz,
    simp only [mem_closed_ball, abs_div, dist_zero_right, norm_eq_abs] at hz ⊢,
    refine div_le_one_of_le (real.sqrt_le_sqrt _) (abs_nonneg _),
    rw [norm_sq_add, norm_sq_add, norm_sq.map_mul, norm_sq_conj, norm_sq.map_one, conj_one, mul_one,
      mul_comm z, ← sub_nonneg],
    convert_to 0 ≤ (1 - norm_sq z) * (1 - norm_sq w), { abel },
     }
  
end
-/

end complex

