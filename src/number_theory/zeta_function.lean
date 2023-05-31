/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.special_functions.gamma.beta
import number_theory.modular_forms.jacobi_theta

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemann_zeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `riemann_completed_zeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `riemann_completed_zeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points (which are not arbitrary, but
I haven't checked exactly what they are).

## Main results:

* `differentiable_completed_zeta₀` : the function `Λ₀(s)` is entire.
* `differentiable_at_completed_zeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiable_at_riemann_zeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_of_one_lt_re` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.

## Outline of proofs:

We define two related functions on the reals, `zeta_kernel₁` and `zeta_kernel₂`. The first is
`(θ (t * I) - 1) / 2`, where `θ` is Jacobi's theta function; its Mellin transform is exactly the
completed zeta function. The second is obtained by subtracting a linear combination of powers on
the interval `Ioc 0 1` to give a function with exponential decay at both `0` and `∞`. We then define
`riemann_completed_zeta₀` as the Mellin transform of the second zeta kernel, and define
`riemann_completed_zeta` and `riemann_zeta` from this.
-/

open measure_theory set filter asymptotics topological_space real asymptotics
open complex (hiding exp norm_eq_abs abs_of_nonneg abs_two continuous_exp)

open_locale topology real

noncomputable theory

/-!
## Definition of the Riemann zeta function and related functions
-/

/-- Function whose Mellin transform is `π ^ (-s) * Γ(s) * zeta (2 * s)`, for `1 / 2 < Re s`. -/
def zeta_kernel₁ (t : ℝ) : ℂ := ∑' (n : ℕ), rexp (-π * t * (n + 1) ^ 2)

/-- Modified zeta kernel, whose Mellin transform is entire. --/
def zeta_kernel₂ : ℝ → ℂ := zeta_kernel₁ + indicator (Ioc 0 1) (λ t, (1 - 1 / sqrt t) / 2)

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def riemann_completed_zeta₀ (s : ℂ) : ℂ := mellin zeta_kernel₂ (s / 2)

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
def riemann_completed_zeta (s : ℂ) : ℂ := riemann_completed_zeta₀ s - 1 / s + 1 / (s - 1)

/-- The Riemann zeta function `ζ(s)`. We set this to be irreducible to hide messy implementation
details. -/
@[irreducible] def riemann_zeta := function.update
  (λ s : ℂ, ↑π ^ (s / 2) * riemann_completed_zeta s / Gamma (s / 2)) 0 (-1 / 2)

/- Note the next lemma is true by definition; what's hard is to show that with this definition, `ζ`
is continuous (and indeed analytic) at 0, see `differentiable_riemann_zeta` below. -/
/-- We have `ζ(0) = -1 / 2`. -/
lemma riemann_zeta_zero : riemann_zeta 0 = -1 / 2 :=
begin
  unfold riemann_zeta,
  exact function.update_same _ _ _
end

/-!
## First properties of the zeta kernels
-/

/-- The sum defining `zeta_kernel₁` is convergent. -/
lemma summable_exp_neg_pi_mul_nat_sq {t : ℝ} (ht : 0 < t) :
  summable (λ n : ℕ, rexp (-π * t * (n + 1) ^ 2)) :=
begin
  have : 0 < (↑t * I).im, by rwa [of_real_mul_im, I_im, mul_one],
  convert summable_norm_iff.mpr (has_sum_nat_jacobi_theta this).summable,
  ext1 n,
  rw [complex.norm_eq_abs, complex.abs_exp],
  rw show ↑π * I * (↑n + 1) ^ 2 * (↑t * I) = ↑(π * t * (n + 1) ^ 2) * I ^ 2, by { push_cast, ring },
  rw [I_sq, mul_neg_one, ←of_real_neg, of_real_re, neg_mul, neg_mul],
end

/-- Relate `zeta_kernel₁` to the Jacobi theta function on `ℍ`. (We don't use this as the definition
of `zeta_kernel₁`, since the sum over `ℕ` rather than `ℤ` is more convenient for relating zeta to
the Dirichlet series for `re s > 1`.) -/
lemma zeta_kernel₁_eq_jacobi_theta {t : ℝ} (ht : 0 < t) :
  zeta_kernel₁ t = (jacobi_theta (t * I) - 1) / 2 :=
begin
  rw [jacobi_theta_eq_tsum_nat ((mul_I_im t).symm ▸ ht : 0 < (↑t * I).im), add_comm, add_sub_cancel,
    mul_div_cancel_left _ (two_ne_zero' ℂ), zeta_kernel₁],
  congr' 1 with n : 1,
  push_cast,
  rw [(by ring : ↑π * I * (n + 1) ^ 2 * (t * I) = I ^ 2 * π * t * (n + 1) ^ 2), I_sq, neg_one_mul],
end

/-- Continuity of `zeta_kernel₁`. -/
lemma continuous_at_zeta_kernel₁ {t : ℝ} (ht : 0 < t) : continuous_at zeta_kernel₁ t :=
begin
  have : continuous_at (λ u : ℝ, (jacobi_theta (u * I) - 1) / 2) t,
  { refine (continuous_at.sub _ continuous_at_const).div_const _,
    refine (continuous_at_jacobi_theta _).comp (continuous_at.mul _ continuous_at_const),
    { rwa [mul_I_im, of_real_re] },
    { exact continuous_of_real.continuous_at } },
  refine this.congr (eventually_of_mem (Ioi_mem_nhds ht) (λ u hu, _)),
  rw zeta_kernel₁_eq_jacobi_theta hu,
end

/-- Local integrability of `zeta_kernel₁`. -/
lemma locally_integrable_zeta_kernel₁ : locally_integrable_on zeta_kernel₁ (Ioi 0) :=
(continuous_at.continuous_on $ λ t ht, continuous_at_zeta_kernel₁ ht).locally_integrable_on
  measurable_set_Ioi

/-- Local integrability of `zeta_kernel₂`. -/
lemma locally_integrable_zeta_kernel₂ : locally_integrable_on zeta_kernel₂ (Ioi 0) :=
begin
  refine (locally_integrable_on_iff (or.inr is_open_Ioi)).mpr (λ k hk hk', integrable.add _ _),
  { refine continuous_on.integrable_on_compact hk' _,
    exact continuous_at.continuous_on (λ x hx, continuous_at_zeta_kernel₁ (hk hx)) },
  { refine (integrable_indicator_iff measurable_set_Ioc).mpr _,
    rw [integrable_on, measure.restrict_restrict, ←integrable_on],
    swap, { exact measurable_set_Ioc },
    apply continuous_on.integrable_on_compact,
    { convert (is_compact_Icc : is_compact $ Icc 0 1).inter hk' using 1,
      exact set.ext (λ t, ⟨λ h, ⟨Ioc_subset_Icc_self h.1, h.2⟩, λ h, ⟨⟨hk h.2, h.1.2⟩, h.2⟩⟩) },
    { refine continuous_on.mono _ ((inter_subset_right _ _).trans hk),
      refine (continuous_on_const.sub _).div_const _,
      refine continuous_on.div continuous_on_const _ (λ x hx, _),
      { exact (continuous_of_real.comp continuous_sqrt).continuous_on },
      exact of_real_ne_zero.mpr (sqrt_ne_zero'.mpr hx) } }
end

/-- Functional equation for `zeta_kernel₂`. -/
lemma zeta_kernel₂_one_div {t : ℝ} (ht : 0 < t) :
  zeta_kernel₂ (1 / t) = sqrt t * zeta_kernel₂ t :=
begin
  have aux : ∀ {u : ℝ} (hu : 1 < u), zeta_kernel₂ (1 / u) = sqrt u * zeta_kernel₂ u,
  { intros u hu,
    simp_rw [zeta_kernel₂, pi.add_apply],
    rw [indicator_of_mem, indicator_of_not_mem (not_mem_Ioc_of_gt hu), add_zero],
    swap, { exact ⟨one_div_pos.mpr (zero_lt_one.trans hu), (one_div u).symm ▸ (inv_le_one hu.le)⟩ },
    rw [zeta_kernel₁_eq_jacobi_theta (one_div_pos.mpr $ zero_lt_one.trans hu),
      zeta_kernel₁_eq_jacobi_theta (zero_lt_one.trans hu), ←add_div, ←mul_div_assoc, add_sub,
      sub_add_cancel, sqrt_div zero_le_one, sqrt_one, one_div (sqrt _), of_real_inv,
      ←one_div, one_div_one_div, mul_sub, mul_one],
    congr' 2,
    let τ : upper_half_plane := ⟨u * I, (mul_I_im u).symm ▸ (zero_lt_one.trans hu)⟩,
    convert jacobi_theta_S_smul τ using 2,
    { rw [upper_half_plane.modular_S_smul, upper_half_plane.coe_mk, subtype.coe_mk, ←neg_inv,
        mul_inv, inv_I, mul_neg, neg_neg, one_div, of_real_inv], },
    { rw [subtype.coe_mk, mul_comm, mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one,
        sqrt_eq_rpow, of_real_cpow (zero_lt_one.trans hu).le],
      push_cast } },
  rcases lt_trichotomy 1 t with h | rfl | h,
  { exact aux h },
  { simp only [div_self, ne.def, one_ne_zero, not_false_iff, sqrt_one, of_real_one, one_mul], },
  { have := aux (show 1 < 1 / t, by rwa [lt_one_div (zero_lt_one' ℝ) ht, div_one]),
    rw one_div_one_div at this,
    rw [this, ←mul_assoc, ←of_real_mul, ←sqrt_mul ht.le, mul_one_div_cancel ht.ne', sqrt_one,
      of_real_one, one_mul] },
end

/-!
## Bounds for zeta kernels

We now establish asymptotic bounds for the zeta kernels as `t → ∞` and `t → 0`, and use these to
show holomorphy of their Mellin transforms (for `1 / 2 < re s` for `zeta_kernel₁`, and all `s` for
`zeta_kernel₂`). -/

/-- Bound for `zeta_kernel₁` for large `t`. -/
lemma is_O_at_top_zeta_kernel₁ : is_O at_top zeta_kernel₁ (λ t, exp (-π * t)) :=
begin
  have h := (is_O_at_im_infty_jacobi_theta_sub_one).const_mul_left (1 / 2),
  simp_rw [(mul_comm (1 / 2 : ℂ) _), mul_one_div] at h,
  have h' : tendsto (λ t : ℝ, ↑t * I) at_top (comap im at_top),
  { rw tendsto_comap_iff,
    convert tendsto_id,
    ext1 t,
    rw [function.comp_app, mul_I_im, of_real_re, id.def] },
  convert ((h.norm_left.comp_tendsto h').congr' (eventually_of_mem (Ioi_mem_at_top 0) (λ t ht, _))
    (eventually_of_mem (Ioi_mem_at_top 0) (λ t ht, _))).of_norm_left,
  { rw [function.comp_app, ←zeta_kernel₁_eq_jacobi_theta ht] },
  { rw [function.comp_app, mul_I_im, of_real_re] }
end

/-- Bound for `zeta_kernel₂` for large `t`. -/
lemma is_O_at_top_zeta_kernel₂ : is_O at_top zeta_kernel₂ (λ t, exp (-π * t)) :=
begin
  refine (eventually_eq_of_mem (Ioi_mem_at_top (1 : ℝ)) (λ t ht, _)).trans_is_O
    is_O_at_top_zeta_kernel₁,
  rw [zeta_kernel₂, pi.add_apply, indicator_of_not_mem (not_mem_Ioc_of_gt ht), add_zero],
end

/-- Precise but awkward-to-use bound for `zeta_kernel₂` for `t → 0`. -/
lemma is_O_zero_zeta_kernel₂ : is_O (𝓝[>] 0) zeta_kernel₂ (λ t, exp (-π / t) / sqrt t) :=
begin
  have h1 := (is_O_at_top_zeta_kernel₂).comp_tendsto tendsto_inv_zero_at_top,
  simp_rw ←one_div at h1,
  have h2 : (zeta_kernel₂ ∘ has_div.div 1) =ᶠ[𝓝[>] 0] λ t, sqrt t * zeta_kernel₂ t,
    from eventually_of_mem self_mem_nhds_within (λ t ht, by simp_rw ←zeta_kernel₂_one_div ht),
  have h3 := (h1.congr' h2 (eventually_eq.refl _ _)),
  have h4 := h3.mul (is_O_refl (λ t : ℝ, 1 / (sqrt t : ℂ)) (𝓝[>] 0)).norm_right,
  refine h4.congr' _ _,
  { refine eventually_of_mem self_mem_nhds_within (λ x hx, _),
    simp_rw [←mul_assoc],
    rw [mul_comm, ←mul_assoc, one_div_mul_cancel, one_mul],
    exact of_real_ne_zero.mpr ((sqrt_ne_zero $ le_of_lt hx).mpr (ne_of_gt hx)) },
  { refine eventually_of_mem self_mem_nhds_within (λ x hx, _),
    dsimp only,
    rw [function.comp_app, mul_one_div, one_div (↑(sqrt _)), ←of_real_inv, is_R_or_C.norm_of_real,
      abs_inv, abs_of_nonneg (sqrt_nonneg _), ←div_eq_mul_inv] },
end

/-- Weaker but more usable bound for `zeta_kernel₂` for `t → 0`. -/
lemma is_O_zero_zeta_kernel₂_rpow (a : ℝ) : is_O (𝓝[>] 0) zeta_kernel₂ (λ t, t ^ a) :=
begin
  have aux1 : is_O at_top (λ t, exp (-π * t)) (λ t, t ^ (-a - 1 / 2)),
    from (is_o_exp_neg_mul_rpow_at_top pi_pos _).is_O,
  have aux2 : is_O at_top (λ t, exp (-π * t) * sqrt t) (λ t, t ^ (-a)),
  { refine (aux1.mul (is_O_refl sqrt _)).congr' (eventually_eq.refl _ _) _,
    refine (eventually_gt_at_top 0).mp (eventually_of_forall (λ t ht, _)),
    simp_rw [sqrt_eq_rpow, ←rpow_add ht, sub_add_cancel] },
  refine is_O_zero_zeta_kernel₂.trans ((aux2.comp_tendsto tendsto_inv_zero_at_top).congr' _ _),
  { refine eventually_of_mem self_mem_nhds_within (λ x hx, _),
    simp_rw [function.comp_app, sqrt_inv, ←div_eq_mul_inv] },
  { refine eventually_of_mem self_mem_nhds_within (λ x hx, _),
    simp_rw [function.comp_app, inv_rpow (le_of_lt hx), rpow_neg (le_of_lt hx), inv_inv] }
end

/-- Bound for `zeta_kernel₁` for `t → 0`. -/
lemma is_O_zero_zeta_kernel₁ : is_O (𝓝[>] 0) zeta_kernel₁ (λ t, t ^ (-(1 / 2) : ℝ)) :=
begin
  have : zeta_kernel₁ =ᶠ[𝓝[>] 0] zeta_kernel₂ + (λ t, (1 / sqrt t - 1) / 2),
  { refine eventually_eq_of_mem (Ioc_mem_nhds_within_Ioi $ left_mem_Ico.mpr zero_lt_one) (λ t h, _),
    rw [pi.add_apply, zeta_kernel₂, pi.add_apply, indicator_of_mem h],
    ring },
  refine ((is_O_zero_zeta_kernel₂_rpow _).add _).congr' this.symm (eventually_eq.refl _ _),
  simp_rw sub_div,
  apply is_O.sub,
  { apply is_O.of_norm_left,
    simp_rw [norm_div, norm_one, div_eq_mul_inv, one_mul, mul_comm _ (‖(2 : ℂ)‖)⁻¹],
    refine ((is_O_refl _ _).congr' (eventually_eq.refl _ _)
      (eventually_eq_of_mem self_mem_nhds_within (λ x hx, _))).const_mul_left _,
    rw [is_R_or_C.norm_of_real, abs_of_nonneg (sqrt_nonneg _)],
    simp_rw [sqrt_eq_rpow, rpow_neg (le_of_lt hx), one_div] },
  { refine is_O_iff.mpr ⟨‖(1 / 2 : ℂ)‖, _⟩,
    refine eventually_of_mem (Ioc_mem_nhds_within_Ioi $ left_mem_Ico.mpr zero_lt_one) (λ t ht, _),
    refine le_mul_of_one_le_right (norm_nonneg _) _,
    rw [norm_of_nonneg (rpow_nonneg_of_nonneg ht.1.le _), rpow_neg ht.1.le],
    exact one_le_inv (rpow_pos_of_pos ht.1 _) (rpow_le_one ht.1.le ht.2 one_half_pos.le) }
end

/-!
## Differentiability of the completed zeta function
-/

/-- The Mellin transform of the first zeta kernel is holomorphic for `1 / 2 < re s`. -/
lemma differentiable_at_mellin_zeta_kernel₁ {s : ℂ} (hs : 1 / 2 < s.re) :
  differentiable_at ℂ (mellin zeta_kernel₁) s :=
mellin_differentiable_at_of_is_O_rpow_exp pi_pos locally_integrable_zeta_kernel₁
  is_O_at_top_zeta_kernel₁ is_O_zero_zeta_kernel₁ hs

/-- The Mellin transform of the second zeta kernel is entire. -/
lemma differentiable_mellin_zeta_kernel₂ : differentiable ℂ (mellin zeta_kernel₂) :=
λ s, mellin_differentiable_at_of_is_O_rpow_exp pi_pos locally_integrable_zeta_kernel₂
  is_O_at_top_zeta_kernel₂ (is_O_zero_zeta_kernel₂_rpow _) ((sub_lt_self_iff _).mpr zero_lt_one)

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s - 1 / (s - 1)` is entire. -/
theorem differentiable_completed_zeta₀ : differentiable ℂ riemann_completed_zeta₀ :=
differentiable_mellin_zeta_kernel₂.comp (differentiable.div_const differentiable_id 2)

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`
(where it has simple poles). -/
theorem differentiable_at_completed_zeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
  differentiable_at ℂ riemann_completed_zeta s :=
begin
  refine (differentiable_completed_zeta₀.differentiable_at.sub _).add _,
  { exact (differentiable.differentiable_at (differentiable_const _)).div differentiable_at_id hs },
  { refine ((differentiable_const _).differentiable_at).div _ (sub_ne_zero.mpr hs'),
    exact differentiable_at_id.sub (differentiable_at_const _) },
end

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
theorem differentiable_at_riemann_zeta {s : ℂ} (hs' : s ≠ 1) :
  differentiable_at ℂ riemann_zeta s :=
begin
  /- First claim: the result holds at `t` for `t ≠ 0`. Note we will need to use this for the case
  `s = 0` also, as a hypothesis for the removable-singularity criterion. -/
  have c1 : ∀ (t : ℂ) (ht : t ≠ 0) (ht' : t ≠ 1), differentiable_at ℂ
      (λ u : ℂ, ↑π ^ (u / 2) * riemann_completed_zeta u / Gamma (u / 2)) t,
  { intros t ht ht',
    apply differentiable_at.mul,
    { refine (differentiable_at.const_cpow _ _).mul (differentiable_at_completed_zeta ht ht'),
      { exact differentiable_at.div_const differentiable_at_id _ },
      { exact or.inl (of_real_ne_zero.mpr pi_pos.ne') } },
    { refine differentiable_one_div_Gamma.differentiable_at.comp t _,
      exact differentiable_at.div_const differentiable_at_id _ } },
  /- Second claim: the limit at `s = 0` exists and is equal to `-1 / 2`. -/
  have c2 : tendsto (λ s : ℂ, ↑π ^ (s / 2) * riemann_completed_zeta s / Gamma (s / 2))
    (𝓝[≠] 0) (𝓝 $ -1 / 2),
  { have h1 : tendsto (λ z : ℂ, (π : ℂ) ^ (z / 2)) (𝓝 0) (𝓝 1),
    { convert (continuous_at_const_cpow (of_real_ne_zero.mpr pi_pos.ne')).comp _,
      { simp_rw [function.comp_app, zero_div, cpow_zero] },
      { exact continuous_at_id.div continuous_at_const two_ne_zero } },
    suffices h2 : tendsto (λ z, riemann_completed_zeta z / Gamma (z / 2)) (𝓝[≠] 0) (𝓝 $ -1 / 2),
    { convert (h1.mono_left nhds_within_le_nhds).mul h2,
      { ext1 x, rw mul_div }, { simp only [one_mul] } },
    suffices h3 : tendsto (λ z, (riemann_completed_zeta z * (z / 2)) / (z / 2 * Gamma (z / 2)))
      (𝓝[≠] 0) (𝓝 $ -1 / 2),
    { refine tendsto.congr' (eventually_eq_of_mem self_mem_nhds_within (λ z hz, _)) h3,
      rw [←div_div, mul_div_cancel _ (div_ne_zero hz two_ne_zero)] },
    have h4 : tendsto (λ z : ℂ, z / 2 * Gamma (z / 2)) (𝓝[≠] 0) (𝓝 1),
    { refine tendsto_self_mul_Gamma_nhds_zero.comp _,
      rw [tendsto_nhds_within_iff, (by simp : 𝓝 (0 : ℂ) = 𝓝 (0 / 2))],
      exact ⟨(tendsto_id.div_const _).mono_left nhds_within_le_nhds,
        eventually_of_mem self_mem_nhds_within (λ x hx, div_ne_zero hx two_ne_zero)⟩ },
    suffices : tendsto (λ z, riemann_completed_zeta z * z / 2) (𝓝[≠] 0) (𝓝 (-1 / 2 : ℂ)),
    { have := this.div h4 one_ne_zero,
      simp_rw [div_one, mul_div_assoc] at this,
      exact this },
    refine tendsto.div _ tendsto_const_nhds two_ne_zero,
    simp_rw [riemann_completed_zeta, add_mul, sub_mul],
    rw show 𝓝 (-1 : ℂ) = 𝓝 (0 - 1 + 0), by rw [zero_sub, add_zero],
    refine (tendsto.sub _ _).add _,
    { refine tendsto.mono_left _ nhds_within_le_nhds,
      have : continuous_at riemann_completed_zeta₀ 0,
        from (differentiable_completed_zeta₀).continuous.continuous_at,
      simpa only [id.def, mul_zero] using tendsto.mul this tendsto_id },
    { refine tendsto_const_nhds.congr' (eventually_eq_of_mem self_mem_nhds_within (λ t ht, _)),
      simp_rw one_div_mul_cancel ht },
    { refine tendsto.mono_left _ nhds_within_le_nhds,
      suffices : continuous_at (λ z : ℂ, 1 / (z - 1)) 0,
        by simpa only [id.def, mul_zero] using tendsto.mul this tendsto_id,
      refine continuous_at_const.div (continuous_at_id.sub continuous_at_const) _,
      simpa only [zero_sub] using neg_ne_zero.mpr one_ne_zero } },
  -- Now the main proof.
  rcases ne_or_eq s 0 with hs | rfl,
  { -- The easy case: `s ≠ 0`
    have : {(0 : ℂ)}ᶜ ∈ 𝓝 s, from is_open_compl_singleton.mem_nhds hs,
    refine (c1 s hs hs').congr_of_eventually_eq (eventually_eq_of_mem this (λ x hx, _)),
    unfold riemann_zeta,
    apply function.update_noteq hx },
  { -- The hard case: `s = 0`.
    rw [riemann_zeta, ←(lim_eq_iff ⟨-1 / 2, c2⟩).mpr c2],
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ), from is_open_compl_singleton.mem_nhds hs',
    refine ((complex.differentiable_on_update_lim_of_is_o S_nhds
      (λ t ht, (c1 t ht.2 ht.1).differentiable_within_at) _) 0 hs').differentiable_at S_nhds,
    simp only [zero_div, div_zero, complex.Gamma_zero, mul_zero, cpow_zero, sub_zero],
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (is_O_const_of_tendsto c2 $ one_ne_zero' ℂ).trans_is_o _,
    rw is_o_iff_tendsto',
    { exact tendsto.congr (λ x, by rw [←one_div, one_div_one_div]) nhds_within_le_nhds },
    { exact eventually_of_mem self_mem_nhds_within (λ x hx hx', (hx $ inv_eq_zero.mp hx').elim) } }
end

/-- The trivial zeroes of the zeta function. -/
lemma riemann_zeta_neg_two_mul_nat_add_one (n : ℕ) : riemann_zeta (-2 * (n + 1)) = 0 :=
begin
  have : (-2 : ℂ) * (n + 1) ≠ 0,
    from mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (nat.cast_add_one_ne_zero n),
  rw [riemann_zeta, function.update_noteq this,
    (show (-2) * ((n : ℂ) + 1) / 2 = -↑(n + 1), by { push_cast, ring }),
    complex.Gamma_neg_nat_eq_zero, div_zero],
end

/-- A formal statement of the Riemann hypothesis – constructing a term of this type is worth a
million dollars. -/
def riemann_hypothesis : Prop :=
∀ (s : ℂ) (hs : riemann_completed_zeta s = 0) (hs' : ¬∃ (n : ℕ), s = -2 * (n + 1)), s.re = 1 / 2

/-!
## Relating the Mellin transforms of the two zeta kernels
-/

lemma has_mellin_one_div_sqrt_Ioc {s : ℂ} (hs : 1 / 2 < re s) :
  has_mellin (indicator (Ioc 0 1) (λ t, 1 / ↑(sqrt t) : ℝ → ℂ)) s (1 / (s - 1 / 2)) :=
begin
  have h1 : eq_on (λ t, 1 / ↑(sqrt t) : ℝ → ℂ) (λ t, ↑t ^ (-1 / 2 : ℂ)) (Ioc 0 1),
  { intros t ht,
    simp_rw [neg_div, cpow_neg, ←one_div, sqrt_eq_rpow, of_real_cpow ht.1.le],
    push_cast },
  simp_rw [indicator_congr h1, (by ring : s - 1/2 = s + (-1) / 2)],
  convert has_mellin_cpow_Ioc (-1 / 2) _,
  rwa [(by push_cast : (-1 / 2 : ℂ) = (-1 / 2 : ℝ)), of_real_re, neg_div, ←sub_eq_add_neg, sub_pos]
end

/-- Evaluate the Mellin transform of the "fudge factor" in `zeta_kernel₂` -/
lemma has_mellin_one_div_sqrt_sub_one_div_two_Ioc {s : ℂ} (hs : 1 / 2 < s.re) :
  has_mellin ((Ioc 0 1).indicator (λ t, (1 - 1 / (sqrt t : ℂ)) / 2)) s
  (1 / (2 * s) - 1 / (2 * s - 1)) :=
begin
  have step1 : has_mellin (indicator (Ioc 0 1) (λ t, 1 - 1 / ↑(sqrt t) : ℝ → ℂ)) s
    (1 / s - 1 / (s - 1 / 2)),
  { have a := has_mellin_one_Ioc (one_half_pos.trans hs),
    have b := has_mellin_one_div_sqrt_Ioc hs,
    simpa only [a.2, b.2, ←indicator_sub] using has_mellin_sub a.1 b.1 },
  -- todo: implement something like "indicator.const_div" (blocked by the port for now)
  rw (show (Ioc 0 1).indicator (λ t, (1 - 1 / (sqrt t : ℂ)) / 2) =
    λ t, ((Ioc 0 1).indicator (λ t, (1 - 1 / (sqrt t : ℂ))) t) / 2,
    by { ext1 t, simp_rw [div_eq_inv_mul, indicator_mul_right] }),
  simp_rw [has_mellin, mellin_div_const, step1.2, sub_div, div_div],
  refine ⟨step1.1.div_const _, _⟩,
  rw [mul_comm, sub_mul, div_mul_cancel _ (two_ne_zero' ℂ), mul_comm s 2],
end

lemma mellin_zeta_kernel₂_eq_of_lt_re {s : ℂ} (hs : 1 / 2 < s.re) :
  mellin zeta_kernel₂ s = mellin zeta_kernel₁ s + 1 / (2 * s) - 1 / (2 * s - 1) :=
begin
  have h := mellin_convergent_of_is_O_rpow_exp pi_pos locally_integrable_zeta_kernel₁
    is_O_at_top_zeta_kernel₁ is_O_zero_zeta_kernel₁ hs,
  have h' := has_mellin_one_div_sqrt_sub_one_div_two_Ioc hs,
  simp_rw [zeta_kernel₂, pi.add_def, add_sub_assoc, (has_mellin_add h h'.1).2, h'.2],
end

lemma completed_zeta_eq_mellin_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
  riemann_completed_zeta s = mellin zeta_kernel₁ (s / 2) :=
begin
  have : 1 / 2 < (s / 2).re,
  { rw (show s / 2 = ↑(2⁻¹ : ℝ) * s, by { push_cast, rw mul_comm, refl }),
    rwa [of_real_mul_re, ←div_eq_inv_mul, div_lt_div_right (zero_lt_two' ℝ)] },
  rw [riemann_completed_zeta, riemann_completed_zeta₀, mellin_zeta_kernel₂_eq_of_lt_re this,
    sub_add, sub_sub, ←add_sub],
  conv_rhs { rw ←add_zero (mellin zeta_kernel₁ $ s / 2) },
  congr' 1,
  rw mul_div_cancel' _ (two_ne_zero' ℂ),
  abel
end

/-!
## Relating the first zeta kernel to the Dirichlet series
-/

/-- Auxiliary lemma for `mellin_zeta_kernel₁_eq_tsum`, computing the Mellin transform of an
individual term in the series. -/
lemma integral_cpow_mul_exp_neg_pi_mul_sq {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
  ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * rexp (-π * t * (n + 1) ^ 2) =
  ↑π ^ -s * complex.Gamma s * (1 / (n + 1) ^ (2 * s)) :=
begin
  rw [complex.Gamma_eq_integral hs, Gamma_integral_eq_mellin],
  conv_rhs { congr, rw [←smul_eq_mul, ←mellin_comp_mul_left _ _ pi_pos] },
  have : (1 / ((n : ℂ) + 1) ^ (2 * s)) = ↑(((n : ℝ) + 1) ^ (2 : ℝ)) ^ (-s),
  { rw [(by push_cast: ((n : ℂ) + 1) = ↑( (n : ℝ) + 1)),
      (by push_cast : (2 * s) = (↑(2 : ℝ) * s)),
      cpow_mul_of_real_nonneg, one_div, cpow_neg],
    rw [←nat.cast_succ],
    exact nat.cast_nonneg _ },
  conv_rhs { rw [this, mul_comm, ←smul_eq_mul] },
  rw [← mellin_comp_mul_right _ _ (show 0 < ((n : ℝ) + 1) ^ (2 : ℝ), by positivity)],
  refine set_integral_congr measurable_set_Ioi (λ t ht, _),
  simp_rw smul_eq_mul,
  congr' 3,
  conv_rhs { rw [←nat.cast_two, rpow_nat_cast] },
  ring
end

lemma mellin_zeta_kernel₁_eq_tsum {s : ℂ} (hs : 1 / 2 < s.re):
  mellin zeta_kernel₁ s = π ^ (-s) * Gamma s * ∑' (n : ℕ), 1 / (n + 1) ^ (2 * s) :=
begin
  let bd : ℕ → ℝ → ℝ := λ n t, t ^ (s.re - 1) * exp (-π * t * (n + 1) ^ 2),
  let f : ℕ → ℝ → ℂ := λ n t, t ^ (s - 1) * exp (-π * t * (n + 1) ^ 2),
  have hm : measurable_set (Ioi (0:ℝ)), from measurable_set_Ioi,
  have h_norm : ∀ (n : ℕ) {t : ℝ} (ht : 0 < t), ‖f n t‖ = bd n t,
  { intros n t ht,
    rw [norm_mul, complex.norm_eq_abs, complex.norm_eq_abs, complex.abs_of_nonneg (exp_pos _).le,
      abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re] },
  have hf_meas : ∀ (n : ℕ), ae_strongly_measurable (f n) (volume.restrict $ Ioi 0),
  { intro n,
    refine (continuous_on.mul _ _).ae_strongly_measurable hm,
    { exact (continuous_at.continuous_on
      (λ x hx, continuous_at_of_real_cpow_const _ _ $ or.inr $ ne_of_gt hx)) },
    { apply continuous.continuous_on,
      exact continuous_of_real.comp (continuous_exp.comp
        ((continuous_const.mul continuous_id').mul continuous_const)) } },
  have h_le : ∀ (n : ℕ), ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), ‖f n t‖ ≤ bd n t,
    from λ n, (ae_restrict_iff' hm).mpr (ae_of_all _ (λ t ht, le_of_eq (h_norm n ht))),
  have h_sum0 : ∀ {t : ℝ} (ht : 0 < t), has_sum (λ n, f n t) (t ^ (s - 1) * zeta_kernel₁ t),
  { intros t ht,
    have := (has_sum_of_real.mpr (summable_exp_neg_pi_mul_nat_sq ht).has_sum).mul_left
      ((t : ℂ) ^ (s - 1)),
    simpa only [of_real_mul, ←mul_assoc, of_real_bit0, of_real_one, mul_comm _ (2 : ℂ),
      of_real_sub, of_real_one, of_real_tsum] using this },
  have h_sum' : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), has_sum (λ (n : ℕ), f n t)
    (t ^ (s - 1) * zeta_kernel₁ t),
    from (ae_restrict_iff' hm).mpr (ae_of_all _ (λ t ht, h_sum0 ht)),
  have h_sum : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), summable (λ n : ℕ, bd n t),
  { refine (ae_restrict_iff' hm).mpr (ae_of_all _ (λ t ht, _)),
    simpa only [λ n, h_norm n ht] using summable_norm_iff.mpr (h_sum0 ht).summable },
  have h_int : integrable (λ t : ℝ, ∑' (n : ℕ), bd n t) (volume.restrict (Ioi 0)),
  { refine integrable_on.congr_fun (mellin_convergent_of_is_O_rpow_exp pi_pos
      locally_integrable_zeta_kernel₁ is_O_at_top_zeta_kernel₁ is_O_zero_zeta_kernel₁ hs).norm
      (λ t ht, _) hm,
    simp_rw [tsum_mul_left, norm_smul, complex.norm_eq_abs ((t : ℂ) ^ _),
      abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re],
    rw [zeta_kernel₁, ←of_real_tsum, complex.norm_eq_abs, complex.abs_of_nonneg],
    exact tsum_nonneg (λ n, (exp_pos _).le) },
  simpa only [integral_cpow_mul_exp_neg_pi_mul_sq (one_half_pos.trans hs), tsum_mul_left] using
    (has_sum_integral_of_dominated_convergence bd hf_meas h_le h_sum h_int h_sum').tsum_eq.symm,
end

lemma completed_zeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
  riemann_completed_zeta s = π ^ (-s / 2) * Gamma (s / 2) * ∑' (n : ℕ), 1 / (n + 1) ^ s :=
begin
  rw [completed_zeta_eq_mellin_of_one_lt_re hs, mellin_zeta_kernel₁_eq_tsum, neg_div,
    mul_div_cancel' _ (two_ne_zero' ℂ)],
  rw (show s / 2 = ↑(2⁻¹ : ℝ) * s, by { push_cast, rw mul_comm, refl }),
  rwa [of_real_mul_re, ←div_eq_inv_mul, div_lt_div_right (zero_lt_two' ℝ)]
end

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
theorem zeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
  riemann_zeta s = ∑' (n : ℕ), 1 / (n + 1) ^ s :=
begin
  have : s ≠ 0, by { contrapose! hs, rw [hs, zero_re], exact zero_le_one },
  rw [riemann_zeta, function.update_noteq this, completed_zeta_eq_tsum_of_one_lt_re hs,
    ←mul_assoc, neg_div, cpow_neg, mul_inv_cancel_left₀, mul_div_cancel_left],
  { apply Gamma_ne_zero_of_re_pos,
    rw [←of_real_one, ←of_real_bit0, div_eq_mul_inv, ←of_real_inv, mul_comm, of_real_mul_re],
    exact mul_pos (inv_pos_of_pos two_pos) (zero_lt_one.trans hs), },
  { rw [ne.def, cpow_eq_zero_iff, not_and_distrib, ←ne.def, of_real_ne_zero],
    exact or.inl (pi_pos.ne') }
end
