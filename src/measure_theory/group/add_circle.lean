/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.integral.periodic
import data.zmod.quotient

/-!
# Measure-theoretic results about the additive circle

The file is a place to collect measure-theoretic results about the additive circle.

## Main definitions:

 * `add_circle.closed_ball_ae_eq_ball`: open and closed balls in the additive circle are almost
   equal
 * `add_circle.is_add_fundamental_domain_of_ae_ball`: a ball is a fundamental domain for rational
   angle rotation in the additive circle

-/

open set function filter measure_theory measure_theory.measure metric
open_locale measure_theory pointwise big_operators topological_space ennreal

namespace add_circle

variables {T : ℝ} [hT : fact (0 < T)]
include hT

lemma closed_ball_ae_eq_ball {x : add_circle T} {ε : ℝ} :
  closed_ball x ε =ᵐ[volume] ball x ε :=
begin
  cases le_or_lt ε 0 with hε hε,
  { rw [ball_eq_empty.mpr hε, ae_eq_empty, volume_closed_ball,
      min_eq_right (by linarith [hT.out] : 2 * ε ≤ T), ennreal.of_real_eq_zero],
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_two hε, },
  { suffices : volume (closed_ball x ε) ≤ volume (ball x ε),
    { exact (ae_eq_of_subset_of_measure_ge ball_subset_closed_ball this measurable_set_ball
        (measure_ne_top _ _)).symm, },
    have : tendsto (λ δ, volume (closed_ball x δ)) (𝓝[<] ε) (𝓝 $ volume (closed_ball x ε)),
    { simp_rw volume_closed_ball,
      refine ennreal.tendsto_of_real (tendsto.min tendsto_const_nhds $ tendsto.const_mul _ _),
      convert (@monotone_id ℝ _).tendsto_nhds_within_Iio ε,
      simp, },
    refine le_of_tendsto this (mem_nhds_within_Iio_iff_exists_Ioo_subset.mpr ⟨0, hε, λ r hr, _⟩),
    exact measure_mono (closed_ball_subset_ball hr.2), },
end

lemma is_add_fundamental_domain_of_ae_ball (I : set $ add_circle T)
  (u x : add_circle T) (hu : is_of_fin_add_order u)
  (hI : I =ᵐ[volume] ball x (T / (2 * add_order_of u))) :
  is_add_fundamental_domain (add_subgroup.zmultiples u) I :=
is_add_fundamental_domain.mk_of_measure_univ_le
(measurable_set_ball.null_measurable_set.congr hI.symm)
begin
  rintros ⟨g, hg⟩ hg',
  replace hg' : g ≠ 0, by simpa only [ne.def, add_subgroup.mk_eq_zero_iff] using hg',
  change ae_disjoint volume (g +ᵥ I) I,
  refine ae_disjoint.congr (disjoint.ae_disjoint _)
    ((quasi_measure_preserving_add_left volume (-g)).vadd_ae_eq_of_ae_eq g hI) hI,
  let B := ball x (T / (2 * add_order_of u)),
  have hBg : g +ᵥ B = ball (g + x) (T / (2 * add_order_of u)),
  { rw [add_comm g x, ← singleton_add_ball _ x g, add_ball, thickening_singleton], },
  rw hBg,
  apply ball_disjoint_ball,
  have hu' : 0 < (add_order_of u : ℝ) := nat.cast_pos.mpr (add_order_of_pos_iff.mpr hu),
  rw [dist_eq_norm, add_sub_cancel, div_mul_eq_div_div, ← add_div, ← add_div, add_self_div_two,
    div_le_iff' hu', ← nsmul_eq_mul],
  refine (le_add_order_smul_norm_of_is_of_fin_add_order (hu.of_mem_zmultiples hg) hg').trans
    (nsmul_le_nsmul (norm_nonneg g) _),
  exact nat.le_of_dvd (add_order_of_pos_iff.mpr hu) (add_order_of_dvd_of_mem_zmultiples hg),
end
(λ g, quasi_measure_preserving_add_left volume g)
begin
  let B := ball x (T / (2 * add_order_of u)),
  replace hI : I =ᵐ[volume] closed_ball x (T / (2 * ↑(add_order_of u))) :=
    hI.trans closed_ball_ae_eq_ball.symm,
  let G := add_subgroup.zmultiples u,
  haveI : fintype G := @fintype.of_finite _ hu.finite_zmultiples,
  have hG_card : (finset.univ : finset G).card = add_order_of u,
  { rw [add_order_eq_card_zmultiples', nat.card_eq_fintype_card], refl, },
  replace hu : 1 ≤ (add_order_of u : ℝ), { norm_cast, linarith [add_order_of_pos' hu], },
  simp_rw [measure_vadd_set],
  rw [add_circle.measure_univ, tsum_fintype, finset.sum_const, measure_congr hI, volume_closed_ball,
    ennreal.nsmul_of_real, mul_div, mul_div_mul_comm, div_self (@two_ne_zero ℝ _ _), one_mul,
    min_eq_right (div_le_self hT.out.le hu), hG_card, nsmul_eq_mul,
    mul_div_cancel' T (lt_of_lt_of_le zero_lt_one hu).ne.symm],
  exact le_refl _,
end

lemma volume_of_add_preimage_eq (s I : set $ add_circle T)
  (u x : add_circle T) (hu : is_of_fin_add_order u) (hs : u +ᵥ s = s)
  (hI : I =ᵐ[volume] ball x (T / (2 * add_order_of u))) :
  volume s = add_order_of u • volume (s ∩ I) :=
begin
  let G := add_subgroup.zmultiples u,
  haveI : fintype G := @fintype.of_finite _ hu.finite_zmultiples,
  have hsG : ∀ (g : G), g +ᵥ s = s,
  { rintros ⟨y, hy⟩, convert vadd_eq_self_of_mem_zmultiples hy hs using 1, },
  rw [(is_add_fundamental_domain_of_ae_ball I u x hu hI).measure_eq_card_smul_of_vadd_eq_self s hsG,
    add_order_eq_card_zmultiples' u, nat.card_eq_fintype_card],
end

end add_circle
