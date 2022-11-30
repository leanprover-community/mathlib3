/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.group.add_circle
import dynamics.ergodic.ergodic
import measure_theory.covering.density_theorem
import data.set.pointwise.iterate

/-!
# Ergodic maps of the additive circle

This file contains proofs of ergodicity for maps of the additive circle.

# Main definitions:

 * `add_circle.ergodic_zsmul`: given `n : ℤ` such that `1 < |n|`, the self map `y ↦ n • y` on
   the additive circle is ergodic (wrt the Haar measure).

# TODO

 * The map `y ↦ n • y + x` is ergodic for any `x` (and `1 < |n|`).

-/

open set function measure_theory measure_theory.measure filter metric
open_locale measure_theory nnreal ennreal topological_space pointwise

namespace add_circle

variables {T : ℝ} [hT : fact (0 < T)]
include hT

/-- If a null-measurable subset `s` of the circle is invariant under rotation by an arbitrarily
small rational angle, then it must be almost empty or almost full. -/
lemma ae_empty_or_univ_of_forall_vadd_eq_self
  {s : set $ add_circle T} (hs : null_measurable_set s volume)
  {ι : Type*} {l : filter ι} [l.ne_bot] {u : ι → add_circle T}
  (hu₁ : ∀ i, (u i) +ᵥ s = s) (hu₂ : tendsto (add_order_of ∘ u) l at_top) :
  s =ᵐ[volume] (∅ : set $ add_circle T) ∨ s =ᵐ[volume] univ :=
begin
  have hT₀ : 0 < T := hT.out,
  have hT₁ : ennreal.of_real T ≠ 0 := by simpa,
  rw [ae_eq_empty, ae_eq_univ_iff_measure_eq hs, add_circle.measure_univ],
  cases (eq_or_ne (volume s) 0) with h h, { exact or.inl h, },
  right,
  obtain ⟨d, -, hd⟩ := exists_mem_of_measure_ne_zero_of_ae h
    (is_doubling_measure.ae_tendsto_measure_inter_div (volume : measure $ add_circle T) s 1),
  let I : ι → set (add_circle T) := λ j, closed_ball d (T / (2 * ↑(add_order_of $ u j))),
  replace hd : tendsto (λ j, volume (s ∩ I j) / volume (I j)) l (𝓝 1),
  { let δ : ι → ℝ := λ j, T / (2 * ↑(add_order_of $ u j)),
    have hδ₀ : ∀ᶠ j in l, 0 < δ j :=
      (hu₂.eventually_gt_at_top 0).mono (λ j hj, div_pos hT₀ $ by positivity),
    have hδ₁ : tendsto δ l (𝓝[>] 0),
    { refine tendsto_nhds_within_iff.mpr ⟨_, hδ₀⟩,
      replace hu₂ : tendsto (λ j, (T⁻¹ * 2) * (add_order_of $ u j)) l at_top :=
        (tendsto_coe_nat_at_top_iff.mpr hu₂).const_mul_at_top (by positivity : 0 < T⁻¹ * 2),
      convert hu₂.inv_tendsto_at_top,
      ext j,
      simp only [δ, pi.inv_apply, mul_inv_rev, inv_inv, div_eq_inv_mul, ← mul_assoc], },
    have hw : ∀ᶠ j in l, d ∈ closed_ball d (1 * δ j) := hδ₀.mono (λ j hj, by simp [hj.le]),
    exact hd _ δ hδ₁ hw, },
  suffices : ∀ᶠ j in l, volume (s ∩ I j) / volume (I j) = volume s / ennreal.of_real T,
  { replace hd := hd.congr' this,
    rwa [tendsto_const_nhds_iff, ennreal.div_eq_one_iff hT₁ ennreal.of_real_ne_top] at hd, },
  refine (hu₂.eventually_gt_at_top 0).mono (λ j hj, _),
  have huj : is_of_fin_add_order (u j) := add_order_of_pos_iff.mp hj,
  have huj' : 1 ≤ (↑(add_order_of $ u j) : ℝ), { norm_cast, exact nat.succ_le_iff.mpr hj, },
  have hI₀ : volume (I j) ≠ 0 := (measure_closed_ball_pos _ d $ by positivity).ne.symm,
  have hI₁ : volume (I j) ≠ ⊤ := measure_ne_top _ _,
  have hI₂ : volume (I j) * ↑(add_order_of $ u j) = ennreal.of_real T,
  { rw [volume_closed_ball, mul_div, mul_div_mul_left T _ two_ne_zero,
      min_eq_right (div_le_self hT₀.le huj'), mul_comm, ← nsmul_eq_mul, ← ennreal.of_real_nsmul,
      nsmul_eq_mul, mul_div_cancel'],
    exact nat.cast_ne_zero.mpr hj.ne', },
  rw [ennreal.div_eq_div_iff hT₁ ennreal.of_real_ne_top hI₀ hI₁,
    volume_of_add_preimage_eq s _ (u j) d huj (hu₁ j) closed_ball_ae_eq_ball, nsmul_eq_mul,
    ← mul_assoc, hI₂],
end

lemma pre_ergodic_zsmul {n : ℤ} (hn : 1 < |n|) :
  pre_ergodic (λ (y : add_circle T), n • y) :=
⟨begin
  intros s hs hs',
  let u : ℕ → add_circle T := λ j, ↑(((↑1 : ℝ) / ↑(n.nat_abs^j)) * T),
  replace hn : 1 < n.nat_abs, { rwa [int.abs_eq_nat_abs, nat.one_lt_cast] at hn, },
  have hu₀ : ∀ j, add_order_of (u j) = n.nat_abs^j,
  { exact λ j, add_order_of_div_of_gcd_eq_one (pow_pos (pos_of_gt hn) j) (gcd_one_left _), },
  have hnu : ∀ j, n^j • (u j) = 0 := λ j, by rw [← add_order_of_dvd_iff_zsmul_eq_zero, hu₀,
    int.coe_nat_pow, ← int.abs_eq_nat_abs, ← abs_pow, abs_dvd],
  have hu₁ : ∀ j, (u j) +ᵥ s = s := λ j, vadd_eq_self_of_preimage_zsmul_eq_self hs' (hnu j),
  have hu₂ : tendsto (λ j, add_order_of $ u j) at_top at_top,
  { simp_rw hu₀, exact nat.tendsto_pow_at_top_at_top_of_one_lt hn, },
  exact ae_empty_or_univ_of_forall_vadd_eq_self hs.null_measurable_set hu₁ hu₂,
end⟩

lemma ergodic_zsmul {n : ℤ} (hn : 1 < |n|) : ergodic (λ (y : add_circle T), n • y) :=
{ .. measure_preserving_zsmul volume (abs_pos.mp $ lt_trans zero_lt_one hn),
  .. pre_ergodic_zsmul hn, }

end add_circle
