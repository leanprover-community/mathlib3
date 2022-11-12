/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.group.add_circle
import dynamics.ergodic.ergodic
import measure_theory.covering.density_theorem

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

variables {T : ℝ}

lemma vadd_eq_self_of_preimage_zsmul_eq_self
  {j : ℕ} {n : ℤ} {s : set $ add_circle T} (hs : (λ y, n • y)⁻¹' s = s)
  {u : add_circle T} (hu : n^j • u = 0) : u +ᵥ s = s :=
begin
  suffices : ∀ {v : add_circle T} (hv : n^j • v = 0), v +ᵥ s ⊆ s,
  { refine le_antisymm (this hu) _,
    conv_lhs { rw ← vadd_neg_vadd u s, },
    replace hu : n^j • (-u) = 0, { rwa [zsmul_neg', neg_smul, neg_eq_zero], },
    simpa only [le_eq_subset, set_vadd_subset_set_vadd_iff] using this hu, },
  set f : add_circle T → add_circle T := λ y, n • y,
  rw (is_fixed_pt.preimage_iterate hs j : (f^[j])⁻¹' s = s).symm,
  rintros v hv - ⟨y, hy : (f^[j]) y ∈ s, rfl⟩,
  change (f^[j]) (v + y) ∈ s,
  simpa only [f, smul_iterate, smul_add, add_left_eq_self, hv, zero_add] using hy,
end

variables [hT : fact (0 < T)]
include hT

lemma pre_ergodic_zsmul {n : ℤ} (hn : 1 < |n|) :
  pre_ergodic (λ (y : add_circle T), n • y) :=
⟨begin
  intros s hs hs',
  have hT₀ : 0 < T := hT.out,
  have hT₁ : ennreal.of_real T ≠ 0 := by simpa,
  replace hn : 1 < n.nat_abs, { rwa [int.abs_eq_nat_abs, nat.one_lt_cast] at hn, },
  replace hs : null_measurable_set s volume := hs.null_measurable_set,
  rw [ae_eq_empty, ae_eq_univ_iff_measure_eq hs, add_circle.measure_univ],
  cases (eq_or_ne (volume s) 0) with h h, { exact or.inl h, },
  right,
  obtain ⟨d, -, hd⟩ := exists_mem_of_measure_ne_zero_of_ae h
    (is_doubling_measure.ae_tendsto_measure_inter_div (volume : measure $ add_circle T) s 1),
  let I : ℕ → set (add_circle T) := λ j, closed_ball d (T / (2 * ↑(n.nat_abs^j))),
  replace hd : tendsto (λ j, volume (s ∩ I j) / volume (I j)) at_top (𝓝 1),
  { let δ : ℕ → ℝ := λ j, T / (2 * ↑(n.nat_abs^j)),
    have hδ₀ : ∀ j, 0 < δ j := λ j, div_pos hT₀ (by positivity),
    have hδ₁ : tendsto δ at_top (𝓝[>] 0),
    { simp_rw [δ, div_eq_mul_inv, mul_inv, ← mul_assoc],
      rw ← mul_zero (T * 2⁻¹),
      apply tendsto_nhds_within_pos.const_mul (by positivity : 0 < T * 2⁻¹),
      simp_rw [nat.cast_pow, ← inv_pow],
      exact tendsto_pow_at_top_nhds_within_0_of_lt_1
        (by positivity) (inv_lt_one $ nat.one_lt_cast.mpr hn), },
    have hw : ∀ᶠ j in at_top, d ∈ closed_ball d (1 * δ j) :=
      eventually_of_forall (λ j, by simp [(hδ₀ j).le]),
    exact hd _ δ hδ₁ hw, },
  suffices : ∀ j, volume (s ∩ I j) / volume (I j) = volume s / ennreal.of_real T,
  { simp_rw [this, tendsto_const_nhds_iff, ennreal.div_eq_one_iff hT₁ ennreal.of_real_ne_top] at hd,
    exact hd, },
  intros j,
  have hnj : 0 < n.nat_abs^j, { positivity, },
  have hnj' : 1 ≤ (↑(n.nat_abs ^ j) : ℝ), { norm_cast, exact nat.succ_le_iff.mpr hnj, },
  let u : add_circle T := ↑(((↑1 : ℝ) / ↑(n.nat_abs^j)) * T),
  have hu₀ : add_order_of u = n.nat_abs^j,
  { exact add_order_of_div_of_gcd_eq_one hnj (gcd_one_right _), },
  have hu₁ : is_of_fin_add_order u, { rwa [← add_order_of_pos_iff, hu₀], },
  have hu₂ : n^j • u = 0,
  { rw [← add_order_of_dvd_iff_zsmul_eq_zero, hu₀, int.coe_nat_pow, ← int.abs_eq_nat_abs, ← abs_pow,
      abs_dvd], },
  have hI₀ : volume (I j) ≠ 0 := (measure_closed_ball_pos _ d $ by positivity).ne.symm,
  have hI₁ : volume (I j) ≠ ⊤ := measure_ne_top _ _,
  have hI₂ : volume (I j) * ↑(n.nat_abs ^ j) = ennreal.of_real T,
  { rw [volume_closed_ball, mul_div, mul_div_mul_left T _ two_ne_zero,
      min_eq_right (div_le_self hT₀.le hnj'), mul_comm, ← nsmul_eq_mul, ennreal.nsmul_of_real,
      nsmul_eq_mul, mul_div_cancel'],
    exact nat.cast_ne_zero.mpr hnj.ne.symm, },
  have hus : u +ᵥ s = s := vadd_eq_self_of_preimage_zsmul_eq_self hs' hu₂,
  rw [ennreal.div_eq_div_iff hT₁ ennreal.of_real_ne_top hI₀ hI₁,
    volume_of_add_preimage_eq s _ u d hu₁ hus closed_ball_ae_eq_ball, hu₀, nsmul_eq_mul,
    ← mul_assoc, hI₂],
end⟩

lemma ergodic_zsmul {n : ℤ} (hn : 1 < |n|) : ergodic (λ (y : add_circle T), n • y) :=
{ .. measure_preserving_zsmul volume (abs_pos.mp $ lt_trans zero_lt_one hn),
  .. pre_ergodic_zsmul hn, }

end add_circle
