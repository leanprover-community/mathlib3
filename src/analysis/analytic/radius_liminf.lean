/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.analytic.basic
import analysis.special_functions.pow

/-!
# Representation of `formal_multilinear_series.radius` as a `liminf`

In this file we prove that the radius of convergence of a `formal_multilinear_series` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `basic.lean` because this
would create a circular dependency once we redefine `exp` using `formal_multilinear_series`.
-/
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

open_locale topology classical big_operators nnreal ennreal
open filter asymptotics

namespace formal_multilinear_series

variables (p : formal_multilinear_series 𝕜 E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
lemma radius_eq_liminf : p.radius = liminf (λ n, 1/((‖p n‖₊) ^ (1 / (n : ℝ)) : ℝ≥0)) at_top :=
begin
  have : ∀ (r : ℝ≥0) {n : ℕ}, 0 < n →
    ((r : ℝ≥0∞) ≤ 1 / ↑(‖p n‖₊ ^ (1 / (n : ℝ))) ↔ ‖p n‖₊ * r ^ n ≤ 1),
  { intros r n hn,
    have : 0 < (n : ℝ) := nat.cast_pos.2 hn,
    conv_lhs {rw [one_div, ennreal.le_inv_iff_mul_le, ← ennreal.coe_mul,
      ennreal.coe_le_one_iff, one_div, ← nnreal.rpow_one r, ← mul_inv_cancel this.ne',
      nnreal.rpow_mul, ← nnreal.mul_rpow, ← nnreal.one_rpow (n⁻¹),
      nnreal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm, nnreal.rpow_nat_cast] } },
  apply le_antisymm; refine ennreal.le_of_forall_nnreal_lt (λ r hr, _),
  { rcases ((tfae_exists_lt_is_o_pow (λ n, ‖p n‖ * r ^ n) 1).out 1 7).1 (p.is_o_of_lt_radius hr)
      with ⟨a, ha, H⟩,
    refine le_Liminf_of_le (by apply_auto_param) (eventually_map.2 $ _),
    refine H.mp ((eventually_gt_at_top 0).mono $ λ n hn₀ hn, (this _ hn₀).2
      (nnreal.coe_le_coe.1 _)),
    push_cast,
    exact (le_abs_self _).trans (hn.trans (pow_le_one _ ha.1.le ha.2.le)) },
  { refine p.le_radius_of_is_O (is_O.of_bound 1 _),
    refine (eventually_lt_of_lt_liminf hr).mp ((eventually_gt_at_top 0).mono (λ n hn₀ hn, _)),
    simpa using nnreal.coe_le_coe.2 ((this _ hn₀).1 hn.le) }
end

end formal_multilinear_series
