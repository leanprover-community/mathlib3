/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.quaternion
import analysis.normed_space.exponential
import analysis.inner_product_space.pi_L2

/-!
# Lemmas about `exp` on `quaternion`s
-/

open_locale quaternion nat

namespace quaternion

section
variables {α : Type*}

lemma has_sum_coe {f : α → ℝ} {r : ℝ} (h : has_sum f r) :
  has_sum (λ a, (f a : ℍ[ℝ])) (↑r : ℍ[ℝ]) :=
by simpa only using h.map (algebra_map ℝ ℍ[ℝ]) (continuous_algebra_map _ _)

lemma continuous_re : continuous (λ q : ℍ[ℝ], q.re) :=
sorry

lemma summable_coe_iff  {f : α → ℝ} : summable (λ a, (f a : ℍ[ℝ])) ↔ summable f :=
by simpa only using summable.map_iff_of_left_inverse (algebra_map ℝ ℍ[ℝ])
  ({to_fun := re, map_add' := add_re, map_zero' := zero_re} : ℍ[ℝ] →+ ℝ)
  (continuous_algebra_map _ _) continuous_re coe_re

lemma tsum_coe (f : α → ℝ) : ∑' a, (f a : ℍ[ℝ]) = ↑(∑' a, f a) :=
begin
  by_cases hf : summable f,
  { exact (has_sum_coe hf.has_sum).tsum_eq, },
  { simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (summable_coe_iff.not.mpr hf)] },
end

end

@[simp, norm_cast] lemma exp_coe (r : ℝ) : exp ℝ (r : ℍ[ℝ]) = ↑(exp ℝ r) :=
(map_exp ℝ (algebra_map ℝ ℍ[ℝ]) (continuous_algebra_map _ _) _).symm

lemma exp_of_imaginary (q : quaternion ℝ) (hq : q.re = 0) :
  exp ℝ q = ↑(real.cos ‖q‖) + (real.sin ‖q‖ / ‖q‖) • q :=
begin
  obtain rfl | hq0 := eq_or_ne q 0,
  { simp },
  have hconj : conj q = -q,
  { ext,
    { simp [hq] },
    iterate 3 { refl } },
  have : q^2 = -norm_sq q,
  { rw [←quaternion.conj_mul_self, hconj, neg_mul, neg_neg, sq], },
  simp_rw exp_eq_tsum,
  have heven : ∀ k : ℕ,
    ((2 * k)! : ℝ)⁻¹ • q ^ (2 * k) = ↑((-1)^k * ((2 * k)! : ℝ)⁻¹ • ‖q‖ ^ (2 * k)),
  { intro k,
    rw [pow_mul, this, ←coe_neg, ←coe_pow, ←coe_smul, norm_sq_eq_norm_sq,
      ←sq, neg_pow (‖q‖^2), mul_smul_comm, pow_mul] },
  have hodd : ∀ k : ℕ,
    ((2 * k + 1)! : ℝ)⁻¹ • q ^ (2 * k + 1)
      = ↑(((-1)^k * ((2 * k + 1)! : ℝ)⁻¹ • ‖q‖ ^ (2 * k + 1)) / ‖q‖) * q,
  { intro k,
    rw [pow_succ' _ (2 * _), pow_mul, this, ←coe_neg, ←coe_pow, ←smul_mul_assoc,
      ←coe_smul, norm_sq_eq_norm_sq,
      ←sq, neg_pow (‖q‖^2), mul_smul_comm, ←pow_mul, div_eq_mul_inv, smul_mul_assoc, mul_assoc,
      pow_succ', mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr hq0), mul_one], },
  rw ←tsum_even_add_odd,
  { simp_rw [heven, hodd, tsum_mul_right, tsum_coe, coe_mul_eq_smul, div_eq_mul_inv,
      tsum_mul_right, ←div_eq_mul_inv],
    congr' 3,
    { -- standard result about cos
      sorry },
    { -- standard result about sin
      sorry } },
  { simp_rw heven,
    -- standard result about cos
    sorry },
  { simp_rw hodd,
    apply summable.mul_right,
    simp_rw [div_eq_mul_inv _ (‖q‖), coe_mul _ (‖q‖⁻¹)],
    apply summable.mul_right,
    -- standard result about sin
    sorry },
end

lemma exp_eq (q : quaternion ℝ) :
  exp ℝ q = exp ℝ q.re • (
    let v := q - q.re in ↑(real.cos ‖v‖) + (real.sin ‖v‖ / ‖v‖) • v) :=
begin
  letI : complete_space (ℍ[ℝ]) := sorry,
  dsimp only,
  rw [←exp_of_imaginary (q - q.re), ←coe_mul_eq_smul, ←exp_coe,
    ←exp_add_of_commute, add_sub_cancel'_right],
  exact algebra.commutes q.re (_ : ℍ[ℝ]),
  exact sub_self _,
end

end quaternion
