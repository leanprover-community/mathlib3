/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.normed_space.basic
import analysis.normed_space.exponential
import topology.instances.triv_sq_zero_ext

/-!
# Results on `triv_sq_zero_ext R M` related to the norm

For now, this file contains results about `exp` for this type.

## Main results

* `triv_sq_zero_ext.fst_exp`
* `triv_sq_zero_ext.snd_exp`
* `triv_sq_zero_ext.exp_inl`
* `triv_sq_zero_ext.exp_inr`

## TODO
* Actually define a sensible norm on `triv_sq_zero_ext R M`, so that we have access to lemmas
  like `exp_add`.
* Generalize some of these results to non-commutative `R`.

-/

variables (𝕜 : Type*) {R M : Type*}

local notation `tsze` := triv_sq_zero_ext

namespace triv_sq_zero_ext

section topology
variables [topological_space R] [topological_space M]


/-- If `exp R x.fst` converges to `e` then `exp R x` converges to `inl e + inr (e • x.snd)`. -/
lemma has_sum_exp_series [field 𝕜] [char_zero 𝕜] [comm_ring R]
  [add_comm_group M] [algebra 𝕜 R]
  [module R M] [module Rᵐᵒᵖ M] [is_central_scalar R M]
  [module 𝕜 M] [is_scalar_tower 𝕜 R M]
  [topological_ring R] [topological_add_group M]
  [has_continuous_smul R M]
  (x : tsze R M) {e : R} (h : has_sum (λ n, exp_series 𝕜 R n (λ _, x.fst)) e) :
  has_sum (λ n, exp_series 𝕜 (tsze R M) n (λ _, x)) (inl e + inr (e • x.snd)) :=
begin
  simp_rw [exp_series_apply_eq] at *,
  conv
  { congr,
    funext,
    rw [←inl_fst_add_inr_snd_eq (x ^ _), fst_pow, snd_pow, smul_add, ←inr_smul,
      ←inl_smul, nsmul_eq_smul_cast 𝕜 n, smul_smul, inv_mul_eq_div, ←inv_div, ←smul_assoc], },
  refine (has_sum_inl M h).add (has_sum_inr M _),
  apply has_sum.smul_const,
  rw [←has_sum_nat_add_iff' 1], swap, apply_instance,
  rw [finset.range_one, finset.sum_singleton, nat.cast_zero, div_zero, inv_zero, zero_smul,
    sub_zero],
  simp_rw [←nat.succ_eq_add_one, nat.pred_succ, nat.factorial_succ, nat.cast_mul,
    ←nat.succ_eq_add_one,
    mul_div_cancel_left _ ((@nat.cast_ne_zero 𝕜 _ _ _).mpr $ nat.succ_ne_zero _)],
  exact h,
end

end topology

section normed_ring
variables [is_R_or_C 𝕜] [normed_comm_ring R] [add_comm_group M]
variables [normed_algebra 𝕜 R] [module R M] [module Rᵐᵒᵖ M] [is_central_scalar R M]
variables [module 𝕜 M] [is_scalar_tower 𝕜 R M]
variables [topological_space M] [topological_ring R]
variables [topological_add_group M] [has_continuous_smul R M]
variables [complete_space R] [t2_space R] [t2_space M]

lemma exp_def (x : tsze R M) : exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) :=
begin
  simp_rw [exp, formal_multilinear_series.sum],
  refine (has_sum_exp_series 𝕜 x _).tsum_eq,
  exact exp_series_has_sum_exp _,
end

@[simp] lemma fst_exp (x : tsze R M) : fst (exp 𝕜 x) = exp 𝕜 x.fst :=
by rw [exp_def, fst_add, fst_inl, fst_inr, add_zero]

@[simp] lemma snd_exp (x : tsze R M) : snd (exp 𝕜 x) = exp 𝕜 x.fst • x.snd :=
by rw [exp_def, snd_add, snd_inl, snd_inr, zero_add]

@[simp] lemma exp_inl (x : R) : exp 𝕜 (inl x : tsze R M) = inl (exp 𝕜 x) :=
by rw [exp_def, fst_inl, snd_inl, smul_zero, inr_zero, add_zero]

@[simp] lemma exp_inr (m : M) : exp 𝕜 (inr m : tsze R M) = 1 + inr m :=
by rw [exp_def, fst_inr, exp_zero, snd_inr, one_smul, inl_one]

/-- Polar form of trivial-square-zero extension. -/
lemma eq_smul_exp_of_invertible (x : tsze R M) [invertible x.fst] :
  x = x.fst • exp 𝕜 (⅟x.fst • inr x.snd) :=
by rw [←inr_smul, exp_inr, smul_add, ←inl_one, ←inl_smul, ←inr_smul, smul_eq_mul, mul_one,
    smul_smul, mul_inv_of_self, one_smul, inl_fst_add_inr_snd_eq]

end normed_ring


section normed_field
variables [is_R_or_C 𝕜] [normed_field R] [add_comm_group M]
variables [normed_algebra 𝕜 R] [module R M] [module Rᵐᵒᵖ M] [is_central_scalar R M]
variables [module 𝕜 M] [is_scalar_tower 𝕜 R M]
variables [topological_space M] [topological_ring R]
variables [topological_add_group M] [has_continuous_smul R M]
variables [complete_space R] [t2_space R] [t2_space M]

/-- More convenient version of `triv_sq_zero_ext.eq_smul_exp_of_invertible` for when `R` is a
field. -/
lemma eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst ≠ 0) :
  x = x.fst • exp 𝕜 (x.fst⁻¹ • inr x.snd) :=
begin
  letI : invertible x.fst := invertible_of_nonzero hx,
  exact eq_smul_exp_of_invertible _ _
end

end normed_field

end triv_sq_zero_ext
