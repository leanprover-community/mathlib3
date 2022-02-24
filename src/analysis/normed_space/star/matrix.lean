/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/

import analysis.normed_space.basic
import data.complex.is_R_or_C
import linear_algebra.unitary_group

open_locale big_operators matrix

variables {𝕜 n : Type*} [is_R_or_C 𝕜]
variables [fintype n] [decidable_eq n]

section entrywise_sup_norm

local attribute [instance] matrix.normed_group

/-- The entrywise sup norm of a unitary matrix is at most 1. -/
lemma entrywise_sup_norm_bound_of_unitary {U : matrix n n 𝕜} (hU : U ∈ matrix.unitary_group n 𝕜) :
  ∥ U ∥ ≤ 1 :=
begin
  rw pi_norm_le_iff zero_le_one,
  intro i,
  rw pi_norm_le_iff zero_le_one,
  intro j,
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ∥ U i j ∥^2 ≤ (∑ (x : n), ∥ U i x ∥^2),
  { apply multiset.single_le_sum,
    { intros x h_x,
      rw multiset.mem_map at h_x,
      cases h_x with a h_a,
      rw ← h_a.2,
      apply sq_nonneg },
    { rw multiset.mem_map,
      use j,
      simp only [eq_self_iff_true, finset.mem_univ_val, and_self, sq_eq_sq] } },
  -- The L2 norm of a row is a diagonal entry of U ⬝ Uᴴ
  have diag_eq_norm_sum : (U ⬝ Uᴴ) i i = ∑ (x : n), ∥ U i x ∥^2,
  { simp only [matrix.mul_apply, matrix.conj_transpose_apply, ←star_ring_end_apply,
               is_R_or_C.mul_conj, is_R_or_C.norm_sq_eq_def', is_R_or_C.of_real_pow] },
  -- The L2 norm of a row is a diagonal entry of U ⬝ Uᴴ, real part
  have re_diag_eq_norm_sum : is_R_or_C.re ((U ⬝ Uᴴ) i i) = ∑ (x : n), ∥ U i x ∥^2,
  { rw is_R_or_C.ext_iff at diag_eq_norm_sum,
    rw diag_eq_norm_sum.1,
    norm_cast },
  -- Since U is unitary, the diagonal entries of U ⬝ Uᴴ are all 1
  have mul_eq_one : (U ⬝ Uᴴ) = 1, from unitary.mul_star_self_of_mem hU,
  have diag_eq_one : is_R_or_C.re ((U ⬝ Uᴴ) i i) = 1,
  { simp only [mul_eq_one, eq_self_iff_true, matrix.one_apply_eq, is_R_or_C.one_re] },
  -- Putting it all together
  rw [← sq_le_one_iff (norm_nonneg (U i j)), ← diag_eq_one, re_diag_eq_norm_sum],
  exact norm_sum,
end

end entrywise_sup_norm
