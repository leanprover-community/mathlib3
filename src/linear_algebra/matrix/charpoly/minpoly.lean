/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/

import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.to_lin
import ring_theory.power_basis

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.
-/

noncomputable theory

universes u v

open polynomial matrix

variables {R : Type u} [comm_ring R]
variables {n : Type v} [decidable_eq n] [fintype n]

open finset

variable {M : matrix n n R}

namespace matrix

theorem is_integral : is_integral R M := ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type*} [field K] (M : matrix n n K) :
  (minpoly K M) ∣ M.charpoly :=
minpoly.dvd _ _ (aeval_self_charpoly M)

end matrix

section power_basis

open algebra

/-- The characteristic polynomial of the map `λ x, a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
lemma charpoly_left_mul_matrix {K S : Type*} [field K] [comm_ring S] [algebra K S]
  (h : power_basis K S) :
  (left_mul_matrix h.basis h.gen).charpoly = minpoly K h.gen :=
begin
  apply minpoly.unique,
  { apply matrix.charpoly_monic },
  { apply (injective_iff_map_eq_zero (left_mul_matrix _)).mp (left_mul_matrix_injective h.basis),
    rw [← polynomial.aeval_alg_hom_apply, aeval_self_charpoly] },
  { intros q q_monic root_q,
    rw [matrix.charpoly_degree_eq_dim, fintype.card_fin, degree_eq_nat_degree q_monic.ne_zero],
    apply with_bot.some_le_some.mpr,
    exact h.dim_le_nat_degree_of_root q_monic.ne_zero root_q }
end

end power_basis
