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
lemma charpoly_left_mul_matrix {S : Type*} [ring S] [algebra R S] (h : power_basis R S) :
  (left_mul_matrix h.basis h.gen).charpoly = minpoly R h.gen :=
begin
  casesI subsingleton_or_nontrivial R, { apply subsingleton.elim },
  apply minpoly.unique' R h.gen (charpoly_monic _),
  { apply (injective_iff_map_eq_zero (left_mul_matrix _)).mp (left_mul_matrix_injective h.basis),
    rw [← polynomial.aeval_alg_hom_apply, aeval_self_charpoly] },
  refine λ q hq, or_iff_not_imp_left.2 (λ h0, _),
  rw [matrix.charpoly_degree_eq_dim, fintype.card_fin] at hq,
  contrapose! hq, exact h.dim_le_degree_of_root h0 hq,
end

end power_basis
