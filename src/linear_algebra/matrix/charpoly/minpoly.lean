/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Eric Wieser
-/

import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.to_lin
import ring_theory.power_basis

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.

This also includes some miscellaneous results about `minpoly` on matrices.
-/

noncomputable theory

universes u v w

open polynomial matrix

variables {R : Type u} [comm_ring R]
variables {n : Type v} [decidable_eq n] [fintype n]
variables {N : Type w} [add_comm_group N] [module R N]

open finset

namespace matrix
open_locale matrix
variables (M : matrix n n R)

@[simp] theorem minpoly_to_lin' : minpoly R M.to_lin' = minpoly R M :=
minpoly.minpoly_alg_equiv (to_lin_alg_equiv' : matrix n n R ≃ₐ[R] _) M

@[simp] theorem minpoly_to_lin (b : basis n R N) (M : matrix n n R) :
  minpoly R (to_lin b b M) = minpoly R M :=
minpoly.minpoly_alg_equiv (to_lin_alg_equiv b : matrix n n R ≃ₐ[R] _) M

theorem is_integral : is_integral R M := ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type*} [field K] (M : matrix n n K) :
  (minpoly K M) ∣ M.charpoly :=
minpoly.dvd _ _ (aeval_self_charpoly M)

end matrix

namespace linear_map

@[simp] theorem minpoly_to_matrix' (f : (n → R) →ₗ[R] (n → R)) :
  minpoly R f.to_matrix' = minpoly R f :=
minpoly.minpoly_alg_equiv (to_matrix_alg_equiv' : _ ≃ₐ[R] matrix n n R) f

@[simp] theorem minpoly_to_matrix (b : basis n R N) (f : N →ₗ[R] N) :
  minpoly R (to_matrix b b f) = minpoly R f :=
minpoly.minpoly_alg_equiv (to_matrix_alg_equiv b : _ ≃ₐ[R] matrix n n R) f

end linear_map

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
