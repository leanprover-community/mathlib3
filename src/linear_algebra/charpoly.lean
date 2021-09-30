/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.basis

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module.

## Main definition

* `linear_map.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : M →ₗ[R] M)

open_locale classical matrix

noncomputable theory

open module.free polynomial matrix

namespace linear_map

section basic

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : polynomial R :=
(to_matrix (choose_basis R M) (choose_basis R M) f).charpoly

lemma charpoly_def :
  f.charpoly = (to_matrix (choose_basis R M) (choose_basis R M) f).charpoly := rfl

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp] lemma charpoly_to_matrix {ι : Type w} [fintype ι] (b : basis ι R M) :
  (to_matrix b b f).charpoly = f.charpoly :=
begin
  set A := to_matrix b b f,
  set b' := choose_basis R M,
  set ι' := choose_basis_index R M,
  set A' := to_matrix b' b' f,
  set e := basis.index_equiv b b',
  set φ := reindex_linear_equiv R R e e,
  set φ₁ := reindex_linear_equiv R R e (equiv.refl ι'),
  set φ₂ := reindex_linear_equiv R R (equiv.refl ι') (equiv.refl ι'),
  set φ₃ := reindex_linear_equiv R R (equiv.refl ι') e,
  set P := b.to_matrix b',
  set Q := b'.to_matrix b,

  have hPQ : C.map_matrix (φ₁ P) ⬝ (C.map_matrix (φ₃ Q)) = 1,
  { rw [ring_hom.map_matrix_apply, ring_hom.map_matrix_apply, ← matrix.map_mul, ←
      @reindex_linear_equiv_mul _ ι' _ _ _ _ R R, basis.to_matrix_mul_to_matrix_flip,
      reindex_linear_equiv_one, ← ring_hom.map_matrix_apply, ring_hom.map_one] },

  calc A.charpoly = (reindex e e A).charpoly : (charpoly_reindex _ _).symm
  ... = (scalar ι' X - C.map_matrix (φ A)).det : rfl
  ... = (scalar ι' X - C.map_matrix (φ (P ⬝ A' ⬝ Q))).det :
    by rw [basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix]
  ... = (scalar ι' X - C.map_matrix (φ₁ P ⬝ φ₂ A' ⬝ φ₃ Q)).det :
    by rw [reindex_linear_equiv_mul R R _ _ e, reindex_linear_equiv_mul R R e _ _]
  ... = (scalar ι' X - (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det : by simp
  ... = (scalar ι' X ⬝ C.map_matrix (φ₁ P) ⬝ (C.map_matrix (φ₃ Q)) -
    (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det :
      by { rw [matrix.mul_assoc ((scalar ι') X), hPQ, matrix.mul_one] }
  ... = (C.map_matrix (φ₁ P) ⬝ scalar ι' X ⬝ (C.map_matrix (φ₃ Q)) -
    (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det : by simp
  ... = (C.map_matrix (φ₁ P) ⬝ (scalar ι' X - C.map_matrix A') ⬝ C.map_matrix (φ₃ Q)).det :
    by rw [← matrix.sub_mul, ← matrix.mul_sub]
  ... = (C.map_matrix (φ₁ P)).det * (scalar ι' X - C.map_matrix A').det *
    (C.map_matrix (φ₃ Q)).det : by rw [det_mul, det_mul]
  ... = (C.map_matrix (φ₁ P)).det * (C.map_matrix (φ₃ Q)).det *
    (scalar ι' X - C.map_matrix A').det : by ring
  ... = (scalar ι' X - C.map_matrix A').det : by rw [← det_mul, hPQ, det_one, one_mul]
  ... = f.charpoly : rfl
end

end basic

section coeff

lemma charpoly_monic : f.charpoly.monic := charpoly_monic _

end coeff

section cayley_hamilton

/-- The Cayley-Hamilton Theorem, that the characteristic polynomial of a linear map, applied to
the linear map itself, is zero. -/
lemma aeval_self_charpoly : aeval f f.charpoly = 0 :=
begin
  apply (linear_equiv.map_eq_zero_iff (alg_equiv_matrix _).to_linear_equiv).1,
  rw [alg_equiv.to_linear_equiv_apply, ← alg_equiv.coe_alg_hom,
    ← polynomial.aeval_alg_hom_apply _ _ _, charpoly_def],
  exact aeval_self_charpoly _,
end

lemma is_integral : is_integral R f := ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

lemma minpoly_dvd_charpoly {K : Type u} {M : Type v} [field K] [add_comm_group M] [module K M]
  [finite_dimensional K M] (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
minpoly.dvd _ _ (aeval_self_charpoly f)

variable {f}

lemma charpoly_coeff_zero_of_injective (hf : function.injective f) : (minpoly R f).coeff 0 ≠ 0 :=
begin
  intro h,
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h,
  have hdegP : P.degree < (minpoly R f).degree,
  { rw [hP, mul_comm],
    refine degree_lt_degree_mul_X (λ h, _),
    rw [h, mul_zero] at hP,
    exact minpoly.ne_zero (is_integral f) hP },
  have hPmonic : P.monic,
  { suffices : (minpoly R f).monic,
    { rwa [monic.def, hP, mul_comm, leading_coeff_mul_X, ← monic.def] at this },
    exact minpoly.monic (is_integral f) },
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _,
  simp only [hP, mul_eq_comp, ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp, alg_hom.map_mul,
    zero_apply] at hzero,
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (ext hzero)),
end

end cayley_hamilton

end linear_map
