/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module
import linear_algebra.charpoly.coeff
import linear_algebra.matrix.basis

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a free `R`-module.

## Main definition

* `linear_map.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : M →ₗ[R] M)

open_locale classical

noncomputable theory

open module.free polynomial matrix

namespace linear_map

section basic

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : polynomial R :=
(linear_map.to_matrix (choose_basis R M) (choose_basis R M) f).charpoly

lemma charpoly_def :
  f.charpoly = (linear_map.to_matrix (choose_basis R M) (choose_basis R M) f).charpoly := rfl

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp] lemma charpoly_to_matrix {ι : Type w} [fintype ι] (b : basis ι R M) :
  (linear_map.to_matrix b b f).charpoly = f.charpoly :=
begin
  set b' := choose_basis R M,
  set P := reindex_linear_equiv R R (basis.index_equiv b' b) (equiv.refl ι) (b'.to_matrix b),
  set Q := reindex_linear_equiv R R (equiv.refl ι) (basis.index_equiv b' b) (b.to_matrix b'),

  have hPQ : (P.map C).mul (Q.map C) = 1,
  { rw [← matrix.map_mul, ← reindex_linear_equiv_mul R R, basis.to_matrix_mul_to_matrix_flip,
      reindex_linear_equiv_one, ← ring_hom.map_matrix_apply, ring_hom.map_one],
    apply_instance },
  have hscalar : (scalar ι) X = (((scalar ι) X).mul (P.map C)).mul (Q.map C),
  { rw [matrix.mul_assoc ((scalar ι) X), hPQ, matrix.mul_one] },
  have hcomm : ((scalar ι) X).mul (P.map C) = (P.map C).mul ((scalar ι) X) := by simp,

  rw [charpoly, ← charpoly_of_reindex (basis.index_equiv (choose_basis R M) b), matrix.charpoly,
    charmatrix, ← linear_map_to_matrix_mul_basis_to_matrix b' b b' f,
    ← basis_to_matrix_mul_linear_map_to_matrix b b' b f, ← reindex_linear_equiv_apply R R,
    reindex_linear_equiv_mul R R _ (equiv.refl ι) _,
    reindex_linear_equiv_mul R R _ (equiv.refl ι) (equiv.refl ι),
    reindex_linear_equiv_refl_refl, linear_equiv.refl_apply, ring_hom.map_matrix_apply,
    matrix.map_mul, matrix.map_mul, hscalar, hcomm, ← matrix.sub_mul, ← matrix.mul_sub,
    det_mul, matrix.det_mul, mul_comm (P.map C).det, mul_assoc, ← det_mul, hPQ, det_one, mul_one],
  refl
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
  [finite_dimensional K M] (f : M →ₗ[K] M) : (minpoly K f) ∣ f.charpoly :=
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
