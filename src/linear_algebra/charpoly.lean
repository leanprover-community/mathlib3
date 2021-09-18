/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module
import linear_algebra.charpoly.coeff
import linear_algebra.matrix.basis
import linear_algebra.dimension

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a free `R`-module.

## Main definition

* `charpoly f` : the characteristic polynomial of `f`.

-/

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : M →ₗ[R] M)

open_locale classical

noncomputable theory

open module.free polynomial

section basic

namespace linear_map

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly := (linear_map.to_matrix (choose_basis R M) (choose_basis R M) f).charpoly

lemma charpoly_def :
  f.charpoly = (linear_map.to_matrix (choose_basis R M) (choose_basis R M) f).charpoly := rfl

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
--Is adding [fintype ι] by hand OK?
lemma charpoly_eq_matrix.charpoly {ι : Type w} [fintype ι] (b : basis ι R M) :
  f.charpoly = (linear_map.to_matrix b b f).charpoly :=
begin
  let b' := choose_basis R M,
  let e := nonempty.some
    (cardinal.lift_mk_eq.1 (cardinal.lift_max.2 (mk_eq_mk_of_basis b' b))),
  simp only [linear_map.charpoly.equations._eqn_1, matrix.coe_scalar,
    matrix.charpoly.equations._eqn_1, ring_hom.map_matrix_apply, charmatrix.equations._eqn_1],
  rw [← linear_map_to_matrix_mul_basis_to_matrix b' b b' f,
    ← basis_to_matrix_mul_linear_map_to_matrix b b' b f, ← matrix.det_reindex_self e _,
    ← matrix.reindex_alg_equiv_apply, alg_equiv.map_sub],

  set φ := matrix.reindex_alg_equiv (polynomial R) e,
  set A := (to_matrix b b) f with hA,
  set P := b'.to_matrix b,
  set Q := b.to_matrix b',
  rw [← hA],


  sorry
end

/-- The Cayley-Hamilton Theorem, that the characteristic polynomial of a linear map, applied to
the linear map itself, is zero. -/
lemma aeval_self_charpoly : aeval f f.charpoly = 0 :=
begin
  apply (linear_equiv.map_eq_zero_iff (alg_equiv_matrix _).to_linear_equiv).1,
  rw [alg_equiv.to_linear_equiv_apply, ← alg_equiv.coe_alg_hom,
    ← polynomial.aeval_alg_hom_apply _ _ _, charpoly_def],
  exact aeval_self_char_poly _,
end

end linear_map

end basic
