/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

import linear_algebra.matrix.determinant

/-!
# Changing the index type of a matrix

This file concerns the map `matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `matrix.reindex_linear_equiv`: `matrix.reindex` is a linear equivalence
* `matrix.reindex_alg_equiv`: `matrix.reindex` is a algebra equivalence

## Tags

matrix, reindex

-/

namespace matrix

open_locale matrix

variables {l m n : Type*} [fintype l] [fintype m] [fintype n]
variables {l' m' n' : Type*} [fintype l'] [fintype m'] [fintype n']
variables {R : Type*}

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`matrix.reindex`, is a linear equivalence. -/
def reindex_linear_equiv [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') :
  matrix m n R ≃ₗ[R] matrix m' n' R :=
{ map_add'  := λ M N, rfl,
  map_smul' := λ M N, rfl,
  ..(reindex eₘ eₙ)}

@[simp] lemma reindex_linear_equiv_apply [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  reindex_linear_equiv eₘ eₙ M = reindex eₘ eₙ M :=
rfl

@[simp] lemma reindex_linear_equiv_symm [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') :
  (reindex_linear_equiv eₘ eₙ : _ ≃ₗ[R] _).symm = reindex_linear_equiv eₘ.symm eₙ.symm :=
rfl

@[simp] lemma reindex_linear_equiv_refl_refl [semiring R] :
  reindex_linear_equiv (equiv.refl m) (equiv.refl n) = linear_equiv.refl R _ :=
linear_equiv.ext $ λ _, rfl

lemma reindex_linear_equiv_mul {o o' : Type*} [fintype o] [fintype o'] [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o') (M : matrix m n R) (N : matrix n o R) :
  reindex_linear_equiv eₘ eₒ (M ⬝ N) =
    reindex_linear_equiv eₘ eₙ M ⬝ reindex_linear_equiv eₙ eₒ N :=
minor_mul_equiv M N _ _ _

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `matrix.reindex`, is an equivalence of algebras. -/
def reindex_alg_equiv [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) : matrix m m R ≃ₐ[R] matrix n n R :=
{ to_fun    := reindex e e,
  map_mul'  := reindex_linear_equiv_mul e e e,
  commutes' := λ r, by simp [algebra_map, algebra.to_ring_hom, minor_smul],
  ..(reindex_linear_equiv e e) }

@[simp] lemma reindex_alg_equiv_apply [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) :
  reindex_alg_equiv e M = reindex e e M :=
rfl

@[simp] lemma reindex_alg_equiv_symm [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) :
  (reindex_alg_equiv e : _ ≃ₐ[R] _).symm = reindex_alg_equiv e.symm :=
rfl

@[simp] lemma reindex_alg_equiv_refl [comm_semiring R] [decidable_eq m] :
  reindex_alg_equiv (equiv.refl m) = (alg_equiv.refl : _ ≃ₐ[R] _) :=
alg_equiv.ext $ λ _, rfl

lemma reindex_alg_equiv_mul [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) (N : matrix m m R) :
  reindex_alg_equiv e (M ⬝ N) = reindex_alg_equiv e M ⬝ reindex_alg_equiv e N :=
(reindex_alg_equiv e).map_mul M N

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
lemma det_reindex_linear_equiv_self [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_linear_equiv e e A) = det A :=
det_reindex_self e A

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
lemma det_reindex_alg_equiv [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_alg_equiv e A) = det A :=
det_reindex_self e A

end matrix
