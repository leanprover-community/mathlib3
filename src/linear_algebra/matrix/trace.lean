/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.basic

/-!
# Trace of a matrix

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `linear_algebra.trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/

open_locale big_operators matrix

namespace matrix

variables {ι m n p : Type*} {α R S : Type*}
variables [fintype m] [fintype n] [fintype p]

section add_comm_monoid
variables [add_comm_monoid R]

/-- The trace of a square matrix. For more bundled versions, see:
* `matrix.trace_add_monoid_hom`
* `matrix.trace_linear_map`
-/
def trace (A : matrix n n R) : R := ∑ i, diag A i

variables (n R)
@[simp] lemma trace_zero : trace (0 : matrix n n R) = 0 :=
(finset.sum_const (0 : R)).trans $ smul_zero _
variables {n R}

@[simp] lemma trace_add (A B : matrix n n R) : trace (A + B) = trace A + trace B :=
finset.sum_add_distrib

@[simp] lemma trace_smul [monoid α] [distrib_mul_action α R] (r : α) (A : matrix n n R) :
  trace (r • A) = r • trace A :=
finset.smul_sum.symm

@[simp] lemma trace_transpose (A : matrix n n R) : trace Aᵀ = trace A := rfl

@[simp] lemma trace_conj_transpose [star_add_monoid R] (A : matrix n n R) :
  trace Aᴴ = star (trace A) :=
(star_sum _ _).symm

variables (n α R)
/-- `matrix.trace` as an `add_monoid_hom` -/
@[simps]
def trace_add_monoid_hom : matrix n n R →+ R :=
{ to_fun := trace, map_zero' := trace_zero n R, map_add' := trace_add }

/-- `matrix.trace` as a `linear_map` -/
@[simps]
def trace_linear_map [semiring α] [module α R] : matrix n n R →ₗ[α] R :=
{ to_fun := trace, map_add' := trace_add, map_smul' := trace_smul }
variables {n α R}

@[simp] lemma trace_list_sum (l : list (matrix n n R)) : trace l.sum = (l.map trace).sum :=
map_list_sum (trace_add_monoid_hom n R) l

@[simp] lemma trace_multiset_sum (s : multiset (matrix n n R)) : trace s.sum = (s.map trace).sum :=
map_multiset_sum (trace_add_monoid_hom n R) s

@[simp] lemma trace_sum (s : finset ι) (f : ι → matrix n n R) :
  trace (∑ i in s, f i) = ∑ i in s, trace (f i) :=
map_sum (trace_add_monoid_hom n R) f s

end add_comm_monoid

section add_comm_group
variables [add_comm_group R]

@[simp] lemma trace_sub (A B : matrix n n R) : trace (A - B) = trace A - trace B :=
finset.sum_sub_distrib

@[simp] lemma trace_neg (A : matrix n n R) : trace (-A) = -trace A :=
finset.sum_neg_distrib

end add_comm_group

section one
variables [decidable_eq n] [add_comm_monoid_with_one R]

@[simp] lemma trace_one : trace (1 : matrix n n R) = fintype.card n :=
by simp_rw [trace, diag_one, pi.one_def, finset.sum_const, nsmul_one, finset.card_univ]

end one

section mul

@[simp] lemma trace_transpose_mul [add_comm_monoid R] [has_mul R]
  (A : matrix m n R) (B : matrix n m R) : trace (Aᵀ ⬝ Bᵀ) = trace (A ⬝ B) := finset.sum_comm

lemma trace_mul_comm [add_comm_monoid R] [comm_semigroup R] (A : matrix m n R) (B : matrix n m R) :
  trace (A ⬝ B) = trace (B ⬝ A) :=
by rw [←trace_transpose, ←trace_transpose_mul, transpose_mul]

lemma trace_mul_cycle [non_unital_comm_semiring R]
  (A : matrix m n R) (B : matrix n p R) (C : matrix p m R) :
  trace (A ⬝ B ⬝ C) = trace (C ⬝ A ⬝ B) :=
by rw [trace_mul_comm, matrix.mul_assoc]

lemma trace_mul_cycle' [non_unital_comm_semiring R]
  (A : matrix m n R) (B : matrix n p R) (C : matrix p m R) :
  trace (A ⬝ (B ⬝ C)) = trace (C ⬝ (A ⬝ B)) :=
by rw [←matrix.mul_assoc, trace_mul_comm]

@[simp] lemma trace_col_mul_row [non_unital_non_assoc_semiring R] (a b : n → R) :
  trace (col a ⬝ row b) = dot_product a b :=
by simp [dot_product, trace]

end mul

section fin
variables [add_comm_monoid R]

/-! ### Special cases for `fin n`

While `simp [fin.sum_univ_succ]` can prove these, we include them for convenience and consistency
with `matrix.det_fin_two` etc.
-/

@[simp] lemma trace_fin_zero (A : matrix (fin 0) (fin 0) R) : trace A = 0 :=
rfl

lemma trace_fin_one (A : matrix (fin 1) (fin 1) R) : trace A = A 0 0 :=
add_zero _

lemma trace_fin_two (A : matrix (fin 2) (fin 2) R) : trace A = A 0 0 + A 1 1 :=
congr_arg ((+) _) (add_zero (A 1 1))

lemma trace_fin_three (A : matrix (fin 3) (fin 3) R) : trace A = A 0 0 + A 1 1 + A 2 2 :=
by { rw [← add_zero (A 2 2), add_assoc], refl }

end fin

end matrix
