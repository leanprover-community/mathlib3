/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import analysis.normed_space.exponential
import analysis.matrix
import topology.uniform_space.matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `exp` on `matrix`s over a topological or normed algebra.
The topological results are:

* `matrix.exp_transpose`
* `matrix.exp_diagonal`

Lemmas `exp_add_of_commute` require a canonical norm on the type, but for matrices there are
multiple sensible choices of norm, none of which are canonical. In an application where you choose
a particular norm using `local attribute [instance]`, then the usual lemmas about `exp` are fine.

In this file, we copy across the lemmas about a `exp` and instantiate a non-canonical norm in the
proof.

* `matrix.exp_add_of_commute`
* `matrix.exp_nsmul`

After this, we prove some additional results about matrix operations:

* `matrix.exp_block_diagonal`
* `matrix.exp_block_diagonal'`

-/
open_locale matrix

section hacks_for_pi_instance_search

/-- A special case of `pi.topological_ring` for when `R` is not dependently typed. -/
instance function.topological_ring (I : Type*) (R : Type*)
  [non_unital_ring R] [topological_space R] [topological_ring R] :
  topological_ring (I → R) :=
pi.topological_ring

/-- A special case of `pi.has_continuous_const_smul` for when `M` is not dependently typed. -/
instance function.has_continuous_const_smul (I : Type*) (R : Type*) (M : Type*) [has_scalar R M]
  [topological_space M] [has_continuous_const_smul R M] :
  has_continuous_const_smul R (I → M) :=
pi.has_continuous_const_smul

/-- A special case of `function.algebra` for when A is a ring not a semiring -/
instance function.algebra_ring (I : Type*) {R : Type*} (A : Type*) [comm_semiring R]
  [ring A] [algebra R A] : algebra R (I → A) :=
pi.algebra _ _

/-- A special case of `pi.algebra` for when `f = λ i, matrix (m i) (m i) A`. -/
instance pi.matrix_algebra (I R A : Type*) (m : I → Type*)
  [comm_semiring R] [semiring A] [algebra R A]
  [Π i, fintype (m i)] [Π i, decidable_eq (m i)] :
  algebra R (Π i, matrix (m i) (m i) A) :=
@pi.algebra I R (λ i, matrix (m i) (m i) A) _ _ (λ i, matrix.algebra)

/-- A special case of `pi.topological_ring` for when `f = λ i, matrix (m i) (m i) A`. -/
instance pi.matrix_topological_ring (I A : Type*) (m : I → Type*)
  [ring A] [topological_space A] [topological_ring A]
  [Π i, fintype (m i)] :
  topological_ring (Π i, matrix (m i) (m i) A) :=
@pi.topological_ring _ (λ i, matrix (m i) (m i) A) _ _ (λ i, matrix.topological_ring)

instance pi.matrix_has_continuous_const_smul (I R A : Type*) (m : I → Type*)
  [topological_space A] [has_scalar R A] [has_continuous_const_smul R A] :
  has_continuous_const_smul R (Π i, matrix (m i) (m i) A) :=
@pi.has_continuous_const_smul _ _ (λ i, matrix (m i) (m i) A) _ _
  (λ i, matrix.has_continuous_const_smul)

end hacks_for_pi_instance_search

variables (𝕂 : Type*) {m n : Type*} {n' : m → Type*} {𝔸 : Type*}

namespace matrix

section topological

section ring
variables [fintype m] [decidable_eq m] [field 𝕂]
  [ring 𝔸] [topological_space 𝔸] [topological_ring 𝔸] [algebra 𝕂 𝔸]
  [has_continuous_const_smul 𝕂 𝔸] [t2_space 𝔸]

lemma exp_diagonal (v : m → 𝔸) : exp 𝕂 _ (diagonal v) = diagonal (exp 𝕂 (m → 𝔸) v) :=
by simp_rw [exp_eq_tsum, diagonal_pow, ←diagonal_smul, ←diagonal_tsum]

/-! TODO: add a `has_continuous_star` typeclass so we can write
```lean
lemma exp_conj_transpose [star_ring 𝔸] [has_continuous_star 𝔸] (A : matrix m m 𝔸) :
  exp 𝕂 (matrix m m 𝔸) Aᴴ = (exp 𝕂 _ A)ᴴ :=
by simp_rw [exp_eq_tsum, conj_transpose_tsum, conj_transpose_smul, conj_transpose_pow]
```
-/

end ring

section comm_ring
variables [fintype m] [decidable_eq m] [field 𝕂]
  [comm_ring 𝔸] [topological_space 𝔸] [topological_ring 𝔸] [algebra 𝕂 𝔸]
  [has_continuous_const_smul 𝕂 𝔸] [t2_space 𝔸]

-- where's transpose_pow!?
lemma exp_transpose (A : matrix m m 𝔸) : exp 𝕂 (matrix m m 𝔸) Aᵀ = (exp 𝕂 _ A)ᵀ :=
by simp_rw [exp_eq_tsum, transpose_tsum, transpose_smul, transpose_pow]

end comm_ring

end topological

section normed

variables [is_R_or_C 𝕂]
  [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n]
  [Π i, fintype (n' i)] [Π i, decidable_eq (n' i)]
  [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

lemma exp_add_of_commute (A B : matrix m m 𝔸) (h : commute A B) :
  exp 𝕂 _ (A + B) = exp 𝕂 _ A * exp 𝕂 _ B :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact exp_add_of_commute h,
end

lemma exp_nsmul (n : ℕ) (A : matrix m m 𝔸) :
  exp 𝕂 _ (n • A) = exp 𝕂 _ A ^ n :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact exp_nsmul n A,
end

lemma exp_block_diagonal (v : m → matrix n n 𝔸) :
  exp 𝕂 _ (block_diagonal v) = block_diagonal (exp 𝕂 (m → matrix n n 𝔸) v) :=
begin
  -- pick the norm on the spaces of matrices
  letI : semi_normed_ring (matrix n n 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix n n 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix n n 𝔸) := matrix.linfty_op_normed_algebra,
  letI : semi_normed_ring (matrix (n × m) (n × m) 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix (n × m) (n × m) 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix (n × m) (n × m) 𝔸) := matrix.linfty_op_normed_algebra,
  -- help out lean which is bad at typeclass resolution on pi types
  letI : complete_space (m → matrix n n 𝔸) := by apply_instance,
  refine (map_exp 𝕂 (block_diagonal_ring_hom n m 𝔸) _ v).symm,
  exact continuous.matrix_block_diagonal continuous_id,
end

lemma exp_block_diagonal' (v : Π i, matrix (n' i) (n' i) 𝔸) :
  exp 𝕂 _ (block_diagonal' v) = block_diagonal' (exp 𝕂 (Π i, matrix (n' i) (n' i) 𝔸) v) :=
begin
  -- pick the norm on the spaces of matrices
  letI : Π i : m, semi_normed_ring (matrix (n' i) (n' i) 𝔸) :=
    λ i, matrix.linfty_op_semi_normed_ring,
  letI : Π i : m, normed_ring (matrix (n' i) (n' i) 𝔸) := λ i, matrix.linfty_op_normed_ring,
  letI : Π i : m, normed_algebra 𝕂 (matrix (n' i) (n' i) 𝔸) :=
    λ i, matrix.linfty_op_normed_algebra,
  letI : semi_normed_ring (matrix (Σ i, n' i) (Σ i, n' i) 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix (Σ i, n' i) (Σ i, n' i) 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix (Σ i, n' i) (Σ i, n' i) 𝔸) := matrix.linfty_op_normed_algebra,
  -- help out lean which is bad at typeclass resolution on pi types
  letI : normed_algebra 𝕂 (Π (i : m), matrix (n' i) (n' i) 𝔸) := by apply_instance,
  letI : complete_space (Π i, matrix (n' i) (n' i) 𝔸) := by apply_instance,
  refine (map_exp 𝕂 (block_diagonal'_ring_hom n' 𝔸) _ v).symm,
  exact continuous.matrix_block_diagonal' continuous_id,
end

end normed

end matrix
