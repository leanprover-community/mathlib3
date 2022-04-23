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

In this file, we provide results about `exp` on `matrix`s over a normed algebra.

This file exists because lemmas like `exp_add_of_commute` require a canonical norm on the type, but
for matrices there are multiple sensible choices of norm, none of which are canonical. In this file,
we copy across the lemmas about a `exp` and instantiate a non-canonical norm in the proof.

* `matrix.exp_add_of_commute`
* `matrix.exp_nsmul`

After this, we prove some additional results about matrix operations:

* `matrix.exp_diagonal`
* `matrix.exp_block_diagonal`
* `matrix.exp_block_diagonal'`

-/

variables (𝕂 : Type*) {m n : Type*} {n' : m → Type*} {𝔸 : Type*}
  [is_R_or_C 𝕂]
  [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n]
  [Π i, fintype (n' i)] [Π i, decidable_eq (n' i)]
  [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

section hacks_for_typeclass_resolution

/-- TODO: are these needed?
/-- A special case of `pi.algebra` for non-dependent types. Lean get stuck on the definition
below without this. -/
instance function.algebra (I : Type*) {R : Type*} (A : Type*) {r : comm_semiring R}
  [semiring A] [algebra R A] : algebra R (I → A) :=
pi.algebra _ _

instance function.topological_ring (I : Type*) (R : Type*) [ring R] [topological_space R]
  [topological_ring R] :
  topological_ring (I → R) :=
pi.topological_ring

instance function.has_continuous_const_smul (I : Type*) (R : Type*) (M : Type*) [has_scalar R M]
  [topological_space M] [has_continuous_const_smul R M] :
  has_continuous_const_smul R (I → M) :=
pi.has_continuous_const_smul
-/

instance pi.matrix_algebra : algebra 𝕂 (Π i : m, matrix (n' i) (n' i) 𝔸) :=
@pi.algebra m 𝕂 (λ i, matrix (n' i) (n' i) 𝔸) _ _ (λ i, matrix.algebra)

instance pi.matrix_topological_ring :
  topological_ring (Π i : m, matrix (n' i) (n' i) 𝔸) :=
@pi.topological_ring _ (λ i, matrix (n' i) (n' i) 𝔸) _ _ (λ i, matrix.topological_ring)

instance pi.matrix_has_continuous_const_smul :
  has_continuous_const_smul 𝕂 (Π i : m, matrix (n' i) (n' i) 𝔸) :=
@pi.has_continuous_const_smul _ _ (λ i, matrix (n' i) (n' i) 𝔸) _ _
  (λ i, matrix.has_continuous_const_smul)

end hacks_for_typeclass_resolution

namespace matrix

local attribute [instance] matrix.subsingleton_of_empty_left

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

lemma exp_diagonal (v : m → 𝔸) :
  exp 𝕂 _ (diagonal v) = diagonal (exp 𝕂 (m → 𝔸) v) :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  letI : normed_algebra 𝕂 (m → 𝔸) := by apply_instance,
  refine (map_exp 𝕂 (diagonal_ring_hom m 𝔸) _ _).symm,
  exact continuous_matrix.diagonal continuous_id,
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

lemma exp_block_diagonal' {n : m → Type*} [Π i, fintype (n i)]
  [Π i, decidable_eq (n i)] (v : Π i, matrix (n' i) (n' i) 𝔸) :
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

end matrix
