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

-/

namespace matrix

variables (m n 𝕂 𝔸 : Type*) [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] [complete_space 𝔸]

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

/-- A special case of `pi.algebra` for non-dependent types. Lean get stuck on the definition
below without this. -/
instance _root_.function.algebra (I : Type*) {R : Type*} (A : Type*) {r : comm_semiring R}
  [semiring A] [algebra R A] : algebra R (I → A) :=
pi.algebra _ _

instance _root_.why : algebra 𝕂 (m → 𝔸) := function.algebra _ _

lemma exp_diagonal (v : m → 𝔸) :
  exp 𝕂 _ (diagonal v) = diagonal (exp 𝕂 (m → 𝔸) v) :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  letI : normed_algebra 𝕂 (m → 𝔸) := pi.normed_algebra _,
  refine (map_exp 𝕂 (diagonal_ring_hom m 𝔸) _ _).symm,
  exact continuous_matrix.diagonal continuous_id,
end

instance : topological_ring (m → matrix n n 𝔸) :=
@pi.topological_ring _ _ _ _ (λ i, matrix.topological_ring)

instance : algebra 𝕂 (m → matrix n n 𝔸) := function.algebra _ _

instance : has_continuous_const_smul 𝕂 (m → matrix n n 𝔸) :=
@pi.has_continuous_const_smul _ _ _ _ _ (λ i, matrix.has_continuous_const_smul)

lemma exp_block_diagonal (v : m → matrix n n 𝔸) :
  exp 𝕂 _ (block_diagonal v) = block_diagonal (exp 𝕂 (m → matrix n n 𝔸) v) :=
begin
  letI : semi_normed_ring (matrix n n 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix n n 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix n n 𝔸) := matrix.linfty_op_normed_algebra,
  letI : semi_normed_ring (matrix (n × m) (n × m) 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix (n × m) (n × m) 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix (n × m) (n × m) 𝔸) := matrix.linfty_op_normed_algebra,
  letI : complete_space (m → matrix n n 𝔸) := by apply_instance,
  refine (map_exp 𝕂 (block_diagonal_ring_hom n m 𝔸) _ v).symm,
  exact continuous_id.block_diagonal,
end

end matrix
