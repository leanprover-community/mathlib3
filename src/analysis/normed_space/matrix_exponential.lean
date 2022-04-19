/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import analysis.normed_space.exponential
import analysis.matrix

/-!
# Lemmas about the matrix Exponential
-/

-- from Heather
section
variables (𝕜 : Type*) [uniform_space 𝕜]
variables (n : Type*) [fintype n] [decidable_eq n] (m : Type*) [fintype m] [decidable_eq m]

instance : uniform_space (matrix n m 𝕜) := Pi.uniform_space (λ i, m → 𝕜)

instance [complete_space 𝕜] : complete_space (matrix n m 𝕜) := Pi.complete (λ i, m → 𝕜)

end

namespace matrix

variables (m n 𝕂 𝔸 : Type*) [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n] [complete_space 𝔸]

local attribute [instance] matrix.subsingleton_of_empty_left

lemma exp_add_of_commute (A B : matrix m m 𝔸) (h : commute A B) :
  exp 𝕂 _ (A + B) = exp 𝕂 _ A * exp 𝕂 _ B :=
begin
  casesI is_empty_or_nonempty m,
  { simp },
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.l0_linf_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.l0_linf_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.l0_linf_normed_algebra,
  exact exp_add_of_commute h,
end

lemma exp_nsmul (n : ℕ) (A : matrix m m 𝔸) :
  exp 𝕂 _ (n • A) = exp 𝕂 _ A ^ n :=
begin
  casesI is_empty_or_nonempty m,
  { simp },
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.l0_linf_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.l0_linf_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.l0_linf_normed_algebra,
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
  casesI is_empty_or_nonempty m,
  { simp },
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.l0_linf_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.l0_linf_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.l0_linf_normed_algebra,
  simp_rw ←diagonal_ring_hom_apply,
  -- timeout :(
  -- have := map_exp 𝕂 (diagonal_ring_hom m 𝔸),
  sorry
end

instance : topological_ring (m → matrix n n 𝔸) :=
@pi.topological_ring _ _ _ _ (λ i, matrix.topological_ring)

instance : algebra 𝕂 (m → matrix n n 𝔸) := function.algebra _ _

instance : has_continuous_const_smul 𝕂 (m → matrix n n 𝔸) :=
@pi.has_continuous_const_smul _ _ _ _ _ (λ i, matrix.has_continuous_const_smul)

lemma exp_block_diagonal (v : m → matrix n n 𝔸) :
  exp 𝕂 _ (block_diagonal v) = block_diagonal (exp 𝕂 (m → matrix n n 𝔸) v) :=
begin
  casesI is_empty_or_nonempty m,
  { simp },
  casesI is_empty_or_nonempty n,
  { simp },
  letI : semi_normed_ring (matrix n n 𝔸) := matrix.l0_linf_semi_normed_ring,
  letI : normed_ring (matrix n n 𝔸) := matrix.l0_linf_normed_ring,
  letI : normed_algebra 𝕂 (matrix n n 𝔸) := matrix.l0_linf_normed_algebra,
  letI : semi_normed_ring (matrix (n × m) (n × m) 𝔸) := matrix.l0_linf_semi_normed_ring,
  letI : normed_ring (matrix (n × m) (n × m) 𝔸) := matrix.l0_linf_normed_ring,
  letI : normed_algebra 𝕂 (matrix (n × m) (n × m) 𝔸) := matrix.l0_linf_normed_algebra,
  simp_rw ←block_diagonal_ring_hom_apply,
  -- -- timeout :(
  -- have := map_exp 𝕂 (block_diagonal_ring_hom n m 𝔸),
end

end matrix
