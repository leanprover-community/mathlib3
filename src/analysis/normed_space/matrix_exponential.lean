/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import analysis.normed_space.exponential
import analysis.matrix
import linear_algebra.matrix.zpow
import topology.uniform_space.matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `exp` on `matrix`s over a topological or normed algebra.
Note that generic results over all topological spaces such as `exp_zero` can be used on matrices
without issue, so are not repeated here. The topological results specific to matrices are:

* `matrix.exp_transpose`
* `matrix.exp_conj_transpose`
* `matrix.exp_diagonal`
* `matrix.exp_block_diagonal`
* `matrix.exp_block_diagonal'`

Lemmas like `exp_add_of_commute` require a canonical norm on the type; while there are multiple
sensible choices for the norm of a `matrix` (`matrix.normed_group`, `matrix.frobenius_normed_group`,
`matrix.linfty_op_normed_group`), none of them are canonical. In an application where a particular
norm is chosen using `local attribute [instance]`, then the usual lemmas about `exp` are fine. When
choosing a norm is undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `exp`, but hide the requirement for a norm inside the
proof.

* `matrix.exp_add_of_commute`
* `matrix.exp_sum_of_commute`
* `matrix.exp_nsmul`
* `matrix.is_unit_exp`
* `matrix.exp_units_conj`
* `matrix.exp_units_conj'`

Additionally, we prove some results about `matrix.has_inv` and `matrix.div_inv_monoid`, as the
results for general rings are instead stated about `ring.inverse`:

* `matrix.exp_neg`
* `matrix.exp_zsmul`
* `matrix.exp_conj`
* `matrix.exp_conj'`

## Implementation notes

This file runs into some sharp edges on typeclass search in lean 3, especially regarding pi types.
To work around this, we copy a handful of instances for when lean can't find them by itself.
Hopefully we will be able to remove these in Lean 4.

## TODO

* Show that `matrix.det (exp 𝕂 A) = exp 𝕂 (matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/
open_locale matrix big_operators

section hacks_for_pi_instance_search

/-- A special case of `pi.topological_ring` for when `R` is not dependently typed. -/
instance function.topological_ring (I : Type*) (R : Type*)
  [non_unital_ring R] [topological_space R] [topological_ring R] :
  topological_ring (I → R) :=
pi.topological_ring

/-- A special case of `function.algebra` for when A is a `ring` not a `semiring` -/
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

end hacks_for_pi_instance_search

variables (𝕂 : Type*) {m n p : Type*} {n' : m → Type*} {𝔸 : Type*}

namespace matrix

section topological

section ring
variables [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
  [Π i, fintype (n' i)] [Π i, decidable_eq (n' i)]
  [field 𝕂] [ring 𝔸] [topological_space 𝔸] [topological_ring 𝔸] [algebra 𝕂 𝔸] [t2_space 𝔸]

lemma exp_diagonal (v : m → 𝔸) : exp 𝕂 (diagonal v) = diagonal (exp 𝕂 v) :=
by simp_rw [exp_eq_tsum, diagonal_pow, ←diagonal_smul, ←diagonal_tsum]

lemma exp_block_diagonal (v : m → matrix n n 𝔸) :
  exp 𝕂 (block_diagonal v) = block_diagonal (exp 𝕂 v) :=
by simp_rw [exp_eq_tsum, ←block_diagonal_pow, ←block_diagonal_smul, ←block_diagonal_tsum]

lemma exp_block_diagonal' (v : Π i, matrix (n' i) (n' i) 𝔸) :
  exp 𝕂 (block_diagonal' v) = block_diagonal' (exp 𝕂 v) :=
by simp_rw [exp_eq_tsum, ←block_diagonal'_pow, ←block_diagonal'_smul, ←block_diagonal'_tsum]

lemma exp_conj_transpose [star_ring 𝔸] [has_continuous_star 𝔸] (A : matrix m m 𝔸) :
  exp 𝕂 Aᴴ = (exp 𝕂 A)ᴴ :=
(star_exp A).symm

end ring

section comm_ring
variables [fintype m] [decidable_eq m] [field 𝕂]
  [comm_ring 𝔸] [topological_space 𝔸] [topological_ring 𝔸] [algebra 𝕂 𝔸] [t2_space 𝔸]

lemma exp_transpose (A : matrix m m 𝔸) : exp 𝕂 Aᵀ = (exp 𝕂 A)ᵀ :=
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
  exp 𝕂 (A + B) = exp 𝕂 A ⬝ exp 𝕂 B :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact exp_add_of_commute h,
end

lemma exp_sum_of_commute {ι} (s : finset ι) (f : ι → matrix m m 𝔸)
  (h : ∀ (i ∈ s) (j ∈ s), commute (f i) (f j)) :
  exp 𝕂 (∑ i in s, f i) = s.noncomm_prod (λ i, exp 𝕂 (f i))
    (λ i hi j hj, (h i hi j hj).exp 𝕂) :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact exp_sum_of_commute s f h,
end

lemma exp_nsmul (n : ℕ) (A : matrix m m 𝔸) :
  exp 𝕂 (n • A) = exp 𝕂 A ^ n :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact exp_nsmul n A,
end

lemma is_unit_exp (A : matrix m m 𝔸) : is_unit (exp 𝕂 A) :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact is_unit_exp _ A,
end

lemma exp_units_conj (U : (matrix m m 𝔸)ˣ) (A : matrix m m 𝔸)  :
  exp 𝕂 (↑U ⬝ A ⬝ ↑(U⁻¹) : matrix m m 𝔸) = ↑U ⬝ exp 𝕂 A ⬝ ↑(U⁻¹) :=
begin
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact exp_units_conj _ U A,
end

lemma exp_units_conj' (U : (matrix m m 𝔸)ˣ) (A : matrix m m 𝔸)  :
  exp 𝕂 (↑(U⁻¹) ⬝ A ⬝ U : matrix m m 𝔸) = ↑(U⁻¹) ⬝ exp 𝕂 A ⬝ U :=
exp_units_conj 𝕂 U⁻¹ A

end normed

section normed_comm

variables [is_R_or_C 𝕂]
  [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n]
  [Π i, fintype (n' i)] [Π i, decidable_eq (n' i)]
  [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

lemma exp_neg (A : matrix m m 𝔸) : exp 𝕂 (-A) = (exp 𝕂 A)⁻¹ :=
begin
  rw nonsing_inv_eq_ring_inverse,
  letI : semi_normed_ring (matrix m m 𝔸) := matrix.linfty_op_semi_normed_ring,
  letI : normed_ring (matrix m m 𝔸) := matrix.linfty_op_normed_ring,
  letI : normed_algebra 𝕂 (matrix m m 𝔸) := matrix.linfty_op_normed_algebra,
  exact (ring.inverse_exp _ A).symm,
end

lemma exp_zsmul (z : ℤ) (A : matrix m m 𝔸) : exp 𝕂 (z • A) = exp 𝕂 A ^ z :=
begin
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
  { rw [zpow_coe_nat, coe_nat_zsmul, exp_nsmul] },
  { have : is_unit (exp 𝕂 A).det := (matrix.is_unit_iff_is_unit_det _).mp (is_unit_exp _ _),
    rw [matrix.zpow_neg this, zpow_coe_nat, neg_smul,
        exp_neg, coe_nat_zsmul, exp_nsmul] },
end

lemma exp_conj (U : matrix m m 𝔸) (A : matrix m m 𝔸) (hy : is_unit U) :
  exp 𝕂 (U ⬝ A ⬝ U⁻¹) = U ⬝ exp 𝕂 A ⬝ U⁻¹ :=
let ⟨u, hu⟩ := hy in hu ▸ by simpa only [matrix.coe_units_inv] using exp_units_conj 𝕂 u A

lemma exp_conj' (U : matrix m m 𝔸) (A : matrix m m 𝔸) (hy : is_unit U) :
  exp 𝕂 (U⁻¹ ⬝ A ⬝ U) = U⁻¹ ⬝ exp 𝕂 A ⬝ U :=
let ⟨u, hu⟩ := hy in hu ▸ by simpa only [matrix.coe_units_inv] using exp_units_conj' 𝕂 u A

end normed_comm

end matrix
