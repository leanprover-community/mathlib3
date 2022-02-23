/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.nonsingular_inverse
import algebra.star.unitary
import analysis.normed_space.basic
import data.complex.is_R_or_C

/-!
# The Unitary Group

This file defines elements of the unitary group `unitary_group n α`, where `α` is a `star_ring`.
This consists of all `n` by `n` matrices with entries in `α` such that the star-transpose is its
inverse. In addition, we define the group structure on `unitary_group n α`, and the embedding into
the general linear group `general_linear_group α (n → α)`.

We also define the orthogonal group `orthogonal_group n β`, where `β` is a `comm_ring`.

## Main Definitions

 * `matrix.unitary_group` is the type of matrices where the star-transpose is the inverse
 * `matrix.unitary_group.group` is the group structure (under multiplication)
 * `matrix.unitary_group.embedding_GL` is the embedding `unitary_group n α → GLₙ(α)`
 * `matrix.orthogonal_group` is the type of matrices where the transpose is the inverse

## References

 * https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/

universes u v

namespace matrix
open linear_map
open_locale matrix

section

variables (n : Type u) [decidable_eq n] [fintype n]
variables (α : Type v) [comm_ring α] [star_ring α]

/--
`unitary_group n` is the group of `n` by `n` matrices where the star-transpose is the inverse.
-/
abbreviation unitary_group := unitary (matrix n n α)

end

variables {n : Type u} [decidable_eq n] [fintype n]
variables {α : Type v} [comm_ring α] [star_ring α]

namespace unitary_group

instance coe_matrix : has_coe (unitary_group n α) (matrix n n α) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (unitary_group n α) (λ _, n → n → α) :=
{ coe := λ A, A.val }

/--
`to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `unitary_group n` is defined,
we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : unitary_group n α) := matrix.to_lin' A

lemma ext_iff (A B : unitary_group n α) : A = B ↔ ∀ i j, A i j = B i j :=
subtype.ext_iff_val.trans ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : unitary_group n α) : (∀ i j, A i j = B i j) → A = B :=
(unitary_group.ext_iff A B).mpr

@[simp]
lemma star_mul_self (A : unitary_group n α) : star A ⬝ A = 1 := A.2.1

section coe_lemmas

variables (A B : unitary_group n α)

@[simp] lemma inv_val : ↑(A⁻¹) = (star A : matrix n n α) := rfl

@[simp] lemma inv_apply : ⇑(A⁻¹) = (star A : matrix n n α) := rfl

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : unitary_group n α) = (1 : matrix n n α) := rfl

@[simp] lemma one_apply : ⇑(1 : unitary_group n α) = (1 : matrix n n α) := rfl

@[simp] lemma to_lin'_mul :
  to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one :
  to_lin' (1 : unitary_group n α) = linear_map.id :=
matrix.to_lin'_one

end coe_lemmas

/-- `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv (A : unitary_group n α) : (n → α) ≃ₗ[α] (n → α) :=
{ inv_fun := to_lin' A⁻¹,
  left_inv := λ x, calc
    (to_lin' A⁻¹).comp (to_lin' A) x
        = (to_lin' (A⁻¹ * A)) x : by rw [←to_lin'_mul]
    ... = x : by rw [mul_left_inv, to_lin'_one, id_apply],
  right_inv := λ x, calc
    (to_lin' A).comp (to_lin' A⁻¹) x
        = to_lin' (A * A⁻¹) x : by rw [←to_lin'_mul]
    ... = x : by rw [mul_right_inv, to_lin'_one, id_apply],
  ..matrix.to_lin' A }

/-- `to_GL` is the map from the unitary group to the general linear group -/
def to_GL (A : unitary_group n α) : general_linear_group α (n → α) :=
general_linear_group.of_linear_equiv (to_linear_equiv A)

lemma coe_to_GL (A : unitary_group n α) :
  ↑(to_GL A) = to_lin' A :=
rfl

@[simp]
lemma to_GL_one : to_GL (1 : unitary_group n α) = 1 :=
by { ext1 v i, rw [coe_to_GL, to_lin'_one], refl }

@[simp]
lemma to_GL_mul (A B : unitary_group n α) :
  to_GL (A * B) = to_GL A * to_GL B :=
by { ext1 v i, rw [coe_to_GL, to_lin'_mul], refl }

/-- `unitary_group.embedding_GL` is the embedding from `unitary_group n α`
to `general_linear_group n α`. -/
def embedding_GL : unitary_group n α →* general_linear_group α (n → α) :=
⟨λ A, to_GL A, by simp, by simp⟩

section norm
variables {𝕜 : Type*} [is_R_or_C 𝕜]
local attribute [instance] matrix.normed_group

open_locale big_operators

/-- The entrywise sup norm of a unitary matrix is at most 1. -/
lemma entrywise_sup_norm_bound_of_unitary {U : matrix n n 𝕜} (hU : U ∈ matrix.unitary_group n 𝕜) :
  ∥ U ∥ ≤ 1 :=
begin
  rw pi_norm_le_iff zero_le_one,
  intro i,
  rw pi_norm_le_iff zero_le_one,
  intro j,
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ∥ U i j ∥^2 ≤ (∑ (x : n), ∥ U i x ∥^2),
  { apply multiset.single_le_sum,
  { intros x h_x,
    rw multiset.mem_map at h_x,
    cases h_x with a h_a,
    rw ← h_a.2,
    apply sq_nonneg },
  { rw multiset.mem_map,
    use j,
    simp only [eq_self_iff_true, finset.mem_univ_val, and_self, sq_eq_sq] } },
  -- The L2 norm of a row is a diagonal entry of U ⬝ Uᴴ
  have diag_eq_norm_sum : (U ⬝ Uᴴ) i i = ∑ (x : n), ∥ U i x ∥^2,
  { simp only [matrix.mul_apply, matrix.conj_transpose_apply, ← star_ring_end_apply],
    conv_lhs
    begin
      congr,
      skip,
      funext,
      rw [is_R_or_C.mul_conj, is_R_or_C.norm_sq_eq_def'],
    end,
    norm_cast,
  },
  -- The L2 norm of a row is a diagonal entry of U ⬝ Uᴴ, real part
  have re_diag_eq_norm_sum : is_R_or_C.re ((U ⬝ Uᴴ) i i) = ∑ (x : n), ∥ U i x ∥^2,
  {
    rw is_R_or_C.ext_iff at diag_eq_norm_sum,
    rw diag_eq_norm_sum.1,
    norm_cast,
  },
  -- Since U is unitary, the diagonal entries of U ⬝ Uᴴ are all 1
  have mul_eq_one : (U ⬝ Uᴴ) = 1, from unitary.mul_star_self_of_mem hU,
  have diag_eq_one : is_R_or_C.re ((U ⬝ Uᴴ) i i) = 1,
  {simp only [mul_eq_one, eq_self_iff_true, matrix.one_apply_eq, is_R_or_C.one_re]},
  -- Putting it all together
  rw ← sq_le_one_iff (norm_nonneg (U i j)),
  rw ← diag_eq_one,
  rw re_diag_eq_norm_sum,
  exact norm_sum,
end

end norm

end unitary_group

section orthogonal_group

variables (β : Type v) [comm_ring β]

local attribute [instance] star_ring_of_comm
/--
`orthogonal_group n` is the group of `n` by `n` matrices where the transpose is the inverse.
-/
abbreviation orthogonal_group := unitary_group n β

end orthogonal_group

end matrix
