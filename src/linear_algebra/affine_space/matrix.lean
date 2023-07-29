/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.affine_space.basis
import linear_algebra.determinant

/-!
# Matrix results for barycentric co-ordinates

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Results about the matrix of barycentric co-ordinates for a family of points in an affine space, with
respect to some affine basis.
-/

open_locale affine big_operators matrix
open set

universes u₁ u₂ u₃ u₄

variables {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variables [add_comm_group V] [affine_space V P]

namespace affine_basis

section ring

variables [ring k] [module k V] (b : affine_basis ι k P)

/-- Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matrix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `basis.to_matrix`. -/
noncomputable def to_matrix {ι' : Type*} (q : ι' → P) : matrix ι' ι k :=
λ i j, b.coord j (q i)

@[simp] lemma to_matrix_apply {ι' : Type*} (q : ι' → P) (i : ι') (j : ι) :
  b.to_matrix q i j = b.coord j (q i) :=
rfl

@[simp] lemma to_matrix_self [decidable_eq ι] :
  b.to_matrix b = (1 : matrix ι ι k) :=
begin
  ext i j,
  rw [to_matrix_apply, coord_apply, matrix.one_eq_pi_single, pi.single_apply],
end

variables {ι' : Type*} [fintype ι'] [fintype ι] (b₂ : affine_basis ι k P)

lemma to_matrix_row_sum_one {ι' : Type*} (q : ι' → P) (i : ι') :
  ∑ j, b.to_matrix q i j = 1 :=
by simp

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine independent. -/
lemma affine_independent_of_to_matrix_right_inv [decidable_eq ι']
  (p : ι' → P) {A : matrix ι ι' k} (hA : (b.to_matrix p) ⬝ A = 1) : affine_independent k p :=
begin
  rw affine_independent_iff_eq_of_fintype_affine_combination_eq,
  intros w₁ w₂ hw₁ hw₂ hweq,
  have hweq' : (b.to_matrix p).vec_mul w₁ = (b.to_matrix p).vec_mul w₂,
  { ext j,
    change ∑ i, (w₁ i) • (b.coord j (p i)) = ∑ i, (w₂ i) • (b.coord j (p i)),
    rw [← finset.univ.affine_combination_eq_linear_combination _ _ hw₁,
        ← finset.univ.affine_combination_eq_linear_combination _ _ hw₂,
        ← finset.univ.map_affine_combination p w₁ hw₁,
        ← finset.univ.map_affine_combination p w₂ hw₂, hweq], },
  replace hweq' := congr_arg (λ w, A.vec_mul w) hweq',
  simpa only [matrix.vec_mul_vec_mul, ← matrix.mul_eq_mul, hA, matrix.vec_mul_one] using hweq',
end

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the entire space. -/
lemma affine_span_eq_top_of_to_matrix_left_inv [decidable_eq ι] [nontrivial k]
  (p : ι' → P) {A : matrix ι ι' k} (hA : A ⬝ b.to_matrix p = 1) : affine_span k (range p) = ⊤ :=
begin
  suffices : ∀ i, b i ∈ affine_span k (range p),
  { rw [eq_top_iff, ← b.tot, affine_span_le],
    rintros q ⟨i, rfl⟩,
    exact this i, },
  intros i,
  have hAi : ∑ j, A i j = 1,
  { calc ∑ j, A i j = ∑ j, (A i j) * ∑ l, b.to_matrix p j l : by simp
                ... = ∑ j, ∑ l, (A i j) * b.to_matrix p j l : by simp_rw finset.mul_sum
                ... = ∑ l, ∑ j, (A i j) * b.to_matrix p j l : by rw finset.sum_comm
                ... = ∑ l, (A ⬝ b.to_matrix p) i l : rfl
                ... = 1 : by simp [hA, matrix.one_apply, finset.filter_eq], },
  have hbi : b i = finset.univ.affine_combination k p (A i),
  { apply b.ext_elem,
    intros j,
    rw [b.coord_apply, finset.univ.map_affine_combination _ _ hAi,
      finset.univ.affine_combination_eq_linear_combination _ _ hAi],
    change _ = (A ⬝ b.to_matrix p) i j,
    simp_rw [hA, matrix.one_apply, @eq_comm _ i j] },
  rw hbi,
  exact affine_combination_mem_affine_span hAi p,
end

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_inv_mul_affine_basis_to_matrix`. -/
@[simp] lemma to_matrix_vec_mul_coords (x : P) :
  (b.to_matrix b₂).vec_mul (b₂.coords x) = b.coords x :=
begin
  ext j,
  change _ = b.coord j x,
  conv_rhs { rw ← b₂.affine_combination_coord_eq_self x, },
  rw finset.map_affine_combination _ _ _ (b₂.sum_coord_apply_eq_one x),
  simp [matrix.vec_mul, matrix.dot_product, to_matrix_apply, coords],
end

variables [decidable_eq ι]

lemma to_matrix_mul_to_matrix :
  (b.to_matrix b₂) ⬝ (b₂.to_matrix b) = 1 :=
begin
  ext l m,
  change (b₂.to_matrix b).vec_mul (b.coords (b₂ l)) m = _,
  rw [to_matrix_vec_mul_coords, coords_apply, ← to_matrix_apply, to_matrix_self],
end

lemma is_unit_to_matrix :
  is_unit (b.to_matrix b₂) :=
⟨{ val     := b.to_matrix b₂,
   inv     := b₂.to_matrix b,
   val_inv := b.to_matrix_mul_to_matrix b₂,
   inv_val := b₂.to_matrix_mul_to_matrix b, }, rfl⟩

lemma is_unit_to_matrix_iff [nontrivial k] (p : ι → P) :
  is_unit (b.to_matrix p) ↔ affine_independent k p ∧ affine_span k (range p) = ⊤ :=
begin
  split,
  { rintros ⟨⟨B, A, hA, hA'⟩, (rfl : B = b.to_matrix p)⟩,
    rw matrix.mul_eq_mul at hA hA',
    exact ⟨b.affine_independent_of_to_matrix_right_inv p hA,
           b.affine_span_eq_top_of_to_matrix_left_inv p hA'⟩, },
  { rintros ⟨h_tot, h_ind⟩,
    let b' : affine_basis ι k P := ⟨p, h_tot, h_ind⟩,
    change is_unit (b.to_matrix b'),
    exact b.is_unit_to_matrix b', },
end

end ring

section comm_ring
variables [comm_ring k] [module k V] [decidable_eq ι] [fintype ι]
variables (b b₂ : affine_basis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_vec_mul_coords`. -/
@[simp] lemma to_matrix_inv_vec_mul_to_matrix (x : P) :
  (b.to_matrix b₂)⁻¹.vec_mul (b.coords x) = b₂.coords x :=
begin
  have hu := b.is_unit_to_matrix b₂,
  rw matrix.is_unit_iff_is_unit_det at hu,
  rw [← b.to_matrix_vec_mul_coords b₂, matrix.vec_mul_vec_mul, matrix.mul_nonsing_inv _ hu,
    matrix.vec_mul_one],
end

/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
lemma det_smul_coords_eq_cramer_coords (x : P) :
  (b.to_matrix b₂).det • b₂.coords x = (b.to_matrix b₂)ᵀ.cramer (b.coords x) :=
begin
  have hu := b.is_unit_to_matrix b₂,
  rw matrix.is_unit_iff_is_unit_det at hu,
  rw [← b.to_matrix_inv_vec_mul_to_matrix, matrix.det_smul_inv_vec_mul_eq_cramer_transpose _ _ hu],
end
end comm_ring

end affine_basis
