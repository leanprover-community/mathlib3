import linear_algebra.affine_space.basis
import linear_algebra.determinant


open_locale affine big_operators matrix

universes u₁ u₂ u₃ u₄

variables {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variables [add_comm_group V] [affine_space V P]

namespace affine_basis

variables [comm_ring k] [module k V] [decidable_eq ι] [fintype ι]
variables (b b₂ : affine_basis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_vec_mul_coords`. -/
@[simp] lemma to_matrix_inv_vec_mul_to_matrix (x : P) :
  (b.to_matrix b₂.points)⁻¹.vec_mul (b.coords x) = b₂.coords x :=
begin
  have hu := b.is_unit_to_matrix b₂,
  rw matrix.is_unit_iff_is_unit_det at hu,
  rw [← b.to_matrix_vec_mul_coords b₂, matrix.vec_mul_vec_mul, matrix.mul_nonsing_inv _ hu,
    matrix.vec_mul_one],
end

/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
lemma det_smul_coords_eq_cramer_coords (x : P) :
  (b.to_matrix b₂.points).det • b₂.coords x = (b.to_matrix b₂.points)ᵀ.cramer (b.coords x) :=
begin
  have hu := b.is_unit_to_matrix b₂,
  rw matrix.is_unit_iff_is_unit_det at hu,
  rw [← b.to_matrix_inv_vec_mul_to_matrix, matrix.det_smul_inv_vec_mul_eq_cramer_transpose _ _ hu],
end

end affine_basis
