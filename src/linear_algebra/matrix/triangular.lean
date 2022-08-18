
import linear_algebra.matrix.block

namespace matrix
open_locale big_operators
variables {α m n : Type*}
variables {R : Type*} [comm_ring R] {M : matrix m m R}

def upper_triangular [has_lt m] (M : matrix m m R) :=
  M.block_triangular id

def lower_triangular [has_lt m] (M : matrix m m R) :=
  M.block_triangular order_dual.to_dual

lemma det_of_upper_triangular [fintype m] [linear_order m] (h : M.upper_triangular) :
  M.det = ∏ i : m, M i i :=
begin
  haveI : decidable_eq R := classical.dec_eq _,
  simp_rw [h.det, finset.image_id, det_to_square_block_id],
end

lemma det_of_lower_triangular [fintype m] [linear_order m] (h : M.lower_triangular) :
  M.det = ∏ i : m, M i i :=
by { rw ←det_transpose, exact det_of_upper_triangular h.transpose }

lemma upper_triangular_inv_of_upper_triangular [fintype m] [linear_order m] [invertible M]
  (hM : upper_triangular M) : upper_triangular M⁻¹ :=
block_triangular_inv_of_block_triangular hM

lemma lower_triangular_inv_of_lower_triangular [fintype m] [linear_order m] [invertible M]
  (hM : lower_triangular M) : lower_triangular M⁻¹ :=
block_triangular_inv_of_block_triangular hM

end matrix
