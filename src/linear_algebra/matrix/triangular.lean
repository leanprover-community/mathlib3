import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.block

namespace matrix
variables {n R : Type*} (M N : matrix n n R)

/-- A matrix is lower triangular if all entries below the diagonal are zero. -/
def lower_triangular [has_lt n] [has_zero R] (M : matrix n n R) :=
∀ i j, i < j → M i j = 0

lemma lower_triangular.eq_zero [has_lt n] [has_zero R]
  {M : matrix n n R} (hM : M.lower_triangular) :
  ∀ {i} {j}, i < j → M i j = 0 := hM

lemma lower_triangular_zero [has_lt n] [has_zero R]
  (hM : M.lower_triangular) (hN : N.lower_triangular) :
  matrix.lower_triangular (0 : matrix n n R) := λ i j hij, rfl

lemma lower_triangular_one [preorder n] [decidable_eq n] [has_zero R] [has_one R]
  (hM : M.lower_triangular) (hN : N.lower_triangular):
  matrix.lower_triangular (1 : matrix n n R) := λ i j hij, diagonal_apply_ne _ (ne_of_lt hij)

lemma lower_triangular_add [has_lt n] [add_zero_class R]
  (hM : M.lower_triangular) (hN : N.lower_triangular):
  (M + N).lower_triangular :=
λ i j hij, show M i j + N i j = 0, by rw [hM.eq_zero hij, hN.eq_zero hij, zero_add]

lemma lower_triangular_mul [linear_order n] [fintype n] [non_unital_non_assoc_semiring R]
  (hM : M.lower_triangular) (hN : N.lower_triangular):
  (M * N).lower_triangular :=
begin
  intros i j hij,
  apply finset.sum_eq_zero,
  intros k hk,
  by_cases hik : i < k,
  { simp_rw [hM.eq_zero hik, zero_mul] },
  { simp_rw [hN.eq_zero (lt_of_le_of_lt (le_of_not_lt hik) hij), mul_zero] },
end

/-- The diagonal entries of an invertible lower triangular matrix are nonzero. -/
lemma diag_ne_zero_of_invertible_of_lower_triangular {n : ℕ} [comm_ring R] [nontrivial R]
  {M : matrix (fin n) (fin n) R} (hM : M.lower_triangular) [invertible M] (i : fin n):
  M i i ≠ 0 :=
λ h, (is_unit_det_of_invertible M).ne_zero
  ((det_of_lower_triangular M hM).trans (finset.prod_eq_zero (finset.mem_univ _) h))

/-- The inverse of a lower triangular matrix is lower triangular. -/
lemma lower_triangular_inv {n : ℕ} [comm_ring R] [nontrivial R] [no_zero_divisors R]
  {M : matrix (fin n) (fin n) R} (hM : M.lower_triangular) [invertible M] :
  (M⁻¹).lower_triangular :=
begin
  rintros ⟨i, hi⟩ ⟨j,hj⟩ hij,
  induction i using nat.strong_induction_on with i ih,
  have : finset.univ.sum (λ k, M ⟨i, hi⟩ k * M⁻¹ k ⟨j, hj⟩) = 0,
    from (matrix.ext_iff.2 (mul_inv_of_invertible M) ⟨i, hi⟩ ⟨j, hj⟩).trans (if_neg (ne_of_lt hij)),
  have : M ⟨i, hi⟩ ⟨i, hi⟩ * M⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ = 0,
  { rw [eq_comm, ← this],
    refine finset.sum_eq_single_of_mem ⟨i, hi⟩ (finset.mem_univ ⟨i, hi⟩) _,
    rintros ⟨k, hk⟩ hk' hki,
    by_cases h : subtype.mk k hk < subtype.mk i hi,
    { simp [ih k h hk (h.trans hij)] },
    { simp [hM ⟨i, hi⟩ ⟨k, hk⟩ (lt_of_le_of_ne' (le_of_not_lt h) hki)] } },
  show M⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ = 0,
    from (mul_eq_zero.1 this).resolve_left (diag_ne_zero_of_invertible_of_lower_triangular hM _)
end

end matrix
