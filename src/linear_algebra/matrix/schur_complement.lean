import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def

namespace matrix

open_locale matrix
variables {n : Type*} [fintype n] [decidable_eq n] {R : Type*} [comm_ring R] [star_ring R]

variables (A B C D : matrix n n R) (x y u v: n → R)

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix

lemma star_sum_elim : star (x ⊕ᵥ y)  = (star x ⊕ᵥ star y) :=
by { ext x, cases x; simp }

lemma schur_complement_eq {A : matrix n n R} (hA : A.is_hermitian) [invertible A] :
vec_mul (star (x ⊕ᵥ y)) (from_blocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vec_mul (star (x + (A⁻¹ ⬝ B).mul_vec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mul_vec y) +
    vec_mul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
begin
  simp [star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul, dot_product_mul_vec,
    vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hA.eq, conj_transpose_nonsing_inv,
    star_mul_vec],
  abel
end

end matrix

namespace matrix

open_locale matrix
variables {n : Type*} [fintype n] [decidable_eq n] {R : Type*} [ordered_comm_ring R] [star_ring R]

variables (A B C D : matrix n n R) (x y u v: n → R)

-- TODO: move
lemma pos_semidef_of_pos_def (hA : A.pos_def) : A.pos_semidef :=
begin
  refine ⟨hA.1, _⟩,
  intros x,
  by_cases hx : x = 0,
  { simp only [hx, zero_dot_product, star_zero] },
  { exact le_of_lt (hA.2 x hx) }
end

-- TODO: invertible if pos_def

-- TODO: move
lemma is_hermitian_sub (hA : A.is_hermitian) (hB : B.is_hermitian) :
  (A - B).is_hermitian :=
begin
  ext i j,
  simp only [dmatrix.sub_apply, star_sub, is_hermitian.apply hA, is_hermitian.apply hB]
end

-- TODO: move
lemma is_hermitian_add (hA : A.is_hermitian) (hB : B.is_hermitian) :
  (A + B).is_hermitian :=
begin
  ext i j,
  simp only [is_hermitian.apply hA, is_hermitian.apply hB, dmatrix.add_apply, star_add]
end

lemma is_hermitian_mul_mul (hA : A.is_hermitian) : (Bᴴ ⬝ A ⬝ B).is_hermitian :=
by simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
  matrix.mul_assoc]

lemma is_hermitian_nonsingular_inv (hA : A.is_hermitian) :
  A⁻¹.is_hermitian :=
by simp [is_hermitian, conj_transpose_nonsing_inv, hA.eq]

lemma schur_complement_is_hermitian_iff (hA : A.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian :=
begin
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian,
  { apply is_hermitian_mul_mul,
    apply is_hermitian_nonsingular_inv _ hA },
  rw [is_hermitian_from_blocks_iff],
  split,
  { intro h,
    apply is_hermitian_sub _ _ h.2.2.2 hBAB },
  { intro h,
    refine ⟨hA, rfl, conj_transpose_conj_transpose B, _⟩,
    rw ← sub_add_cancel D,
    apply is_hermitian_add _ _ h hBAB }
end

lemma schur_complement_pos_def [invertible A] (hA : A.pos_def) :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).pos_semidef :=
begin
  unfold pos_semidef,
  rw schur_complement_is_hermitian_iff _ _ _ hA.1,
  split,
  { refine λ h, ⟨h.1, λ x, _⟩,
    unfold pos_def at hA,
    have := h.2 (- ((A⁻¹ ⬝ B).mul_vec x) ⊕ᵥ x),
    rw [dot_product_mul_vec, schur_complement_eq _ _ _ _ hA.1, neg_add_self,
      dot_product_zero, zero_add] at this,
    rw [dot_product_mul_vec], exact this },
  { refine λ h, ⟨h.1, λ x, _⟩,
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq _ _ _ _ hA.1],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply (pos_semidef_of_pos_def A hA).2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end

end matrix
