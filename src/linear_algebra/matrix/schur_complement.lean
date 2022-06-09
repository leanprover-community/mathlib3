import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse

namespace matrix

open_locale matrix
variables {n : Type*} [fintype n] [decidable_eq n] {R : Type*} [comm_ring R]

variables (A B C D : matrix n n R) (x y u v: n → R)

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix
localized "infix ` ᵛ⬝ `:73 := vec_mul" in matrix
localized "infix ` ⬝ᵛ `:74 := mul_vec" in matrix

lemma schur_complement_eq {A : matrix n n R} (hA : A.is_symm) [invertible A] :
(x ⊕ᵥ y) ᵛ⬝ from_blocks A B Bᵀ D ⬝ᵥ (x ⊕ᵥ y) =
  (x + A⁻¹ ⬝ B ⬝ᵛ y) ᵛ⬝ A ⬝ᵥ (x + A⁻¹ ⬝ B ⬝ᵛ y) + y ᵛ⬝ (D - Bᵀ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
begin
  simp [from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul, dot_product_mul_vec,
    vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hA.eq, transpose_nonsing_inv],
  abel
end

end matrix


namespace matrix

open_locale matrix
variables {n : Type*} [fintype n] [decidable_eq n] {R : Type*} [ordered_comm_ring R]

variables (A B C D : matrix n n R) (x y u v: n → R)

def pos_def := ∀ x, x ≠ 0 → 0 < x ᵛ⬝ A ⬝ᵥ x
def pos_semidef := ∀ x, 0 ≤ x ᵛ⬝ A ⬝ᵥ x

lemma pos_semidef_of_pos_def (hA : A.pos_def) : A.pos_semidef :=
begin
  intros x,
  by_cases hx : x = 0,
  { simp only [hx, zero_vec_mul, zero_dot_product] },
  { exact le_of_lt (hA x hx) },
end

lemma schur_complement_pos_def [invertible A] (hAsymm : A.is_symm) (hA : A.pos_def) :
  (from_blocks A B Bᵀ D).pos_semidef ↔ (D - Bᵀ ⬝ A⁻¹ ⬝ B).pos_semidef :=
begin
  split,
  { intros h x,
    unfold pos_def at *,
    have := h (- (A⁻¹ ⬝ B ⬝ᵛ x) ⊕ᵥ x),
    rw [schur_complement_eq _ _ _ _ hAsymm, neg_add_self, dot_product_zero, zero_add] at this,
    exact this },
  { intros h x,
    rw [← sum.elim_comp_inl_inr x, schur_complement_eq _ _ _ _ hAsymm],
    apply le_add_of_nonneg_of_le,
    { apply (pos_semidef_of_pos_def A hA) },
    { apply h } }
end


end matrix
