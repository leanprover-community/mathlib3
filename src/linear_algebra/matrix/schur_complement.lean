import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse

namespace matrix

open_locale matrix
variables {n : Type*} [fintype n] [decidable_eq n] {R : Type*} [comm_ring R]

variables (A B C D : matrix n n R) (x y u v: n → R)

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix
localized "infix ` ᵛ⬝ `:73 := vec_mul" in matrix
localized "infix ` ⬝ᵛ `:74 := mul_vec" in matrix
-- lemma xxxxx : (sum.elim x y)

@[simp] lemma elim_dot_product_elim : (x ⊕ᵥ y) ⬝ᵥ (u ⊕ᵥ v) = x ⬝ᵥ u + y ⬝ᵥ v :=
by simp [dot_product]

lemma mul_vec_vec_mul : (A ⬝ᵛ x) ᵛ⬝ B = x ᵛ⬝ (Aᵀ ⬝ B) :=
by rw [← vec_mul_vec_mul, vec_mul_transpose]

@[simp] lemma from_blocks_mul_vec_elim : (from_blocks A B C D) ⬝ᵛ (x ⊕ᵥ y) =
  (A ⬝ᵛ x + B ⬝ᵛ y) ⊕ᵥ
  (C ⬝ᵛ x + D ⬝ᵛ y) :=
begin
  ext i,
  cases i,
  simp [mul_vec, dot_product],
  simp [mul_vec, dot_product],
end

@[simp] lemma elim_vec_mul_from_blocks : (x ⊕ᵥ y) ᵛ⬝ (from_blocks A B C D) =
  (x ᵛ⬝ A + y ᵛ⬝ C) ⊕ᵥ
  (x ᵛ⬝ B + y ᵛ⬝ D) :=
begin
  ext i,
  cases i,
  simp [vec_mul, dot_product],
  simp [vec_mul, dot_product],
end

@[simp] protected lemma matrix.inv_mul [invertible A] : ⅟A ⬝ A = 1 :=
by rw [←mul_eq_mul, inv_of_mul_self]

@[simp] protected lemma matrix.mul_inv [invertible A] : A ⬝ ⅟A = 1 :=
by rw [←mul_eq_mul, mul_inv_of_self]

@[simp] lemma matrix.mul_inv_cancel_right [invertible A] : C ⬝ A ⬝ ⅟A = C :=
by rw [matrix.mul_assoc, matrix.mul_inv, matrix.mul_one]

@[simp] lemma matrix.mul_inv_cancel_right' [invertible A] : C ⬝ A ⬝ A⁻¹ = C :=
by rw [←inv_of_eq_nonsing_inv, matrix.mul_inv_cancel_right]

@[simp] lemma matrix.inv_mul_cancel_right [invertible A] : C ⬝ ⅟A ⬝ A = C :=
by rw [matrix.mul_assoc, matrix.inv_mul, matrix.mul_one]

@[simp] lemma matrix.inv_mul_cancel_right' [invertible A] : C ⬝ A⁻¹ ⬝ A = C :=
by rw [←inv_of_eq_nonsing_inv, matrix.inv_mul_cancel_right]

@[simp] lemma sub_mul_vec : (A - B) ⬝ᵛ x = A ⬝ᵛ x - B ⬝ᵛ x :=
by simp [sub_eq_add_neg, add_mul_vec, neg_mul_vec]

@[simp] lemma vec_mul_sub : x ᵛ⬝ (A - B) = x ᵛ⬝ A - x ᵛ⬝ B :=
by simp [sub_eq_add_neg, vec_mul_add, vec_mul_neg]

lemma schur_complement_eq {A : matrix n n R} (hA : A.is_symm) [invertible A] :
(x ⊕ᵥ y) ᵛ⬝ from_blocks A B Bᵀ D ⬝ᵥ (x ⊕ᵥ y) =
  (x + ⅟A ⬝ B ⬝ᵛ y) ᵛ⬝ A ⬝ᵥ (x + ⅟A ⬝ B ⬝ᵛ y) + y ᵛ⬝ (D - Bᵀ ⬝ ⅟A ⬝ B) ⬝ᵥ y :=
begin
  simp [-inv_of_eq_inv, from_blocks_mul_vec_elim, mul_vec_add, add_vec_mul, dot_product_mul_vec,
    ←matrix.mul_assoc, mul_vec_vec_mul, hA.eq, transpose_nonsing_inv],
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
  (from_blocks A B Bᵀ D).pos_semidef ↔ (D - Bᵀ ⬝ ⅟A ⬝ B).pos_semidef :=
begin
  split,
  { intros h x,
    unfold pos_def at *,
    have := h (- (⅟A ⬝ B ⬝ᵛ x) ⊕ᵥ x),
    rw [schur_complement_eq _ _ _ _ hAsymm, neg_add_self, dot_product_zero, zero_add] at this,
    exact this },
  { intros h x,
    rw [← sum.elim_comp_inl_inr x, schur_complement_eq _ _ _ _ hAsymm],
    apply le_add_of_nonneg_of_le,
    { apply (pos_semidef_of_pos_def A hA) },
    { apply h } }
end


end matrix
