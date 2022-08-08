/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import linear_algebra.matrix.spectrum
import linear_algebra.quadratic_form.basic

/-! # Positive Definite Matrices
This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.
## Main definition
 * `matrix.pos_def` : a matrix `M : matrix n n R` is positive definite if it is hermitian and `xᴴMx`
   is greater than zero for all nonzero `x`.
 * `matrix.pos_semidef` : a matrix `M : matrix n n R` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`.
-/

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] {m n : Type*} [fintype m] [fintype n]

open_locale matrix

/-- A matrix `M : matrix n n R` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def pos_def (M : matrix n n 𝕜) :=
M.is_hermitian ∧ ∀ x : n → 𝕜, x ≠ 0 → 0 < is_R_or_C.re (dot_product (star x) (M.mul_vec x))

lemma pos_def.is_hermitian {M : matrix n n 𝕜} (hM : M.pos_def) : M.is_hermitian := hM.1

/-- A matrix `M : matrix n n R` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`. -/
def pos_semidef (M : matrix n n R) :=
M.is_hermitian ∧ ∀ x : n → R, 0 ≤ dot_product (star x) (M.mul_vec x)

lemma pos_def.pos_semidef {M : matrix n n R} (hM : M.pos_def) : M.pos_semidef :=
begin
  refine ⟨hM.1, _⟩,
  intros x,
  by_cases hx : x = 0,
  { simp only [hx, zero_dot_product, star_zero] },
  { exact le_of_lt (hM.2 x hx) }
end

lemma pos_semidef.minor {M : matrix n n R} (hM : M.pos_semidef) (e : m ≃ n):
  (M.minor e e).pos_semidef :=
begin
  refine ⟨hM.1.minor e, λ x, _⟩,
  have : (M.minor ⇑e ⇑e).mul_vec x = M.mul_vec (λ (i : n), x (e.symm i)) ∘ e,
  { ext i,
    dsimp only [(∘), mul_vec, dot_product],
    rw finset.sum_bij' (λ i _, e i) _ _ (λ i _, e.symm i);
    simp only [eq_self_iff_true, implies_true_iff, equiv.symm_apply_apply, finset.mem_univ,
      minor_apply, equiv.apply_symm_apply] },
  rw this,
  convert hM.2 (λ i, x (e.symm i)) using 3,
  unfold dot_product,
  rw [finset.sum_bij' (λ i _, e i) _ _ (λ i _, e.symm i)];
  simp only [eq_self_iff_true, implies_true_iff, equiv.symm_apply_apply, finset.mem_univ,
    minor_apply, equiv.apply_symm_apply, pi.star_apply],
end

@[simp] lemma pos_semidef_minor_equiv {M : matrix n n R} (e : m ≃ n) :
  (M.minor e e).pos_semidef ↔ M.pos_semidef :=
⟨λ h, by simpa using h.minor e.symm, λ h, h.minor _⟩

lemma pos_def_of_to_quadratic_form' [decidable_eq n] {M : matrix n n ℝ}
  (hM : M.is_symm) (hMq : M.to_quadratic_form'.pos_def) :
  M.pos_def :=
begin
  refine ⟨hM, λ x hx, _⟩,
  simp only [to_quadratic_form', quadratic_form.pos_def, bilin_form.to_quadratic_form_apply,
    matrix.to_bilin'_apply'] at hMq,
  apply hMq x hx,
end

lemma pos_def_to_quadratic_form' [decidable_eq n] {M : matrix n n ℝ} (hM : M.pos_def) :
  M.to_quadratic_form'.pos_def :=
begin
  intros x hx,
  simp only [to_quadratic_form', bilin_form.to_quadratic_form_apply, matrix.to_bilin'_apply'],
  apply hM.2 x hx,
end

end matrix

namespace quadratic_form

variables {n : Type*} [fintype n]

lemma pos_def_of_to_matrix'
  [decidable_eq n] {Q : quadratic_form ℝ (n → ℝ)} (hQ : Q.to_matrix'.pos_def) :
  Q.pos_def :=
begin
  rw [←to_quadratic_form_associated ℝ Q,
      ←bilin_form.to_matrix'.left_inv ((associated_hom _) Q)],
  apply matrix.pos_def_to_quadratic_form' hQ
end

lemma pos_def_to_matrix' [decidable_eq n] {Q : quadratic_form ℝ (n → ℝ)} (hQ : Q.pos_def) :
  Q.to_matrix'.pos_def :=
begin
  rw [←to_quadratic_form_associated ℝ Q,
    ←bilin_form.to_matrix'.left_inv ((associated_hom _) Q)] at hQ,
  apply matrix.pos_def_of_to_quadratic_form' (is_symm_to_matrix' Q) hQ,
end

end quadratic_form

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]

/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
noncomputable def inner_product_space.of_matrix
  {M : matrix n n 𝕜} (hM : M.pos_def) : inner_product_space 𝕜 (n → 𝕜) :=
inner_product_space.of_core
{ inner := λ x y, dot_product (star x) (M.mul_vec y),
  conj_sym := λ x y, by
    rw [star_dot_product, star_ring_end_apply, star_star, star_mul_vec,
      dot_product_mul_vec, hM.is_hermitian.eq],
  nonneg_re := λ x,
    begin
      by_cases h : x = 0,
      { simp [h] },
      { exact le_of_lt (hM.2 x h) }
    end,
  definite := λ x hx,
    begin
      by_contra' h,
      simpa [hx, lt_self_iff_false] using hM.2 x h,
    end,
  add_left := by simp only [star_add, add_dot_product, eq_self_iff_true, forall_const],
  smul_left := λ x y r, by rw [← smul_eq_mul, ←smul_dot_product, star_ring_end_apply, ← star_smul] }

end matrix
