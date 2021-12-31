import data.matrix.basic
import linear_algebra.matrix.symmetric
import analysis.convex.cone
import analysis.inner_product_space.spectrum


section psd_cone

variables (n : ℕ)

local notation `ℳₙ` := matrix (fin n) (fin n) ℝ

section definitions

open_locale matrix
open matrix

noncomputable instance : inner_product_space ℝ (fin n → ℝ) :=
inner_product_space.of_core $ {
  inner := matrix.dot_product,
  conj_sym := sorry,
  nonneg_re := sorry,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry,
}

lemma inner_def (v w : fin n → ℝ) : inner v w = matrix.dot_product v w := rfl

end definitions

section spectral_theorem

lemma is_self_adjoint_of_is_symm (M : ℳₙ) (hM : M.is_symm)
  : is_self_adjoint (matrix.mul_vec_lin M) :=
begin
  intros x y,
  simp [inner_def, matrix.dot_product_mul_vec, ←matrix.mul_vec_transpose],
  congr,
  exact hM.symm,
end

lemma spectral_theorem
  (M : ℳₙ) (hM : M.is_symm)
  (μ : module.End.eigenvalues (matrix.mul_vec_lin M))
  (v : fin n → ℝ) :
  (is_self_adjoint_of_is_symm n M hM).diagonalization (M.mul_vec_lin v) μ
  = (μ : ℝ) • (is_self_adjoint_of_is_symm n M hM).diagonalization v μ :=
begin
  sorry,
end

#check is_self_adjoint.diagonalization_apply_self_apply

end spectral_theorem

/-
instance : has_inner ℝ (matrix (fin n) (fin n) ℝ) :=
{ inner := λ A B, trace (fin n) ℝ ℝ (Aᵀ ⬝ B) }

noncomputable instance matrix.normed_group.inst : normed_group (matrix (fin n) (fin n) ℝ) :=
matrix.normed_group

noncomputable instance matrix.normed_space.inst : normed_space ℝ (matrix (fin n) (fin n) ℝ) :=
matrix.normed_space

lemma matrix.dot_product_self_nonneg
  {γ R} [fintype γ] [linear_ordered_ring R] (v : γ → R)
  : 0 ≤ dot_product v v :=
begin
  apply finset.sum_nonneg,
  intros i hi,
  exact mul_self_nonneg (v i),
end

noncomputable instance : inner_product_space ℝ (matrix (fin n) (fin n) ℝ) :=
inner_product_space.of_core $ {
  inner := λ A B, trace (fin n) ℝ ℝ (Aᵀ ⬝ B),
  conj_sym := begin
    intros A B,
    simp only [star_ring_aut, star, coe_fn, has_coe_to_fun.coe, id],
    show trace (fin n) ℝ ℝ _ = trace (fin n) ℝ ℝ _,
    rw [← trace_transpose, transpose_mul, transpose_transpose],
  end,
  nonneg_re := begin
    intros A,
    simp [matrix.trace],
    apply finset.sum_nonneg,
    intros i hi,
    simp [matrix.mul],
    exact matrix.dot_product_self_nonneg _,
  end,
  definite := begin
    sorry,
  end,
  add_left := begin
    sorry,
  end,
  smul_left := begin
    sorry,
  end,
}

def psd_cone_set : set (matrix (fin n) (fin n) ℝ) :=
{ P | is_symm P ∧ ∀ x, dot_product (vec_mul x P) x ≥ 0 }

noncomputable def psd_cone_dual : convex_cone ℝ (matrix (fin n) (fin n) ℝ) :=
set.inner_dual_cone (psd_cone_set n)

-/

end psd_cone
