import data.matrix.basic
import linear_algebra.matrix.symmetric
import analysis.convex.cone

section psd_cone

variables (n : ℕ)

open_locale matrix
open matrix

/--
instance : has_inner ℝ (matrix (fin n) (fin n) ℝ) :=
{ inner := λ A B, trace (fin n) ℝ ℝ (Aᵀ ⬝ B) }

noncomputable instance matrix.normed_group.inst : normed_group (matrix (fin n) (fin n) ℝ) :=
matrix.normed_group

noncomputable instance matrix.normed_space.inst : normed_space ℝ (matrix (fin n) (fin n) ℝ) :=
matrix.normed_space
--/

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

end psd_cone
