import linear_algebra.matrix.spectrum
import linear_algebra.quadratic_form.basic

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ x y

def pos_def (M : matrix n n 𝕜) :=
M.is_hermitian ∧ ∀ x : n → 𝕜, x ≠ 0 → (0 : ℝ) < is_R_or_C.re ⟪x, M.mul_vec x⟫

def pos_semidef (M : matrix n n 𝕜) :=
M.is_hermitian ∧ ∀ x : n → 𝕜, (0 : ℝ) ≤ is_R_or_C.re ⟪x, M.mul_vec x⟫

lemma pos_def_of_to_quadratic_form' [decidable_eq n] {M : matrix n n ℝ}
  (hM : M.is_hermitian) (hMq : M.to_quadratic_form'.pos_def) :
  M.pos_def :=
begin
  refine ⟨hM, _⟩,
  intros x hx,
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

lemma _root_.quadratic_form.pos_def_iff_matrix
  [decidable_eq n] {Q : quadratic_form ℝ (n → ℝ)} (hQ : Q.to_matrix'.pos_def) :
  Q.pos_def :=
begin
  rw [←quadratic_form.to_quadratic_form_associated _ Q,
      ←bilin_form.to_matrix'.left_inv ((quadratic_form.associated_hom _) Q)],
  apply pos_def_to_quadratic_form' hQ,
end

#check linear_equiv.conj_trans

#check quadratic_form.pos_def
#check @quadratic_form.to_matrix'
#check matrix.to_quadratic_form'

end matrix
