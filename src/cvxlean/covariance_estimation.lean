import linear_algebra.matrix.pos_def

open real
open matrix
open_locale real
open_locale matrix
open_locale big_operators

noncomputable def gaussian_pdf {n : ℕ} (R : matrix (fin n) (fin n) ℝ) (x : fin n → ℝ) : ℝ :=
  (1 / sqrt (((2 * π) ^ n) * R.det)) * exp  (- x ⬝ᵥ R⁻¹.mul_vec x / 2)

-- noncomputable def problem (n : ℕ) (N : ℕ) (y : fin N → fin n →  ℝ) :=
--   optimization (R : Matrix (Finₓ n) (Finₓ n) ℝ)
--     maximize (∏ i, gaussianPdf R (y i))
--     subject to c_pos_def : R.posDef

def covariance_matrix {N n : ℕ} (y : fin N → fin n → ℝ) : matrix (fin n) (fin n) ℝ :=
  λ i j : fin n, ∑ k : fin N, y k i * y k j

lemma gaussian_pdf_pos {n : ℕ} (R : matrix (fin n) (fin n) ℝ) (y : fin n → ℝ) (h : R.pos_def):
  0 < gaussian_pdf R y :=
mul_pos (div_pos zero_lt_one
  (sqrt_pos.2 (mul_pos (pow_pos (mul_pos (by linarith) pi_pos) _) h.det_pos))) (exp_pos _)

lemma prod_gaussian_pdf_pos {N n : ℕ} (R : matrix (fin n) (fin n) ℝ) (y : fin N → fin n → ℝ)
    (h : R.pos_def):
  0 < ∏ i : fin N, gaussian_pdf R (y i) :=
finset.prod_pos (λ i hi, gaussian_pdf_pos _ _ h)

-- reduction reduction₁₂/problem₂ (n : ℕ) (N : ℕ) (y : Finₓ N → Finₓ n → ℝ) :
--   problem n N y := by
--   simp only [problem]
--   apply map_objective ℝ ℝ _ (fun x => - log (-x))
--   · intros R S hR hS h
--     apply neg_le_neg
--     simp only [maximizeNeg] at h
--     rwa [neg_negₓ, neg_negₓ,
--       @neg_le_neg_iff Real _ _ (OrderedAddCommGroup.to_covariant_class_left_le _) _,
--       log_le_log] at h
--     exact prod_gaussianPdf_pos S y hS
--     exact prod_gaussianPdf_pos R y hR
--   simp only [Function.comp, neg_negₓ, maximizeNeg]
--   change
--     Solution $
--     optimization (R : Matrix (Finₓ n) (Finₓ n) ℝ)
--     maximize log $ Finset.prod Finset.univ fun (i : Finₓ N) => gaussianPdf R (y i)
--     subject to c_pos_def : R.posDef

-- noncomputable def add_const {of : D → ℝ} {cs : D → Prop}
-- {c : ℝ}
-- (sol : Solution
--     { objFun := of
--       constraints := cs })  :
-- Solution {objFun := fun x => of x + c, constraints := cs} :=
-- map_objective ℝ ℝ (fun x => of x + c) (g := fun (x : ℝ) => x - c) cs
--   (by sorry)
--   (by sorry)

lemma log_prod_gaussianPdf {N n : ℕ} (y : fin N → fin n → ℝ) (R : matrix (fin n) (fin n) ℝ) :
    (log ∏ i : fin N, gaussian_pdf R (y i))
    = ∑ i : fin N, (log 1 - (log (sqrt ((2 * π) ^ n)) + log (sqrt (det R))) + - y i ⬝ᵥ R⁻¹.mul_vec (y i) / 2) :=
begin
    have : ∀ i,
      i ∈ finset.univ → gaussian_pdf R (y i) ≠ 0 := sorry,
    rw [log_prod finset.univ (λ i, gaussian_pdf R (y i)) this],
    unfold gaussian_pdf,
    apply congr_arg (finset.sum finset.univ),
    ext i,
    rw [log_mul, log_div, sqrt_mul, log_mul, log_exp],
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry
end

lemma sum_quadForm {n : ℕ} (R : Matrix (Finₓ n) (Finₓ n) ℝ) {m : ℕ} (y : Finₓ m → Finₓ n → ℝ) :
  (Finset.sum Finset.univ fun x => quadForm R (y x))
  = (covarianceMatrix y ⬝ R).trace := by
  simp only [quadForm, Matrix.trace, covarianceMatrix, mul, dotProduct, diag, vecMul, idRhs]
  rw [Finset.sum_comm]
  apply congrArg
  ext i
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply congrArg
  ext j
  apply congrArg
  ext k
  rw [_root_.mul_assoc, _root_.mul_comm (R j i), ←_root_.mul_assoc, _root_.mul_comm (y k i)]

lemma Real.log_sqrt' : ∀ {x : Real}, Zero.zero ≤ x → log (sqrt x) = log x / 2 := sorry

reduction reduction₂₃/problem₃ (n : ℕ) (N : ℕ) (y : Finₓ N → Finₓ n → ℝ) :
  problem₂ n N y := by
  simp_rw [problem₂]
  conv =>
    congr
    congr
    ext p
    show_vars p
    rw [log_prod_gaussianPdf, Finset.sum_add_distrib, SubNegMonoidₓ.sub_eq_add_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      ← SubNegMonoidₓ.sub_eq_add_neg, ←sub_sub, sub_add, maximizeNeg, neg_sub,
      SubNegMonoidₓ.sub_eq_add_neg, neg_sub]
  apply add_const
  conv =>
    congr
    congr
    ext p
    show_vars p
    rw [Finset.sum_const, Finset.card_fin]
    rw [@Real.log_sqrt' (det R) sorry, ← Finset.sum_div, div_eq_mul_one_div, ←smul_mul_assoc,
      ←div_eq_mul_one_div, @div_sub_div_same]
    rw [Finset.sum_neg_distrib, sub_neg_eq_add, sum_quadForm R⁻¹ y]

lemma IsUnit_of_posDef [OrderedCommRing R] [DecidableEq n] [Fintype n] (M : Matrix n n R) :
  posDef M → IsUnit M.det := sorry

lemma posDef_inv_iff [OrderedCommRing R] [DecidableEq n] [Fintype n] (M : Matrix n n R) :
  posDef M⁻¹ ↔ posDef M := sorry

lemma matrix.det_inv [Field R] [Fintype n] [DecidableEq n] (M : Matrix n n R) :
  (M⁻¹).det = M.det⁻¹ := sorry

reduction reduction₃₄/problem₄ (n : ℕ) (N : ℕ) (y : Finₓ N → Finₓ n → ℝ) :
  problem₃ n N y := by
    simp only [problem₃]
    apply map_domain (f := (·⁻¹)) (g := (·⁻¹))
    · intros R hR
      have : IsUnit R.det := IsUnit_of_posDef R hR
      simp only [nonsing_inv_nonsing_inv R this]
    simp only [Function.comp, posDef_inv_iff]
    apply rewrite_objective
    · intros R hR
      have : IsUnit R.det := IsUnit_of_posDef R hR
      rw [nonsing_inv_nonsing_inv R this, matrix.det_inv]
    -- simp



#print problem₄


noncomputable def dcp_reducible_problem (n : ℕ) (N : ℕ) (y : Finₓ N → Finₓ n → ℝ) :=
  optimization (R :  Matrix (Finₓ n) (Finₓ n) ℝ)
    maximize log (det R) - trace (covarianceMatrix y ⬝ R)
    subject to
      c_pos_def : posDef R

noncomputable def dcp_reduction (n : ℕ) (N : ℕ) (y : Finₓ N → Finₓ n → ℝ) : Solution (dcp_reducible_problem n N y) := by
  simp only [dcp_reducible_problem]
  dcp
  sorry
