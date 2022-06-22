/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.function.jacobian

noncomputable theory

open real set measure_theory
open_locale real



#check matrix

@[simp, to_additive] lemma finset.prod_univ_fin_two {E : Type*} [comm_monoid E] (f : fin 2 → E) :
  finset.univ.prod f = f 0 * f 1 :=
by simp [fin.prod_univ_succ]

lemma det_two {α : Type*} [comm_ring α] {a b c d : α} :
  matrix.det ![![a, b], ![c, d]] = a * d - b * c :=
begin
  simp [matrix.det_succ_row_zero],
  ring
end


def basis_fin_two_prod (R : Type*) [semiring R] : basis (fin 2) R (R × R) :=
basis.of_equiv_fun (linear_equiv.fin_two_arrow R R).symm

@[simp] lemma basis_fin_two_prod_zero (R : Type*) [semiring R] : basis_fin_two_prod R 0 = (1, 0) :=
by simp [basis_fin_two_prod]

@[simp] lemma basis_fin_two_prod_one (R : Type*) [semiring R] : basis_fin_two_prod R 1 = (0, 1) :=
by simp [basis_fin_two_prod]

lemma to_lin_prod_continuous_linear_map (a b c d : ℝ) :
  (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![a, b], ![c, d]]).to_continuous_linear_map =
  (a • continuous_linear_map.fst ℝ ℝ ℝ + b • continuous_linear_map.snd ℝ ℝ ℝ).prod
  (c • continuous_linear_map.fst ℝ ℝ ℝ + d • continuous_linear_map.snd ℝ ℝ ℝ) :=
begin
  ext;
  simp only [continuous_linear_map.coe_comp', linear_map.coe_to_continuous_linear_map',
    function.comp_app, continuous_linear_map.inl_apply, continuous_linear_map.prod_apply,
    continuous_linear_map.add_apply, continuous_linear_map.coe_smul',
    continuous_linear_map.coe_fst', pi.smul_apply, algebra.id.smul_eq_mul, mul_one,
    continuous_linear_map.coe_snd', mul_zero, add_zero, continuous_linear_map.inr_apply, zero_add],
  { rw [← basis_fin_two_prod_zero ℝ, matrix.to_lin_self],
    simp only [finset.sum_univ_fin_two, matrix.cons_val_zero, basis_fin_two_prod_zero, prod.smul_mk,
      algebra.id.smul_eq_mul, mul_one, mul_zero, basis_fin_two_prod_one, prod.mk_add_mk,
      add_zero] },
  { rw [← basis_fin_two_prod_zero ℝ, matrix.to_lin_self],
    simp only [finset.sum_univ_fin_two, matrix.cons_val_zero, basis_fin_two_prod_zero, prod.smul_mk,
    algebra.id.smul_eq_mul, mul_one, mul_zero, matrix.cons_val_one, matrix.head_cons,
    basis_fin_two_prod_one, prod.mk_add_mk, zero_add] },
  { rw [← basis_fin_two_prod_one ℝ, matrix.to_lin_self],
    simp only [finset.sum_univ_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
      basis_fin_two_prod_zero, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, mul_zero,
      basis_fin_two_prod_one, prod.mk_add_mk, add_zero] },
  { rw [← basis_fin_two_prod_one ℝ, matrix.to_lin_self],
    simp only [finset.sum_univ_fin_two, matrix.cons_val_one, matrix.head_cons,
    basis_fin_two_prod_zero, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, mul_zero,
    basis_fin_two_prod_one, prod.mk_add_mk, zero_add] }
end

lemma has_fderiv_at_polar (p : ℝ × ℝ) :
  has_fderiv_at (λ (p : ℝ × ℝ), (p.1 * cos p.2, p.1 * sin p.2))
    (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]]).to_continuous_linear_map p :=
begin
  rw to_lin_prod_continuous_linear_map,
  convert has_fderiv_at.prod
    (has_fderiv_at_fst.mul ((has_deriv_at_cos p.2).comp_has_fderiv_at p has_fderiv_at_snd))
    (has_fderiv_at_fst.mul ((has_deriv_at_sin p.2).comp_has_fderiv_at p has_fderiv_at_snd)) using 2;
  simp only [smul_smul, add_comm, neg_mul, neg_smul, smul_neg],
end



theorem glouk {E : Type*} (f : ℝ × ℝ → ℝ) :
  -- ∫ θ in Icc (0 : ℝ) (2 * π), (∫ r in Ici (0 : ℝ), f (r * cos θ, r * sin θ) * r) = ∫ p, f p :=
  (∫ p in (Ici (0 : ℝ) ×ˢ Icc 0 (2 * π) : set (ℝ × ℝ)), f (p.1 * cos p.2, p.1 * sin p.2) * p.1)
    = ∫ p, f p :=
begin
/-  begin
    assume p,
    let M : matrix (fin 2) (fin 2) ℝ := ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]],
    have : M.det = p.1,
    { conv_rhs {rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2] },
      simp only [M, det_two],
      ring_exp },
    exact (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ) M).to_continuous_linear_map,

  end, -/
  let A : ℝ × ℝ → ℝ × ℝ := λ p, (p.1 * cos p.2, p.1 * sin p.2),
  set B : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := λ p,
    (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]]).to_continuous_linear_map with hB,
  have : ∀ p, has_fderiv_at A (B p) p := has_fderiv_at_polar,
  have : ∀ p, (B p).det = p.1,
  { assume p,
    simp [hB],

  }

end


#exit
