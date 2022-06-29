/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.function.jacobian

/-!
# Changing variables in integrals through polar coordinates

-/

noncomputable theory

open real set measure_theory
open_locale real

lemma is_open_ne_fun
  {α β : Type*} [topological_space α] [topological_space β] [t2_space α] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : is_open {x:β | f x ≠ g x} :=
begin
  rw ← is_closed_compl_iff,
  convert is_closed_eq hf hg,
  ext x,
  simp,
end


/-- The polar coordinates local homeomorphism in `ℝ^2`, mapping `(r cos θ, r sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π)`. -/
@[simps] def polar_coord : local_homeomorph (ℝ × ℝ) (ℝ × ℝ) :=
{ to_fun := λ q, (real.sqrt (q.1^2 + q.2^2), complex.arg (complex.equiv_real_prod.symm q)),
  inv_fun := λ p, (p.1 * cos p.2, p.1 * sin p.2),
  source := {q | 0 < q.1} ∪ {q | q.2 ≠ 0},
  target := Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
  map_target' :=
  begin
    rintros ⟨r, θ⟩ ⟨hr, hθ⟩,
    dsimp at hr hθ,
    rcases eq_or_ne θ 0 with rfl|h'θ,
    { simpa using hr },
    { right,
      simpa only [ne_of_gt hr, ne.def, mem_set_of_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using h'θ }
  end,
  map_source' :=
  begin
    rintros ⟨x, y⟩ hxy,
    simp only [prod_mk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, complex.neg_pi_lt_arg,
      true_and, complex.arg_lt_pi_iff],
    split,
    { cases hxy,
      { dsimp at hxy, linarith [sq_pos_of_ne_zero _ (hxy.ne'), sq_nonneg y] },
      { linarith [sq_nonneg x, sq_pos_of_ne_zero _ hxy] } },
    { cases hxy,
      { exact or.inl (le_of_lt hxy) },
      { exact or.inr hxy } }
  end,
  right_inv' :=
  begin
    rintros ⟨r, θ⟩ ⟨hr, hθ⟩,
    dsimp at hr hθ,
    simp only [prod.mk.inj_iff],
    split,
    { conv_rhs { rw [← sqrt_sq (le_of_lt hr), ← one_mul (r^2), ← sin_sq_add_cos_sq θ], },
      congr' 1,
      ring_exp },
    { convert complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩,
      simp only [complex.equiv_real_prod_symm_apply, complex.of_real_mul, complex.of_real_cos,
        complex.of_real_sin],
      ring }
  end,
  left_inv' :=
  begin
    rintros ⟨x, y⟩ hxy,
    have A : sqrt (x ^ 2 + y ^ 2) = complex.abs (x + y * complex.I),
      by simp only [complex.abs, complex.norm_sq, pow_two, monoid_with_zero_hom.coe_mk,
        complex.add_re, complex.of_real_re, complex.mul_re, complex.I_re, mul_zero,
        complex.of_real_im, complex.I_im, sub_self, add_zero, complex.add_im,
        complex.mul_im, mul_one, zero_add],
    have Z := complex.abs_mul_cos_add_sin_mul_I (x + y * complex.I),
    simp only [← complex.of_real_cos, ← complex.of_real_sin, mul_add, ← complex.of_real_mul,
      ← mul_assoc] at Z,
    simpa [A, -complex.of_real_cos, -complex.of_real_sin] using complex.ext_iff.1 Z,
  end,
  open_target := is_open_Ioi.prod is_open_Ioo,
  open_source := (is_open_lt continuous_const continuous_fst).union
    (is_open_ne_fun continuous_snd continuous_const),
  continuous_inv_fun := ((continuous_fst.mul (continuous_cos.comp continuous_snd)).prod_mk
    (continuous_fst.mul (continuous_sin.comp continuous_snd))).continuous_on,
  continuous_to_fun :=
  begin
    apply ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.continuous_on.prod,
    have A : maps_to complex.equiv_real_prod.symm
      ({q : ℝ × ℝ | 0 < q.1} ∪ {q : ℝ × ℝ | q.2 ≠ 0}) {z | 0 < z.re ∨ z.im ≠ 0},
    { rintros ⟨x, y⟩ hxy, simpa only using hxy },
    apply continuous_on.comp (λ z hz, _) _ A,
    { exact (complex.continuous_at_arg hz).continuous_within_at },
    { exact complex.equiv_real_prodₗ.symm.continuous.continuous_on }
  end }

/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
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
    simp only [fin.sum_univ_two, matrix.cons_val_zero, basis_fin_two_prod_zero, prod.smul_mk,
      algebra.id.smul_eq_mul, mul_one, mul_zero, basis_fin_two_prod_one, prod.mk_add_mk,
      add_zero] },
  { rw [← basis_fin_two_prod_zero ℝ, matrix.to_lin_self],
    simp only [fin.sum_univ_two, matrix.cons_val_zero, basis_fin_two_prod_zero, prod.smul_mk,
      algebra.id.smul_eq_mul, mul_one, mul_zero, matrix.cons_val_one, matrix.head_cons,
      basis_fin_two_prod_one, prod.mk_add_mk, zero_add] },
  { rw [← basis_fin_two_prod_one ℝ, matrix.to_lin_self],
    simp only [fin.sum_univ_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
      basis_fin_two_prod_zero, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, mul_zero,
      basis_fin_two_prod_one, prod.mk_add_mk, add_zero] },
  { rw [← basis_fin_two_prod_one ℝ, matrix.to_lin_self],
    simp only [fin.sum_univ_two, matrix.cons_val_one, matrix.head_cons,
      basis_fin_two_prod_zero, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, mul_zero,
      basis_fin_two_prod_one, prod.mk_add_mk, zero_add] }
end

lemma has_fderiv_at_polar_coord_symm (p : ℝ × ℝ) :
  has_fderiv_at polar_coord.symm
    (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]]).to_continuous_linear_map p :=
begin
  rw to_lin_prod_continuous_linear_map,
  convert has_fderiv_at.prod
    (has_fderiv_at_fst.mul ((has_deriv_at_cos p.2).comp_has_fderiv_at p has_fderiv_at_snd))
    (has_fderiv_at_fst.mul ((has_deriv_at_sin p.2).comp_has_fderiv_at p has_fderiv_at_snd)) using 2;
  simp only [smul_smul, add_comm, neg_mul, neg_smul, smul_neg],
end

.

@[simp] lemma det_to_lin
  {ι : Type*} {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (b : basis ι R M) [fintype ι] [decidable_eq ι] (f : matrix ι ι R) :
  linear_map.det (matrix.to_lin b b f) = f.det :=
by rw [← linear_map.det_to_matrix b, linear_map.to_matrix_to_lin]

lemma zouf :
  polar_coord.source =ᵐ[volume] univ :=
begin
  have : polar_coord.sourceᶜ ⊆ {p | p.2 = 0},
  { assume x hx,
    simp only [polar_coord_source, compl_union, mem_inter_eq, mem_compl_eq, mem_set_of_eq, not_lt,
      not_not] at hx,
    exact hx.2 },
  have : volume ((linear_map.snd ℝ ℝ ℝ).ker : set (ℝ × ℝ)) = 0,
  { apply measure.add_haar_submodule,

  },
  simp only [ae_eq_univ],
end



theorem glouk {E : Type*} (f : ℝ × ℝ → ℝ) :
  (∫ p in (Ioi (0 : ℝ) ×ˢ (Ioo (-π) π) : set (ℝ × ℝ)), f (p.1 * cos p.2, p.1 * sin p.2) * p.1)
    = ∫ p, f p :=
begin
  set B : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := λ p,
    (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]]).to_continuous_linear_map with hB,
  have : ∀ p, has_fderiv_at polar_coord.symm (B p) p := has_fderiv_at_polar_coord_symm,
  have B_det : ∀ p, (B p).det = p.1,
  { assume p,
    conv_rhs {rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2] },
    simp only [neg_mul, linear_map.det_to_continuous_linear_map, det_to_lin,
      matrix.det_fin_two_mk, sub_neg_eq_add],
    ring_exp },
  symmetry,
  calc
  ∫ p, f p
      = ∫ p in polar_coord.source, f p : sorry
  ... = ∫ p in polar_coord.target, f (polar_coord.symm p) * abs((B p).det) : sorry
  ... = ∫ p in polar_coord.target, f (polar_coord.symm p) * p.1 :
  begin
    apply set_integral_congr (polar_coord.open_target.measurable_set) (λ x hx, _),
    rw [B_det, abs_of_pos],
    exact hx.1,
  end
end


#exit
