/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import linear_algebra.quadratic_form.basic
import analysis.special_functions.pow
import data.real.sign

/-!
# Real quadratic forms

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegerate we can take the weights to be ±1,
as in `equivalent_one_zero_neg_one_weighted_sum_squared`.

-/

namespace quadratic_form

open_locale big_operators
open real finset

variables {ι : Type*} [fintype ι]

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometry_sign_weighted_sum_squares
  [decidable_eq ι] (w : ι → ℝ) :
  isometry (weighted_sum_squares ℝ w) (weighted_sum_squares ℝ (sign ∘ w)) :=
begin
  let u := λ i, if h : w i = 0 then (1 : ℝˣ) else units.mk0 (w i) h,
  have hu' : ∀ i : ι, (sign (u i) * u i) ^ - (1 / 2 : ℝ) ≠ 0,
  { intro i, refine (ne_of_lt (real.rpow_pos_of_pos
      (sign_mul_pos_of_ne_zero _ $ units.ne_zero _) _)).symm},
  convert ((weighted_sum_squares ℝ w).isometry_basis_repr
    ((pi.basis_fun ℝ ι).units_smul (λ i, (is_unit_iff_ne_zero.2 $ hu' i).unit))),
  ext1 v,
  rw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • ((is_unit_iff_ne_zero.2 $ hu' i).unit : ℝ) •
    (pi.basis_fun ℝ ι) i) j = v j • (sign (u j) * u j) ^ - (1 / 2 : ℝ),
  { rw [finset.sum_apply, sum_eq_single j, pi.basis_fun_apply, is_unit.unit_spec,
        linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_same,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij,
    rw [pi.basis_fun_apply, linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply,
        function.update_noteq hij.symm, pi.zero_apply, smul_eq_mul, smul_eq_mul,
        mul_zero, mul_zero],
    intro hj', exact false.elim (hj' hj) },
  simp_rw basis.units_smul_apply,
  erw [hsum],
  simp only [u, function.comp, smul_eq_mul],
  split_ifs,
  { simp only [h, zero_smul, zero_mul, sign_zero] },
  have hwu : w j = u j,
  { simp only [u, dif_neg h, units.coe_mk0] },
  simp only [hwu, units.coe_mk0],
  suffices : (u j : ℝ).sign * v j * v j = (sign (u j) * u j) ^ - (1 / 2 : ℝ) *
    (sign (u j) * u j) ^ - (1 / 2 : ℝ) * u j * v j * v j,
  { erw [← mul_assoc, this], ring },
  rw [← real.rpow_add (sign_mul_pos_of_ne_zero _ $ units.ne_zero _),
      show - (1 / 2 : ℝ) + - (1 / 2) = -1, by ring, real.rpow_neg_one, mul_inv,
      inv_sign, mul_assoc (sign (u j)) (u j)⁻¹,
      inv_mul_cancel (units.ne_zero _), mul_one],
  apply_instance
end

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared
  {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M]
  (Q : quadratic_form ℝ M) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ,
  (∀ i, w i = -1 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ in
  ⟨sign ∘ coe ∘ w,
   λ i, sign_apply_eq_of_ne_zero (w i) (w i).ne_zero,
   ⟨hw₁.trans (isometry_sign_weighted_sum_squares (coe ∘ w))⟩⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared
  {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M]
  (Q : quadratic_form ℝ M) :
  ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ,
  (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares in
  ⟨sign ∘ coe ∘ w,
   λ i, sign_apply_eq (w i),
   ⟨hw₁.trans (isometry_sign_weighted_sum_squares w)⟩⟩

end quadratic_form
