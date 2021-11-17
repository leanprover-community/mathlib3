/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import linear_algebra.quadratic_form.basic
import analysis.special_functions.pow

/-!
# Quadratic forms over the complex numbers

`equivalent_sum_squares`: A nondegenerate quadratic form over the complex numbers is equivalent to
a sum of squares.

-/

namespace quadratic_form

open_locale big_operators
open finset

variables {ι : Type*} [fintype ι]

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weights 1 or 0. -/
noncomputable def isometry_sum_squares [decidable_eq ι] (w' : ι → ℂ) :
  isometry (weighted_sum_squares ℂ w')
    (weighted_sum_squares ℂ (λ i, if w' i = 0 then 0 else 1 : ι → ℂ)) :=
begin
  let w := λ i, if h : w' i = 0 then (1 : units ℂ) else units.mk0 (w' i) h,
  have hw' : ∀ i : ι, (w i : ℂ) ^ - (1 / 2 : ℂ) ≠ 0,
  { intros i hi,
    exact (w i).ne_zero ((complex.cpow_eq_zero_iff _ _).1 hi).1 },
  convert (weighted_sum_squares ℂ w').isometry_basis_repr
    ((pi.basis_fun ℂ ι).units_smul (λ i, (is_unit_iff_ne_zero.2 $ hw' i).unit)),
  ext1 v,
  erw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • ((is_unit_iff_ne_zero.2 $ hw' i).unit : ℂ) •
    (pi.basis_fun ℂ ι) i) j = v j • w j ^ - (1 / 2 : ℂ),
  { rw [finset.sum_apply, sum_eq_single j, pi.basis_fun_apply, is_unit.unit_spec,
        linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_same,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij,
    rw [pi.basis_fun_apply, linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply,
        function.update_noteq hij.symm, pi.zero_apply, smul_eq_mul, smul_eq_mul,
        mul_zero, mul_zero],
    intro hj', exact false.elim (hj' hj) },
  simp_rw basis.units_smul_apply,
  erw [hsum, smul_eq_mul],
  split_ifs,
  { simp only [h, zero_smul, zero_mul]},
  have hww' : w' j = w j,
  { simp only [w, dif_neg h, units.coe_mk0] },
  simp only [hww', one_mul],
  change v j * v j = ↑(w j) * ((v j * ↑(w j) ^ -(1 / 2 : ℂ)) * (v j * ↑(w j) ^ -(1 / 2 : ℂ))),
  suffices : v j * v j = w j ^ - (1 / 2 : ℂ) * w j ^ - (1 / 2 : ℂ) * w j * v j * v j,
  { rw [this], ring },
  rw [← complex.cpow_add _ _ (w j).ne_zero, show - (1 / 2 : ℂ) + - (1 / 2) = -1, by ring,
      complex.cpow_neg_one, inv_mul_cancel (w j).ne_zero, one_mul],
end

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable def isometry_sum_squares_units [decidable_eq ι] (w : ι → units ℂ) :
  isometry (weighted_sum_squares ℂ w) (weighted_sum_squares ℂ (1 : ι → ℂ)) :=
begin
  have hw1 : (λ i, if (w i : ℂ) = 0 then 0 else 1 : ι → ℂ) = 1,
  { ext i : 1, exact dif_neg (w i).ne_zero },
  have := isometry_sum_squares (coe ∘ w),
  rw hw1 at this,
  exact this,
end

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squares {M : Type*} [add_comm_group M] [module ℂ M]
  [finite_dimensional ℂ M] (Q : quadratic_form ℂ M) (hQ : (associated Q).nondegenerate) :
  equivalent Q (weighted_sum_squares ℂ (1 : fin (finite_dimensional.finrank ℂ M) → ℂ)) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ in
  ⟨hw₁.trans (isometry_sum_squares_units w)⟩

end quadratic_form
