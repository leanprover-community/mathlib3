/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.integral_closure
import data.padics.padic_integers

open algebra

theorem is_integrally_closed_int_rat : is_integrally_closed ℤ ℚ :=
{ inj := int.cast_injective,
  closed :=
  begin
    rintros r ⟨f, hf, hr⟩,
    lift r to ℤ, { exact ⟨r, rfl⟩ },
    by_contradiction H,
    let p := nat.min_fac r.denom,
    have hp : p.prime := nat.min_fac_prime H,
    rw [f.as_sum, finset.sum_range_succ,
      alg_hom.map_add, add_eq_zero_iff_eq_neg] at hr,
    replace hr := congr_arg (padic_val_rat p) hr,
    refine ne_of_lt _ hr, clear hr,
    have := hf.leading_coeff, rw [leading_coeff] at this,
    rw [this, C_1, one_mul],
    rw [padic_val_rat.neg, ← finset.sum_hom (aeval ℤ ℚ r), is_monoid_hom.map_pow (aeval ℤ ℚ r)],
    rw [aeval_def, eval₂_X],
    replace : r ≠ 0, { rintro rfl, apply H, refl },
    resetI,
    rw [padic_val_rat.pow p this],
  end }

lemma is_integrally_closed (p : ℕ) [p.prime] : is_integrally_closed ℤ_[p] ℚ_[p] :=
{ inj := subtype.val_injective,
  closed :=
  begin
    rintros x ⟨f, f_monic, hf⟩,
    have bleh : eval₂ (algebra_map ℚ_[p]) x ((finset.range (nat_degree f)).sum (λ (i : ℕ), C (coeff f i) * X^i)) =
      ((finset.range (nat_degree f)).sum (λ (i : ℕ), eval₂ (algebra_map ℚ_[p]) x $ C (coeff f i) * X^i)),
    { exact (finset.sum_hom _).symm },
    erw subtype.val_range,
    show ∥x∥ ≤ 1,
    rw [f_monic.as_sum, aeval_def, eval₂_add, eval₂_pow, eval₂_X] at hf,
    rw [bleh] at hf,
    replace hf := congr_arg (@has_norm.norm ℚ_[p] _) hf,
    contrapose! hf with H,
    apply ne_of_gt,
    rw [norm_zero, padic_norm_e.add_eq_max_of_ne],
    { apply lt_of_lt_of_le _ (le_max_left _ _),
      rw [← fpow_of_nat, normed_field.norm_fpow],
      apply fpow_pos_of_pos,
      exact lt_trans zero_lt_one H, },
    { apply ne_of_gt,
      apply lt_of_le_of_lt (padic.norm_sum _ _),
      rw finset.fold_max_lt,
      split,
      { rw [← fpow_of_nat, normed_field.norm_fpow], apply fpow_pos_of_pos, exact lt_trans zero_lt_one H },
      { intros i hi,
        suffices : ∥algebra_map ℚ_[p] (coeff f i)∥ * ∥x∥ ^ i < ∥x∥ ^ nat_degree f,
        by simpa [eval₂_pow],
        refine lt_of_le_of_lt (mul_le_of_le_one_left _ _ : _ ≤ ∥x∥ ^ i) _,
        { rw [← fpow_of_nat], apply fpow_nonneg_of_nonneg, exact norm_nonneg _ },
        { exact (coeff f i).property },
        { rw [← fpow_of_nat, ← fpow_of_nat, (fpow_strict_mono H).lt_iff_lt],
          rw finset.mem_range at hi, exact_mod_cast hi, } } }
  end }
