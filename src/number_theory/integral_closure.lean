/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.integral_closure
import data.padics.padic_integers

open algebra polynomial

lemma padic_val_rat_pos_iff_padic_norm_le_one (p : ℕ) [hp : nat.prime p] (r : ℚ) :
   0 ≤ padic_val_rat p r ↔ ∥(r : ℚ_[p])∥ ≤ 1 :=
begin
  rw [padic_norm_e.eq_padic_norm, padic_norm],
  split_ifs with hr,
  { subst hr, rw padic_val_rat, rw dif_neg,
    { split; intros, { exact_mod_cast zero_le_one }, { trivial } },
    push_neg, left, trivial },
  { split; intros H,
    { norm_cast, rw [← neg_le_neg_iff, neg_zero] at H,
      rw fpow_strict_mono },
    }
end

lemma rat.denom_eq_one_iff_padic_val_rat_pos (r : ℚ) :
  r.denom = 1 ↔ (∀ p : ℕ, p.prime → 0 ≤ padic_val_rat p r) :=
sorry

lemma rat.denom_eq_one_iff_padic_val_le_one (r : ℚ) :
  r.denom = 1 ↔ (∀ p : ℕ, p.prime → by exactI ∥(r : ℚ_[p])∥ ≤ 1) :=
begin
  rw rat.denom_eq_one_iff_padic_val_rat_pos,
  apply forall_congr, intros p,
  apply forall_congr, intros hp, resetI,
  exact padic_val_rat_pos_iff_padic_norm_le_one p r
end

theorem int.is_integrally_closed : is_integrally_closed ℤ ℚ :=
{ inj := int.cast_injective,
  closed :=
  begin
    rintros r ⟨f, hf, hr⟩,
    suffices : r.denom = 1,
    { lift r to ℤ using this, exact ⟨r, rfl⟩ },
    contrapose! hr,
    let p := nat.min_fac r.denom,
    have hp : p.prime := nat.min_fac_prime hr,
    rw [hf.as_sum, alg_hom.map_add, add_eq_zero_iff_eq_neg],
    apply mt (congr_arg (padic_val_rat p)),
    apply ne_of_lt,
    rw [is_monoid_hom.map_pow (aeval ℤ ℚ r), aeval_X],
    rw [padic_val_rat.neg, ← finset.sum_hom (aeval ℤ ℚ r)],
    have : r ≠ 0, { rintro rfl, apply hr, refl },
    resetI,
    rw [padic_val_rat.pow p this],
  end }

lemma padic_int.is_integrally_closed (p : ℕ) [p.prime] : is_integrally_closed ℤ_[p] ℚ_[p] :=
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
