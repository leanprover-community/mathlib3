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
  { have one_lt_p : (1:ℚ) < p := by exact_mod_cast hp.one_lt,
    rw [← neg_nonpos, ← (fpow_strict_mono one_lt_p).le_iff_le],
    norm_cast }
end

lemma rat.denom_eq_one_iff_padic_val_rat_pos (r : ℚ) :
  r.denom = 1 ↔ (∀ p : ℕ, p.prime → 0 ≤ padic_val_rat p r) :=
begin
  split; intro H,
  { intros p hp, delta padic_val_rat,
    split_ifs, { simp [H] }, { trivial } },
  { contrapose! H,
    let p := nat.min_fac r.denom,
    have hp : p.prime := nat.min_fac_prime H,
    have hpdenom : p ∣ r.denom := nat.min_fac_dvd _,
    use [p, hp],
    rw [padic_val_rat, dif_pos],
    { apply sub_neg_of_lt,
      rw [int.coe_nat_lt, ← enat.coe_lt_coe, enat.coe_get, enat.coe_get],
      by_contradiction h, push_neg at h,
      rw multiplicity.multiplicity_le_multiplicity_iff at h,
      specialize h 1, rw pow_one at h, norm_cast at h, specialize h hpdenom,
      have hpnum : p ∣ r.num.nat_abs := int.dvd_nat_abs_of_of_nat_dvd h,
      have cop : nat.gcd _ _ = 1 := r.cop,
      apply hp.not_dvd_one,
      rw ← cop,
      exact nat.dvd_gcd hpnum hpdenom },
    { split, { rintro rfl, exact H rfl }, { exact hp.ne_one } } }
end

lemma rat.denom_eq_one_iff_padic_norm_le_one (r : ℚ) :
  r.denom = 1 ↔ (∀ p : ℕ, p.prime → by exactI ∥(r : ℚ_[p])∥ ≤ 1) :=
calc r.denom = 1 ↔ (∀ p : ℕ, p.prime → 0 ≤ padic_val_rat p r) :
    rat.denom_eq_one_iff_padic_val_rat_pos r
  ... ↔ (∀ p : ℕ, p.prime → by exactI ∥(r : ℚ_[p])∥ ≤ 1) :
    forall_congr $ λ p, forall_congr $ λ hp,
      by exactI padic_val_rat_pos_iff_padic_norm_le_one p r

lemma padic.norm_sum (p : ℕ) [p.prime] {α : Type*} [decidable_eq α] (s : finset α) (f : α → ℚ_[p]) :
  ∥s.sum f∥ ≤ s.fold max 0 (λ a, ∥f a∥) :=
begin
  apply finset.induction_on s, { simp, },
  clear s,
  intros a s ha IH,
  rw [finset.sum_insert ha, finset.fold_insert ha],
  refine le_trans (padic_norm_e.nonarchimedean _ _) (max_le _ _),
  { apply le_max_left, },
  { refine le_trans IH (le_max_right _ _), }
end

lemma padic_int.is_integrally_closed (p : ℕ) [p.prime] : is_integrally_closed ℤ_[p] ℚ_[p] :=
{ inj := subtype.val_injective,
  closed :=
  begin
    rintros x ⟨f, hf, hx⟩,
    erw subtype.val_range,
    show ∥x∥ ≤ 1,
    rw [hf.as_sum, alg_hom.map_add, ← finset.sum_hom (aeval ℤ_[p] ℚ_[p] x)] at hx,
    replace hx := congr_arg (@has_norm.norm ℚ_[p] _) hx,
    contrapose! hx with H,
    apply ne_of_gt,
    rw [norm_zero, padic_norm_e.add_eq_max_of_ne],
    { apply lt_of_lt_of_le _ (le_max_left _ _),
      rw [is_monoid_hom.map_pow (aeval ℤ_[p] ℚ_[p] x), aeval_X,
        ← fpow_of_nat, normed_field.norm_fpow],
      apply fpow_pos_of_pos,
      exact lt_trans zero_lt_one H, },
    { apply ne_of_gt,
      refine lt_of_le_of_lt (padic.norm_sum _ _ _) _,
      rw finset.fold_max_lt,
      split,
      { rw [is_monoid_hom.map_pow (aeval ℤ_[p] ℚ_[p] x), aeval_X,
          ← fpow_of_nat, normed_field.norm_fpow],
        apply fpow_pos_of_pos, exact lt_trans zero_lt_one H },
      { intros i hi,
        suffices : ∥algebra_map ℚ_[p] (coeff f i)∥ * ∥x∥ ^ i < ∥x∥ ^ nat_degree f,
        by simpa [aeval_def, eval₂_pow],
        refine lt_of_le_of_lt (mul_le_of_le_one_left _ _ : _ ≤ ∥x∥ ^ i) _,
        { rw [← fpow_of_nat], apply fpow_nonneg_of_nonneg, exact norm_nonneg _ },
        { exact (coeff f i).property },
        { rw [← fpow_of_nat, ← fpow_of_nat, (fpow_strict_mono H).lt_iff_lt],
          rw finset.mem_range at hi, exact_mod_cast hi, } } }
  end }

theorem int.is_integrally_closed : is_integrally_closed ℤ ℚ :=
{ inj := int.cast_injective,
  closed :=
  begin
    rintros r ⟨f, hf, hr⟩,
    suffices : r.denom = 1,
    { lift r to ℤ using this, exact ⟨r, rfl⟩ },
    rw rat.denom_eq_one_iff_padic_norm_le_one,
    intros p hp, resetI,
    suffices : is_integral ℤ_[p] (r:ℚ_[p]),
    { replace := (padic_int.is_integrally_closed p).closed _ this,
      erw subtype.val_range at this, exact this, },
    use [f.map coe, monic_map coe hf],
    replace hr := congr_arg (coe : ℚ → ℚ_[p]) hr,
    rw rat.cast_zero at hr,
    rw [aeval_def, ← polynomial.eval_map, polynomial.map_map],
    have : (λ x : ℤ, algebra_map ℚ_[p] (x : ℤ_[p])) = (algebra_map ℚ_[p]) ∘ (algebra_map ℚ : ℤ → ℚ),
    { change algebra_map ℚ_[p] ∘ (coe : ℤ → ℤ_[p]) = _,
      calc _ = int.cast : int.eq_cast' _
         ... = _        : (int.eq_cast' _).symm },
    rw [this, ← hr], clear this,
    rw [aeval_def],
    symmetry,
    have := polynomial.hom_eval₂ f (algebra_map ℚ : ℤ → ℚ) (algebra_map ℚ_[p] : ℚ → ℚ_[p]) r,
    convert this,
    let g := ((algebra_map ℚ_[p]) ∘ (algebra_map ℚ : ℤ → ℚ)),
    let tmp₃ : _ := _,
    refine @polynomial.eval_map ℤ ℚ_[p] _ f _ ((algebra_map ℚ_[p]) ∘ (algebra_map ℚ : ℤ → ℚ)) tmp₃ r,
    refine @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
  end }
