/-
Copyright (c) 2022 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import combinatorics.additive.mathlib

/-!
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`.

## Main declarations

* `finset.mul_stab`: The stabilizer of a **nonempty** finset as a finset.
* `finset.mul_kneser`: Kneser's theorem.

## References

* [Imre Ruzsa, *Sumsets and structure][ruzsa2009]
-/

open function mul_action
open_locale classical pointwise

variables {α : Type*} [comm_group α] [decidable_eq α] {s t : finset α} {a : α}

namespace finset

/-! ### Kneser's theorem -/

/-- **Kneser's multiplication theorem**: A bound on the size of `s * t` in terms of its stabilizer.
-/
@[to_additive "**Kneser's addition theorem**: A bound on the size of `s + t` in terms of its
stabilizer."]
lemma mul_kneser (s t : finset α) :
  (s * (s * t).mul_stab).card + (t * (s * t).mul_stab).card ≤
    (s * t).card + (s * t).mul_stab.card :=
begin
  /- We're doing induction on `(s * t).card + s.card` generalizing the group. This is a bit tricky
  in Lean -/
  set n := (s * t).card + s.card with hn,
  clear_value n,
  unfreezingI { induction n using nat.strong_induction_on with n ih generalizing α },
  obtain rfl | hs := s.eq_empty_or_nonempty,
  sorry { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  sorry { simp },
  classical,
  obtain hstab | hstab := ne_or_eq (s * t).mul_stab 1,
  sorry { have image_coe_mul :
      ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))) = s.image coe * t.image coe,
    { exact image_mul (quotient_group.mk' _ : α →* α ⧸ stabilizer α (s * t)) },
    have : ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))).mul_stab = 1,
    { exact mul_stab_image_coe_quotient (hs.mul ht) },
    have := ih _ _ (s.image coe : finset (α ⧸ stabilizer α (s * t))) (t.image coe) rfl,
    rw ←image_coe_mul at this,
    sorry,
    { rw [←image_coe_mul, hn],
      refine add_lt_add_of_lt_of_le _ card_image_le,
      sorry } },
  simp only [hstab, mul_one, card_one] at ⊢ ih,
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial,
  sorry { simp_rw [hstab, card_singleton_mul, mul_one, add_comm t.card] },
  have : b / a ∉ stabilizer α t,
  sorry { refine λ h, hab _,
    sorry },
  simp only [mem_stabilizer_finset', smul_eq_mul, not_forall, exists_prop] at this,
  obtain ⟨c, hc, hbac⟩ := this,
  set t' := (a / c) • t with ht',
  clear_value t',
  rw ←inv_smul_eq_iff at ht',
  subst ht',
  rename t' t,
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel'] at hc,
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ←mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac,
  rw smul_finset_nonempty at ht,
  simp only [mul_smul_comm, smul_mul_assoc, mul_stab_smul, card_smul_finset] at *,
  have hst : (s ∩ t).nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩,
  clear_dependent a b,
  set convergent : set (finset α) :=
    {C | C ⊆ s * t ∧ (s ∩ t).card + ((s ∪ t) * C.mul_stab).card ≤ C.card + C.mul_stab.card},
  have convergent_nonempty : convergent.nonempty,
  sorry { refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_right (card_le_of_subset $
      subset_mul_left _ $ one_mem_mul_stab.2 $ hst.mul $ hs.mono $ subset_union_left _ _) _).trans $
      ih _ _ (s ∩ t) (s ∪ t) rfl⟩,
    rw hn,
    refine add_lt_add_of_le_of_lt (card_le_of_subset inter_mul_union_subset) (card_lt_card
      ⟨inter_subset_left _ _, (not_subset _ _).2 ⟨_, hb, λ h, hbac $ inter_subset_right _ _ h⟩⟩) },
  let C := argmin_on (λ C : finset α, C.mul_stab.card) is_well_founded.wf _ convergent_nonempty,
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argmin_on_mem _ _ _ _,
  clear_value C,
  obtain rfl | hC := C.eq_empty_or_nonempty,
  sorry { simpa [hst.ne_empty] using hCcard },
  -- If the stabilizer of `C` is trivial, then
  -- `s.card + t.card - 1 = (s ∩ t).card + (s ∪ t).card - 1.card = ≤ C.card ≤ (s * t).card`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mul_stab.2 hC),
  { simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard,
    exact hCcard.trans (add_le_add_right (card_le_of_subset hCst) _) },
  sorry
end

end finset
