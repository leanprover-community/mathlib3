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

/-- A version of Lagrange's theorem. -/
@[to_additive "A version of Lagrange's theorem."]
lemma card_mul_card_image_coe' (s t : finset α) :
  t.mul_stab.card * (s.image coe : finset (α ⧸ stabilizer α t)).card = (s * t.mul_stab).card :=
begin
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  have := quotient_group.preimage_mk_equiv_subgroup_times_set (stabilizer α t)
    (coe '' (s : set α) : set (α ⧸ stabilizer α t)),
  have that : ↥(stabilizer α t) = ↥t.mul_stab,
  { rw [←subgroup.coe_sort_coe, ←coe_mul_stab ht, finset.coe_sort_coe] },
  have temp := this.trans (equiv.prod_congr (equiv.cast that) (equiv.refl _ )),
  rw to_name s t ht at temp,
  replace temp := fintype.card_congr temp,
  simp only [← coe_mul, fintype.card_prod, fintype.card_coe, fintype.card_of_finset, to_finset_coe] at temp,
  rw [← temp],
  simp only [fintype.card_of_finset, mem_coe, iff_self, forall_const]
end

@[to_additive]
lemma card_mul_card_eq_mul_stab_card_mul_coe (s t : finset α) :
  (s * t).card = (s * t).mul_stab.card *
  ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))).card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  have := quotient_group.preimage_mk_equiv_subgroup_times_set (stabilizer α (s * t))
    (coe '' ((s : set α) * ↑t) : set (α ⧸ stabilizer α (s * t))),
  have that : ↥(stabilizer α (s * t)) = ↥(s * t).mul_stab,
  { rw [←subgroup.coe_sort_coe, ←coe_mul_stab (hs.mul ht), finset.coe_sort_coe] },
  have temp := this.trans (equiv.prod_congr (equiv.cast that) (equiv.refl _ )),
  rw to_name_also s t at temp,
  replace temp := fintype.card_congr temp,
  have h1 : fintype.card ↥(((s * t) : finset α) : set α) = fintype.card ↥(s * t) := by congr,
  simp_rw [← coe_mul s t, h1, fintype.card_coe, coe_mul, fintype.card_prod,
    fintype.card_of_finset, fintype.card_coe, ← coe_mul s t, to_finset_coe] at temp,
  exact temp
end

/-- A version of Lagrange's theorem. -/
@[to_additive "A version of Lagrange's theorem."]
lemma card_mul_card_image_coe (s t : finset α) :
  (s * t).mul_stab.card *
  ((s.image coe : finset (α ⧸ stabilizer α (s * t))) *
  (t.image coe : finset (α ⧸ stabilizer α (s * t)))).card = (s * t).card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  have := quotient_group.preimage_mk_equiv_subgroup_times_set (stabilizer α (s * t))
    (((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) *
    ((t : set α).image coe : set (α ⧸ stabilizer α (s * t)))),
  have image_coe_mul :
    (((s : set α) * t).image coe : set (α ⧸ stabilizer α (s * t))) =
      (s : set α).image coe * (t : set α).image coe,
  { exact set.image_mul (quotient_group.mk' _ : α →* α ⧸ stabilizer α (s * t)) },
  rw ← image_coe_mul at this,
  rw to_name_also s t at this,
  rw image_coe_mul at this,
  have that : (stabilizer α (s * t) × ↥(((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) *
    ((t : set α).image coe : set (α ⧸ stabilizer α (s * t))))) =
    ((s * t).mul_stab × ↥(((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) *
    ((t : set α).image coe : set (α ⧸ stabilizer α (s * t))))),
  { rw [←subgroup.coe_sort_coe, ←coe_mul_stab (hs.mul ht), finset.coe_sort_coe] },
  have temp := this.trans (equiv.cast that),
  replace temp := fintype.card_congr temp,
  simp_rw ← finset.coe_mul s t at temp,
  simp only [fintype.card_prod, fintype.card_coe] at temp,
  have h1 : fintype.card ↥(((s * t) : finset α) : set α) = fintype.card ↥(s * t) := by congr,
  have h2 : ((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) * coe '' ↑t =
    ((s.image coe : finset (α ⧸ stabilizer α (s * t))) *
    t.image coe : finset (α ⧸ stabilizer α (s * t))) := by simp,
  have h3 : fintype.card ↥(((s : set α).image coe : set (α ⧸ stabilizer α (s * t)))  *
    coe '' (t : set α)) = fintype.card ↥((s.image coe : finset (α ⧸ stabilizer α (s * t))) *
    image coe t),
  { simp_rw h2,
    congr },
  simp only [h1, h3, fintype.card_coe] at temp,
  rw temp
end

@[to_additive]
lemma mul_stab_mul_ssubset_mul_stab {a b : α} {s t C : finset α} (hs₁ : (s ∩ a • C.mul_stab).nonempty)
  (ht₁ : (t ∩ b • C.mul_stab).nonempty) (hab : ¬ (a * b) • C.mul_stab ⊆ s * t) :
  (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab) ⊂ C.mul_stab :=
begin
  sorry
end

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
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  classical,
  obtain hstab | hstab := ne_or_eq (s * t).mul_stab 1,
  { have image_coe_mul :
      ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))) = s.image coe * t.image coe,
    { exact image_mul (quotient_group.mk' _ : α →* α ⧸ stabilizer α (s * t)) },
    have hmulstab1 : ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))).mul_stab = 1,
    { exact mul_stab_image_coe_quotient (hs.mul ht) },
    have := ih _ _ (s.image coe : finset (α ⧸ stabilizer α (s * t))) (t.image coe) rfl,
    rw ←image_coe_mul at this,
    have hineq : (s * t).mul_stab.card * ((s.image coe : finset (α ⧸ stabilizer α (s * t))).card +
      (t.image coe : finset (α ⧸ stabilizer α (s * t))).card - 1) ≤ (s * t).card,
    { simp only [hmulstab1, mul_one, card_one] at this,
      replace this := tsub_le_iff_right.mpr this,
      exact le_of_le_of_eq ((mul_le_mul_left (card_pos.mpr (mul_stab_nonempty.mpr (hs.mul ht)))).mpr this)
        (eq.symm (card_mul_card_eq_mul_stab_card_mul_coe s t)) },
    -- now to prove that (s * (s * t).mul_stab).card = (s * t).mul_stab * (s.image coe) and analogous statement for s and t interchanged
    -- this will conclude the proof of the first case immediately
    { rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mul_card_image_coe',
        card_mul_card_image_coe'] at hineq,
      convert hineq using 1,
      exact add_comm _ _ },
    { rw [←image_coe_mul, hn],
      refine add_lt_add_of_lt_of_le _ card_image_le,
      rw card_mul_card_eq_mul_stab_card_mul_coe s t,
      apply lt_mul_left (card_pos.mpr _) _,
      { simp only [nonempty.image_iff, mul_nonempty, hs.mul ht], },
      { apply lt_of_le_of_ne (nat.one_le_iff_ne_zero.mpr
          (card_ne_zero_of_mem (one_mem_mul_stab.mpr (hs.mul ht)))) _,
        contrapose! hstab,
        exact card_mul_stab_eq_one.mp (eq.symm hstab) } } },
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ⊢ ih,
  replace ih := λ s t h, @ih _ h α _ _ s t rfl,
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial,
  { rw [card_singleton, card_singleton_mul, add_comm] },
  have : b / a ∉ stabilizer α t,
  { refine λ h, hab _,
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
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left _ _, (not_subset _ _).2 ⟨_, hb, λ h, hbac $ inter_subset_right _ _ h⟩⟩,
  clear_dependent a b,
  set convergent : set (finset α) :=
    {C | C ⊆ s * t ∧ (s ∩ t).card + ((s ∪ t) * C.mul_stab).card ≤ C.card + C.mul_stab.card},
  have convergent_nonempty : convergent.nonempty,
  { refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_right (card_le_of_subset $
      subset_mul_left _ $ one_mem_mul_stab.2 $ hst.mul $ hs.mono $ subset_union_left _ _) _).trans $
      ih (s ∩ t) (s ∪ t) _⟩,
    rw hn,
    exact add_lt_add_of_le_of_lt (card_le_of_subset inter_mul_union_subset) (card_lt_card hsts) },
  let C := argmin_on (λ C : finset α, C.mul_stab.card) is_well_founded.wf _ convergent_nonempty,
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argmin_on_mem _ _ _ _,
  have hCmin : ∀ D : finset α, D ∈ convergent → C.mul_stab.card ≤ D.mul_stab.card :=
    λ D, argmin_on_le (λ D : finset α, D.mul_stab.card) _ _,
  clear_value C,
  set H := C.mul_stab with hH,
  obtain rfl | hC := C.eq_empty_or_nonempty,
  { simpa [hst.ne_empty, hH] using hCcard },
  -- If the stabilizer of `C` is trivial, then
  -- `s.card + t.card - 1 = (s ∩ t).card + (s ∪ t).card - 1.card = ≤ C.card ≤ (s * t).card`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mul_stab.2 hC),
  { simp only [hH, hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard,
    exact hCcard.trans (add_le_add_right (card_le_of_subset hCst) _) },
  exfalso,
  have : ¬ s * t * H ⊆ s * t,
  { rw [mul_subset_left_iff (hs.mul ht), hstab, ←coe_subset, coe_one],
    exact hCstab.not_subset_singleton },
  simp_rw [mul_subset_iff_left, not_forall, mem_mul] at this,
  obtain ⟨_, ⟨a, b, ha, hb, rfl⟩, hab⟩ := this,
  set s₁ := s ∩ a • H with hs₁,
  set s₂ := s ∩ b • H with hs₂,
  set t₁ := t ∩ b • H with ht₁,
  set t₂ := t ∩ a • H with ht₂,
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.mpr ⟨1, ⟨one_mem_mul_stab.mpr hC, by simp only [smul_eq_mul, mul_one]⟩⟩⟩,
  have hs₁ne : s₁.nonempty := finset.nonempty_of_ne_empty (finset.ne_empty_of_mem has₁),
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.mpr ⟨1, one_mem_mul_stab.mpr hC, by simp only [smul_eq_mul, mul_one]⟩⟩,
  have ht₁ne : t₁.nonempty := finset.nonempty_of_ne_empty (finset.ne_empty_of_mem hbt₁),
  set C₁ := C ∪ (s₁ * t₁) with hC₁,
  set C₂ := C ∪ (s₂ * t₂) with hC₂,
  set H₁ := (s₁ * t₁).mul_stab with hH₁,
  set H₂ := (s₂ * t₂).mul_stab with hH₂,
  sorry
end

end finset
