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
lemma mul_stab_mul_ssubset_mul_stab {a b : α} {s t C : finset α}
  (hs₁ : (s ∩ a • C.mul_stab).nonempty) (ht₁ : (t ∩ b • C.mul_stab).nonempty)
  (hab : ¬ (a * b) • C.mul_stab ⊆ s * t) :
  ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab ⊂ C.mul_stab :=
begin
  have hCne : C.nonempty,
  { contrapose! hab,
    simp only [not_nonempty_iff_eq_empty] at hab,
    simp only [hab, mul_stab_empty, smul_finset_empty, empty_subset] },
  obtain ⟨x, hx⟩ := hs₁,
  obtain ⟨y, hy⟩ := ht₁,
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx),
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy),
  have hsubset : ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab ⊆ C.mul_stab,
  { have hxymem : x * y ∈ s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab) := mul_mem_mul hx hy,
    apply subset_trans (mul_stab_subset_div_right hxymem),
    have : s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab) ⊆ (x * y) • C.mul_stab,
    { apply subset_trans (mul_subset_mul (inter_subset_right s _) (inter_subset_right t _)),
      rw smul_mul_smul,
      rw [← hac, ← had, smul_mul_smul, smul_assoc],
      apply smul_finset_subset_smul_finset,
      rw [← smul_smul],
      rw mul_subset_iff,
      intros x hx y hy,
      rw [smul_mul_stab hd, smul_mul_stab hc, mem_mul_stab hCne, ← smul_smul,
        (mem_mul_stab hCne).mp hy, (mem_mul_stab hCne).mp hx] },
    apply subset_trans (div_subset_div_right this) _,
    have hsing : (x * y) • C.mul_stab = {x * y} * C.mul_stab,
    { rw singleton_mul; refl},
    simp_rw [hsing, singleton_mul, div_singleton, image_image, div_eq_mul_inv, comp,
      mul_comm _ (x * y)⁻¹, ← mul_assoc, mul_assoc, inv_mul_self (x * y), one_mul_eq_id, image_id,
      subset_refl] },
  have : (a * b) • C.mul_stab = ((a * c) * (b * d)) • C.mul_stab,
  { rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc,
      ← mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_self (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mul_stab hc, smul_mul_stab hd] },
  have hsub : (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab)) ⊆ (a * b) • C.mul_stab,
  { apply subset_trans (mul_subset_mul (inter_subset_right s _) (inter_subset_right t _)),
    simp only [smul_mul_smul, mul_stab_mul_mul_stab, subset_refl] },
  have hxy : x * y ∈ (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab) := mul_mem_mul hx hy,
  rw this at hsub,
  rw this at hab,
  obtain ⟨z, hz, hzst⟩ := (not_subset _ _).mp hab,
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz,
  refine (finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, _⟩,
  rw mem_mul_stab' ⟨x * y, hxy⟩,
  push_neg,
  refine ⟨(a * c * (b * d)), by convert hxy, _⟩,
  rw [smul_eq_mul, mul_comm, ← smul_eq_mul, hwz],
  exact not_mem_mono (mul_subset_mul (inter_subset_left s _) (inter_subset_left t _)) hzst
end

@[to_additive]
lemma inter_mul_stab_subset_mul_stab_union (s t : finset α) :
  s.mul_stab ∩ t.mul_stab ⊆ (s ∪ t).mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  { intros x hx,
    rw [mem_mul_stab (finset.nonempty.mono (subset_union_left s t) hs), smul_finset_union,
      (mem_mul_stab hs).mp (mem_of_mem_inter_left hx),
      (mem_mul_stab ht).mp (mem_of_mem_inter_right hx)], }
end

@[to_additive]
lemma mul_stab_eq_mul_stab_union {a b : α} {s t C : finset α}
  (hs₁ : (s ∩ a • C.mul_stab).nonempty) (ht₁ : (t ∩ b • C.mul_stab).nonempty)
  (hab : ¬ (a * b) • C.mul_stab ⊆ s * t)
  (hC : C ∩ ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)) = ∅) :
  ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab =
  (C ∪ (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab :=
begin
  have hCne : C.nonempty,
  { contrapose ht₁,
    simp only [not_nonempty_iff_eq_empty] at ht₁,
    simp only [ht₁, mul_stab_empty, smul_finset_empty, inter_empty,
      not_nonempty_empty, not_false_iff] },
  apply subset_antisymm,
  { refine subset_trans _ (inter_mul_stab_subset_mul_stab_union _ _),
    refine subset_trans _
      (inter_subset_inter_right (subset_of_ssubset (mul_stab_mul_ssubset_mul_stab hs₁ ht₁ hab))),
    simp only [inter_self, subset.refl] },
  { intros x hx,
    replace hx := (mem_mul_stab (nonempty.mono (subset_union_right _ _)
      (mul_nonempty.mpr ⟨hs₁, ht₁⟩))).mp hx,
    rw smul_finset_union at hx,
    have hxC : x ∈ C.mul_stab,
    { by_contra,
      have : x • C ∩ (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab)) ≠ ∅,
      { intros hempty,
        rw mem_mul_stab hCne at h,
        have hxC := union_subset_left (subset_of_eq hx),
        have : x • C ⊆ C,
        { intros y hy,
          cases (mem_union.mp (hxC hy)) with hymem hymem,
          { exact hymem },
          { exfalso,
            apply nonempty_iff_ne_empty.mp (⟨y, (mem_inter_of_mem hy hymem)⟩) hempty }},
        replace this := card_lt_card (ssubset_iff_subset_ne.mpr ⟨this, h⟩),
        simpa [card_smul_finset, lt_self_iff_false] },
      have hUn :
        C.bUnion (λ y, x • y • C.mul_stab) ∩ (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab)) ≠ ∅,
      { have hxsmul : x • C.bUnion (λ (y : α), y • C.mul_stab) =
          C.bUnion (λ (y : α), x • y • C.mul_stab) := finset.bUnion_image,
        simpa [← hxsmul, bUnion_smul_mul_stab C] },
      simp_rw [bUnion_inter, ← nonempty_iff_ne_empty, bUnion_nonempty,
        ← smul_assoc, smul_eq_mul] at hUn,
      obtain ⟨y, hy, hyne⟩ := hUn,
      have hxyCsubC : (x * y) • C.mul_stab ⊆ x • C,
      { rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff],
        conv_rhs { rw ←  bUnion_smul_mul_stab C },
        exact subset_bUnion_of_mem _ hy },
      have hxyC : (x * y) • C.mul_stab ∩ C = ∅,
      { apply or_iff_not_imp_left.mp
          (smul_mul_stab_subset_or_disj (x * y) (bUnion_smul_mul_stab C)),
        intro h,
        apply (finset.nonempty_iff_ne_empty.mp
            (finset.nonempty.mono (inter_subset_inter_right h) hyne)) hC },
      have hxysub : (x * y) • C.mul_stab ⊆ s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab),
      { have hxyCun := subset_trans hxyCsubC
          (subset_union_left _ (x • (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab)))),
        rw hx at hxyCun,
        intros w hw,
        have hwC : w ∉ C,
        { intro hwC,
          apply (not_ne_iff.mpr hxyC),
          rw ← nonempty_iff_ne_empty,
          exact ⟨w, mem_inter.mpr ⟨hw, hwC⟩⟩ },
        exact or_iff_not_imp_left.mp (mem_union.mp (hxyCun hw)) hwC },
      replace hxysub := card_le_of_subset hxysub,
      simp only [card_smul_finset] at hxysub,
      apply not_lt.mpr hxysub,
      suffices : (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab) ⊂ (a * b) • C.mul_stab,
      { convert card_lt_card this using 1,
        rw card_smul_finset },
      apply ssubset_of_subset_not_subset,
      { refine subset_trans (mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _)) _,
        simp only [smul_mul_smul, mul_stab_mul_mul_stab, subset_refl] },
      { contrapose! hab,
        exact subset_trans hab (mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)) }},
    rw (mem_mul_stab hCne).mp hxC at hx,
    rw mem_mul_stab (mul_nonempty.mpr ⟨hs₁, ht₁⟩),
    apply eq.symm (eq_of_subset_of_card_le _ _),
    { replace hx := (union_eq_union_iff_left.mp hx).2,
      intros w hw,
      have hwC : w ∉ C,
      { intro hwC,
        apply (not_ne_iff.mpr hC),
        rw ← nonempty_iff_ne_empty,
        exact ⟨w, mem_inter.mpr ⟨hwC, hw⟩⟩ },
        exact or_iff_not_imp_left.mp (mem_union.mp (hx hw)) hwC },
    { simp only [card_smul_finset] }}
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
  replace ih := λ s' t' h, @ih _ h α _ _ s' t' rfl,
  subst hn,
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

variables {s' t' : finset α}

@[to_additive] lemma mul_aux1 (hs' : s'.nonempty) (ht' : t'.nonempty)
  (ih : (s' * (s' * t').mul_stab).card + (t' * (s' * t').mul_stab).card
    ≤ (s' * t').card + (s' * t').mul_stab.card) :
  ((s ∪ t) * (s * t).mul_stab).card - ((s' ∪ t') * (s * t).mul_stab).card <
    (s * t).mul_stab.card - (s' * (s' * t').mul_stab).card - (t' * (s' * t').mul_stab).card :=
begin
  set H := (s * t).mul_stab with hH,
  set H' := (s' * t').mul_stab with hH',
  set C : finset α := sorry,
  set C' := C ∪ (s' * t') with hC',
  calc
    ((s ∪ t) * H).card - ((s' ∪ t') * H).card
        < C.card + H.card - (s ∩ t).card - (C'.card + H'.card - (s ∩ t).card) : sorry
    ... = H.card - ((s' * t').card + H'.card) : sorry
    ... ≤ H.card - ((s' * H').card + (t' * H').card) : tsub_le_tsub_left ih _
    ... = H.card - (s' * H').card - (t' * H').card : by rw tsub_tsub,
end

end finset
