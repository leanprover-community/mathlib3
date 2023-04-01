/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import combinatorics.additive.mathlib

/-!
# Stabilizer of a finset

This file defines the stabilizer of a finset of a group as a finset.

## Main declarations

* `finset.mul_stab`: The stabilizer of a **nonempty** finset as a finset.
-/

open function mul_action
open_locale pointwise

namespace finset
variables {ι α : Type*}

section group
variables [group α] [decidable_eq α] {s t : finset α} {a : α}

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`.-/
@[to_additive "The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`."]
def mul_stab (s : finset α) : finset α := (s / s).filter $ λ a, a • s = s

@[simp, to_additive]
lemma mem_mul_stab (hs : s.nonempty) : a ∈ s.mul_stab ↔ a • s = s :=
begin
  rw [mul_stab, mem_filter, mem_div, and_iff_right_of_imp],
  obtain ⟨b, hb⟩ := hs,
  exact λ h, ⟨_, _, by { rw ←h, exact smul_mem_smul_finset hb }, hb, mul_div_cancel'' _ _⟩,
end

@[to_additive] lemma mul_stab_subset_div : s.mul_stab ⊆ s / s := filter_subset _ _

@[to_additive] lemma mul_stab_subset_div_right (ha : a ∈ s) : s.mul_stab ⊆ s / {a} :=
begin
  refine λ b hb, mem_div.2 ⟨_, _, _, mem_singleton_self _, mul_div_cancel'' _ _⟩,
  rw mem_mul_stab ⟨a, ha⟩ at hb,
  rw ←hb,
  exact smul_mem_smul_finset ha,
end

@[simp, to_additive] lemma coe_mul_stab (hs : s.nonempty) :
  (s.mul_stab : set α) = mul_action.stabilizer α s :=
by { ext, simp [mem_mul_stab hs] }

@[to_additive] lemma mem_mul_stab_iff_subset_smul_finset (hs : s.nonempty) :
  a ∈ s.mul_stab ↔ s ⊆ a • s :=
by rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe, mem_stabilizer_finset_iff_subset_smul_finset]

@[to_additive] lemma mem_mul_stab_iff_smul_finset_subset (hs : s.nonempty) :
  a ∈ s.mul_stab ↔ a • s ⊆ s :=
by rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe, mem_stabilizer_finset_iff_smul_finset_subset]

@[to_additive] lemma mem_mul_stab' (hs : s.nonempty) : a ∈ s.mul_stab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s :=
by rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe, mem_stabilizer_finset']

@[simp, to_additive] lemma mul_stab_empty : mul_stab (∅ : finset α) = ∅ := by simp [mul_stab]
@[simp, to_additive] lemma mul_stab_singleton (a : α) : mul_stab ({a} : finset α) = 1 :=
by simp [mul_stab, singleton_one]

@[to_additive] lemma nonempty.of_mul_stab : s.mul_stab.nonempty → s.nonempty :=
by { simp_rw [nonempty_iff_ne_empty, not_imp_not], rintro rfl, exact mul_stab_empty }

@[simp, to_additive] lemma one_mem_mul_stab : (1 : α) ∈ s.mul_stab ↔ s.nonempty :=
⟨λ h, nonempty.of_mul_stab ⟨_, h⟩, λ h, (mem_mul_stab h).2 $ one_smul _ _⟩

alias one_mem_mul_stab ↔ _ nonempty.one_mem_mul_stab

attribute [protected, to_additive] nonempty.one_mem_mul_stab

@[to_additive] lemma nonempty.mul_stab (h : s.nonempty) : s.mul_stab.nonempty :=
⟨_, h.one_mem_mul_stab⟩

@[simp, to_additive] lemma mul_stab_nonempty : s.mul_stab.nonempty ↔ s.nonempty :=
⟨nonempty.of_mul_stab, nonempty.mul_stab⟩

@[simp, to_additive] lemma card_mul_stab_eq_one : s.mul_stab.card = 1 ↔ s.mul_stab = 1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨a, ha⟩ := card_eq_one.1 h,
    rw ha,
    rw [eq_singleton_iff_nonempty_unique_mem, mul_stab_nonempty, ←one_mem_mul_stab] at ha,
    rw [←ha.2 _ ha.1, singleton_one] },
  { rw [h, card_one] }
end

@[to_additive] lemma nonempty.mul_stab_nontrivial (h : s.nonempty) :
  s.mul_stab.nontrivial' ↔ s.mul_stab ≠ 1 :=
nontrivial_iff_ne_singleton h.one_mem_mul_stab

@[to_additive] lemma subset_mul_stab_mul_left (ht : t.nonempty) : s.mul_stab ⊆ (s * t).mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  simp_rw [subset_iff, mem_mul_stab hs, mem_mul_stab (hs.mul ht)],
  rintro a h,
  rw [←smul_mul_assoc, h],
end

@[simp, to_additive] lemma mul_stab_mul (s : finset α) : s.mul_stab * s = s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact mul_empty _ },
  refine coe_injective _,
  simp only [hs, coe_mul, coe_mul_stab, ←stabilizer_coe_finset, stabilizer_mul],
end

@[to_additive] lemma mul_subset_right_iff (ht : t.nonempty) : s * t ⊆ t ↔ s ⊆ t.mul_stab :=
by simp_rw [←smul_eq_mul, ←bUnion_smul_finset, bUnion_subset,
  ←mem_mul_stab_iff_smul_finset_subset ht, subset_iff]

@[to_additive] lemma mul_subset_right : s ⊆ t.mul_stab → s * t ⊆ t :=
begin
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  { exact (mul_subset_right_iff ht).2 }
end

@[to_additive]
lemma smul_mul_stab (ha : a ∈ s.mul_stab) : a • s.mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe] at ha,
  rw [←coe_inj, coe_smul_finset, coe_mul_stab hs, subgroup.smul_coe ha],
end

@[simp, to_additive]
lemma mul_stab_mul_mul_stab (s : finset α) : s.mul_stab * s.mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  { simp_rw [←smul_eq_mul, ← bUnion_smul_finset, bUnion_congr rfl (λ a, smul_mul_stab),
    ←sup_eq_bUnion, sup_const hs.mul_stab] }
end

@[to_additive]
lemma inter_mul_stab_subset_mul_stab_union : s.mul_stab ∩ t.mul_stab ⊆ (s ∪ t).mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  intros x hx,
  rw [mem_mul_stab (finset.nonempty.mono (subset_union_left s t) hs), smul_finset_union,
    (mem_mul_stab hs).mp (mem_of_mem_inter_left hx),
    (mem_mul_stab ht).mp (mem_of_mem_inter_right hx)],
end

end group

variables [comm_group α] [decidable_eq α] {s t : finset α} {a : α}

@[to_additive] lemma mul_stab_subset_div_left (ha : a ∈ s) : s.mul_stab ⊆ {a} / s :=
begin
  refine λ b hb, mem_div.2 ⟨_, _, mem_singleton_self _, _, div_div_cancel _ _⟩,
  rw mem_mul_stab ⟨a, ha⟩ at hb,
  rwa [←hb, ←inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha,
end

@[to_additive] lemma subset_mul_stab_mul_right (hs : s.nonempty) : t.mul_stab ⊆ (s * t).mul_stab :=
by { rw mul_comm, exact subset_mul_stab_mul_left hs }

@[simp, to_additive] lemma mul_mul_stab (s : finset α) : s * s.mul_stab = s :=
by { rw mul_comm, exact mul_stab_mul _ }

@[simp] lemma mul_mul_stab_mul_mul_mul_mul_stab_mul :
  s * (s * t).mul_stab * (t * (s * t).mul_stab) = s * t :=
by rw [mul_mul_mul_comm, mul_stab_mul_mul_stab, mul_mul_stab]

@[to_additive] lemma smul_finset_mul_stab_subset (ha : a ∈ s) : a • s.mul_stab ⊆ s :=
(smul_finset_subset_smul ha).trans s.mul_mul_stab.subset'

@[to_additive] lemma mul_subset_left_iff (hs : s.nonempty) : s * t ⊆ s ↔ t ⊆ s.mul_stab :=
by rw [mul_comm, mul_subset_right_iff hs]

@[to_additive] lemma mul_subset_left : t ⊆ s.mul_stab → s * t ⊆ s :=
by { rw mul_comm, exact mul_subset_right }

@[simp, to_additive] lemma mul_stab_idem (s : finset α) : s.mul_stab.mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  refine coe_injective _,
  rw [coe_mul_stab hs, coe_mul_stab hs.mul_stab, ←stabilizer_coe_finset, coe_mul_stab hs],
  simp,
end

@[simp, to_additive] lemma mul_stab_smul (a : α) (s : finset α) : (a • s).mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  refine coe_injective _,
  rw [coe_mul_stab hs, coe_mul_stab hs.smul_finset, stabilizer_smul_eq_right],
end

open_locale classical

@[to_additive] lemma mul_stab_image_coe_quotient (hs : s.nonempty) :
  (s.image coe : finset (α ⧸ stabilizer α s)).mul_stab = 1 :=
begin
  refine coe_injective _,
  rw [coe_mul_stab (hs.image _), ←stabilizer_coe_finset, ←stabilizer_coe_finset, coe_image, coe_one,
    stabilizer_image_coe_quotient, subgroup.coe_bot, set.singleton_one],
end

@[to_additive]
lemma to_name_mul (s t : finset α) (ht : t.nonempty):
  quotient_group.mk ⁻¹' (coe '' (s : set α) : set (α ⧸ stabilizer α t)) = s * t.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  convert (stabilizer α t).mul_alt_version s,
  refine eq.trans _ (set.Union_subtype _ _).symm,
  simp_rw [subgroup.mk_smul,← set_like.mem_coe, ← coe_mul_stab ht, ← coe_smul_finset,
    ← coe_bUnion, bUnion_smul_finset, smul_eq_mul, coe_mul, mul_comm]
end

@[to_additive]
lemma to_name_mul_also (s t : finset α) :
  quotient_group.mk ⁻¹' (coe '' ((s : set α) * ↑t) : set (α ⧸ stabilizer α (s * t))) = ↑s * ↑t :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  convert to_name_mul (s * t) (s * t) (hs.mul ht) using 1,
  { simp },
  { norm_cast,
    rw mul_mul_stab (s * t) }
end

@[to_additive] lemma pairwise_disjoint_smul_finset_mul_stab (s : finset α) :
  (set.range $ λ a : α, a • s.mul_stab).pairwise_disjoint id :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩,
  dsimp,
  simp_rw [←disjoint_coe, ←coe_injective.eq_iff, coe_smul_finset, coe_mul_stab hs],
  exact subgroup.pairwise_disjoint_smul _ (set.mem_range_self _) (set.mem_range_self _),
end

@[to_additive] lemma disjoint_smul_finset_mul_stab_mul_mul_stab :
  ¬ a • s.mul_stab ⊆ t * s.mul_stab → disjoint (a • s.mul_stab) (t * s.mul_stab) :=
begin
  simp_rw [@not_imp_comm (_ ⊆ _), ←smul_eq_mul, ←bUnion_smul_finset, disjoint_bUnion_right,
    not_forall],
  rintro ⟨b, hb, h⟩,
  rw s.pairwise_disjoint_smul_finset_mul_stab.eq (set.mem_range_self _) (set.mem_range_self _) h,
  exact subset_bUnion_of_mem _ hb,
end

@[to_additive] lemma card_mul_stab_dvd_card_mul_mul_stab (s t : finset α) :
  t.mul_stab.card ∣ (s * t.mul_stab).card :=
card_dvd_card_smul_right $ t.pairwise_disjoint_smul_finset_mul_stab.subset $
  set.image_subset_range _ _

@[to_additive] lemma card_mul_stab_dvd_card (s : finset α) : s.mul_stab.card ∣ s.card :=
by simpa only [mul_mul_stab] using s.card_mul_stab_dvd_card_mul_mul_stab s

/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mul_stab`. -/
@[to_additive "A fintype instance for the stabilizer of a nonempty finset `s` in terms of
`s.add_stab`."]
private def fintype_stabilizer_of_mul_stab (hs : s.nonempty) : fintype (stabilizer α s) :=
{ elems := s.mul_stab.attach.map ⟨subtype.map id $ λ _, (mem_mul_stab hs).1,
    subtype.map_injective _ injective_id⟩,
  complete := λ a, mem_map.2
    ⟨⟨_, (mem_mul_stab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mul_stab hs).2 a.2⟩, subtype.ext rfl⟩ }

@[to_additive] lemma card_mul_stab_dvd_card_mul_stab (hs : s.nonempty)
  (h : s.mul_stab ⊆ t.mul_stab) :
  s.mul_stab.card ∣ t.mul_stab.card :=
begin
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  rw [←coe_subset, coe_mul_stab hs, coe_mul_stab ht, set_like.coe_subset_coe] at h,
  letI : fintype (stabilizer α s) := fintype_stabilizer_of_mul_stab hs,
  letI : fintype (stabilizer α t) := fintype_stabilizer_of_mul_stab ht,
  convert subgroup.card_dvd_of_le h using 1; exact ((card_map _).trans card_attach).symm,
end

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
  rw to_name_mul s t ht at temp,
  replace temp := fintype.card_congr temp,
  simp only [←coe_mul, fintype.card_prod, fintype.card_coe, fintype.card_of_finset, to_finset_coe]
    at temp,
  rw ←temp,
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
  rw to_name_mul_also s t at temp,
  replace temp := fintype.card_congr temp,
  have h1 : fintype.card ↥(((s * t) : finset α) : set α) = fintype.card ↥(s * t) := by congr,
  simp_rw [← coe_mul s t, h1, fintype.card_coe, coe_mul, fintype.card_prod,
    fintype.card_of_finset, fintype.card_coe, ← coe_mul s t, to_finset_coe] at temp,
  exact temp
end

/-- A version of Lagrange's theorem. -/
@[to_additive "A version of Lagrange's theorem."]
lemma card_mul_card_image_coe (s t : finset α) :
  (s * t).mul_stab.card * (s.image coe * t.image coe : finset (α ⧸ stabilizer α (s * t))).card
    = (s * t).card :=
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
  rw [←image_coe_mul, to_name_mul_also, image_coe_mul] at this,
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

end finset
