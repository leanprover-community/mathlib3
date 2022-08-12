/-
Copyright (c) 2022 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import data.finset.pointwise
import group_theory.quotient_group

/-!
# Kneser's theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`.

## Main declarations

* `finset.mul_stab`: The stabilizer of a **nonempty** finset as a finset.
* `finset.mul_kneser`: Kneser's theorem.

## References

* [Imre Ruzsa, *Sumsets and structure][ruzsa2009]
-/

attribute [simp] finset.singleton_inj

open_locale pointwise

namespace set
variables {α β γ : Type*}

section
variables [has_smul α β] [has_smul α γ]

@[to_additive] lemma smul_image (f : β → γ) (s : set β) (a : α) :
  (∀ b, a • f b = f (a • b)) → a • f '' s = f '' (a • s) :=
image_comm

end

variables [monoid α] [monoid β]

@[to_additive] lemma image_smul' (f : α →* β) (s : set α) (a : α) : f '' (a • s) = f a • f '' s :=
image_comm $ map_mul _ _

end set

namespace subgroup
variables {α : Type*} [group α] {H : subgroup α} [subgroup.normal H] {s t : set α}

open set

@[to_additive]
lemma image_coe_quotient (H : subgroup α) [H.normal] : (coe : α → α ⧸ H) '' H = 1 :=
begin
  ext a,
  dsimp,
  split,
  { rintro ⟨a, ha, rfl⟩,
    rwa [quotient_group.eq_one_iff] },
  { rintro rfl,
    exact ⟨1, H.one_mem, rfl⟩ }
end

@[to_additive] lemma preimage_image_coe (s : set α) : (coe : α → α ⧸ H) ⁻¹' (coe '' s) = H * s :=
begin
  ext a,
  split,
  { rintro ⟨b, hb, h⟩,
    refine ⟨a / b, b, (quotient_group.eq_one_iff _).1 _, hb, div_mul_cancel' _ _⟩,
    simp only [h, quotient_group.coe_div, div_self'] },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    refine ⟨b, hb, _⟩,
    simpa only [quotient_group.coe_mul, self_eq_mul_left, quotient_group.eq_one_iff] }
end

@[to_additive]
lemma image_coe_inj : (coe : α → α ⧸ H) '' s = (coe : α → α ⧸ H) '' t ↔ ↑H * s = H * t :=
by { simp_rw ←preimage_image_coe,
  exact quotient_group.mk_surjective.preimage_injective.eq_iff.symm }

end subgroup

namespace mul_action
variables {α β γ : Type*} [group α] [mul_action α β] [mul_action α γ] {a : α}

open function set

section set

@[simp, to_additive] lemma stabilizer_empty : stabilizer α (∅ : set β) = ⊤ :=
subgroup.coe_eq_univ.1 $ eq_univ_of_forall $ λ a, smul_set_empty

@[simp, to_additive] lemma stabilizer_singleton (b : β) :
  stabilizer α ({b} : set β) = stabilizer α b :=
by { ext, simp }

@[to_additive] lemma mem_stabilizer_set {s : set β} :
  a ∈ stabilizer α s ↔ ∀ ⦃b⦄, a • b ∈ s ↔ b ∈ s :=
begin
  refine ⟨λ h b, _, λ h, _⟩,
  { rw [←(smul_mem_smul_set_iff : a • b ∈ a • s ↔ _), mem_stabilizer_iff.1 h] },
  simp_rw [mem_stabilizer_iff, set.ext_iff, mem_smul_set_iff_inv_smul_mem],
  exact ((mul_action.to_perm a).forall_congr' $ by simp [iff.comm]).1 h,
end

@[to_additive] lemma map_stabilizer_le (f : α →* α) (s : set α) :
  (stabilizer α s).map f ≤ stabilizer α (f '' s) :=
begin
  rintro a,
  simp only [subgroup.mem_map, mem_stabilizer_iff, exists_prop, forall_exists_index, and_imp],
  rintro a ha rfl,
  rw [←image_smul', ha],
end

@[simp, to_additive] lemma stabilizer_mul (s : set α) : (stabilizer α s : set α) * s = s :=
begin
  ext,
  refine ⟨_, λ h, ⟨_, _, (stabilizer α s).one_mem, h, one_mul _⟩⟩,
  rintro ⟨a, b, ha, hb, rfl⟩,
  rw ←mem_stabilizer_iff.1 ha,
  exact smul_mem_smul_set hb,
end

lemma le_stabilizer_smul_left [has_smul β γ] [is_scalar_tower α β γ] (b : β) (c : γ) :
  stabilizer α b ≤ stabilizer α (b • c) :=
by { simp_rw [set_like.le_def, mem_stabilizer_iff, ←smul_assoc], rintro a h, rw h }

@[to_additive]
lemma le_stabilizer_smul_right [has_smul β γ] [smul_comm_class α β γ] (b : β) (c : γ) :
  stabilizer α c ≤ stabilizer α (b • c) :=
by { simp_rw [set_like.le_def, mem_stabilizer_iff, smul_comm], rintro a h, rw h }

@[simp] lemma stabilizer_smul_left [group β] [mul_action β γ] [is_scalar_tower α β β] (b c : β) :
  stabilizer α (b • c) = stabilizer α b :=
(le_stabilizer_smul_left _ _).antisymm' $ λ a ha,
  by { dsimp at ha, rwa [←smul_mul_assoc, mul_left_inj] at ha }

@[simp, to_additive]
lemma stabilizer_smul_right [group β] [mul_action β γ] [smul_comm_class α β γ] (b : β) (c : γ) :
  stabilizer α (b • c) = stabilizer α c :=
(le_stabilizer_smul_right _ _).antisymm' $ (le_stabilizer_smul_right b⁻¹ _).trans_eq $
  by rw inv_smul_smul

end set

section
variables [decidable_eq β]

@[simp, to_additive] lemma stabilizer_coe_finset (s : finset β) :
  stabilizer α (s : set β) = stabilizer α s :=
by { ext, simp [←finset.coe_smul_finset] }

@[simp, to_additive] lemma stabilizer_finset_empty : stabilizer α (∅ : finset β) = ⊤ :=
subgroup.coe_eq_univ.1 $ eq_univ_of_forall finset.smul_finset_empty

@[simp, to_additive] lemma stabilizer_finset_singleton (b : β) :
  stabilizer α ({b} : finset β) = stabilizer α b :=
by { ext, simp }

end

end mul_action

namespace mul_action
variables {α : Type*} [comm_group α] {s : set α}

open function set
open_locale pointwise

@[simp, to_additive] lemma mul_stabilizer (s : set α) : s * (stabilizer α s : set α) = s :=
by rw [mul_comm, stabilizer_mul]

@[to_additive] lemma stabilizer_image_coe_quotient (s : set α) :
  stabilizer (α ⧸ stabilizer α s) ((coe : α → α ⧸ stabilizer α s) '' s) = ⊥ :=
begin
  ext a,
  induction a using quotient_group.induction_on',
  simp only [mem_stabilizer_iff, subgroup.mem_bot, quotient_group.eq_one_iff],
  have : ↑a • (coe : α → α ⧸ stabilizer α s) '' s = coe '' (a • s) :=
    (image_smul' (quotient_group.mk' _) _ _).symm,
  rw this,
  refine ⟨λ h, _, λ h, by rw h⟩,
  rwa [subgroup.image_coe_inj, mul_smul_comm, stabilizer_mul] at h,
end

end mul_action

open mul_action

namespace finset
variables {ι α : Type*}

/-! ### Stabilizer of a finset -/

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

@[to_additive] lemma mul_stab_subset_div (s : finset α) : s.mul_stab ⊆ s / s := filter_subset _ _

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

@[simp, to_additive] lemma mul_stab_empty : mul_stab (∅ : finset α) = ∅ := by simp [mul_stab]
@[simp, to_additive] lemma mul_stab_singleton (a : α) : mul_stab ({a} : finset α) = 1 :=
by simp [mul_stab, singleton_one]

@[to_additive] lemma nonempty.of_mul_stab : s.mul_stab.nonempty → s.nonempty :=
by { simp_rw [nonempty_iff_ne_empty, not_imp_not], rintro rfl, exact mul_stab_empty }

@[simp, to_additive] lemma one_mem_mul_stab : (1 : α) ∈ s.mul_stab ↔ s.nonempty :=
⟨λ h, nonempty.of_mul_stab ⟨_, h⟩, λ h, (mem_mul_stab h).2 $ one_smul _ _⟩

@[to_additive] lemma nonempty.mul_stab (h : s.nonempty) : s.mul_stab.nonempty :=
⟨_, one_mem_mul_stab.2 h⟩

@[simp, to_additive] lemma mul_stab_nonempty : s.mul_stab.nonempty ↔ s.nonempty :=
⟨nonempty.of_mul_stab, nonempty.mul_stab⟩

lemma subset_mul_stab_mul_left (ht : t.nonempty) : s.mul_stab ⊆ (s * t).mul_stab :=
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

end group

variables [comm_group α] [decidable_eq α] {s t : finset α} {a : α}

@[to_additive] lemma mul_stab_subset_div_left (ha : a ∈ s) : s.mul_stab ⊆ {a} / s :=
begin
  refine λ b hb, mem_div.2 ⟨_, _, mem_singleton_self _, _, div_div_cancel _ _⟩,
  rw mem_mul_stab ⟨a, ha⟩ at hb,
  rwa [←hb, ←inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha,
end

lemma subset_mul_stab_mul_right (hs : s.nonempty) : t.mul_stab ⊆ (s * t).mul_stab :=
by { rw mul_comm, exact subset_mul_stab_mul_left hs }

@[simp, to_additive] lemma mul_mul_stab (s : finset α) : s * s.mul_stab = s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact mul_empty _ },
  { rw [←coe_inj, coe_mul, coe_mul_stab hs, ←stabilizer_coe_finset, mul_stabilizer] }
end

section classical
open_locale classical

@[to_additive] lemma mul_stab_image_coe_quotient (hs : s.nonempty) :
  (s.image coe : finset (α ⧸ stabilizer α s)).mul_stab = 1 :=
begin
  refine coe_injective _,
  rw [coe_mul_stab (hs.image _), ←stabilizer_coe_finset, ←stabilizer_coe_finset, coe_image, coe_one,
    stabilizer_image_coe_quotient, subgroup.coe_bot, set.singleton_one],
end

/-- A version of Lagrange's theorem. -/
@[to_additive "A version of Lagrange's theorem."]
lemma card_mul_card_image_coe (s t : finset α) :
  s.card * (t.image coe : finset (α ⧸ stabilizer α s)).card = (s * t).card :=
sorry

end classical

/-! ### Kneser's theorem -/

/-- **Kneser's theorem**: A bound on the size of `s * t` in terms of its stabilizer. -/
@[to_additive "**Kneser's theorem**: A bound on the size of `s + t` in terms of its stabilizer."]
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
      ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))) = s.image coe * t.image coe :=
    sorry, -- image_mul quotient_group.mk',
    have : ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))).mul_stab = 1,
    { exact mul_stab_image_coe_quotient (hs.mul ht) },
    have := ih _ _ (s.image coe : finset (α ⧸ stabilizer α (s * t))) (t.image coe) rfl,
    rw ←image_coe_mul at this,
    sorry,
    { rw [←image_coe_mul, hn],
      refine add_lt_add_of_lt_of_le _ card_image_le,
      sorry } },
  have hs' : s.card = 1 ∨ 1 < s.card := sorry,
  rw [card_eq_one, one_lt_card] at hs',
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs',
  { simp_rw [hstab, card_singleton_mul, mul_one, add_comm t.card] },
  sorry,
end

end finset
