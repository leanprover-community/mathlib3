/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import data.set.lattice
import data.set.pointwise


/-! # Stuff to put somewhere in mathlib

Various lemmas on intersection and complement

The first part could go to `data.set.lattice`,
the second to `data.set.pointwise`

-/

open function
open_locale pointwise

variables {α β  G X : Type*} {ι : Sort*} {κ : ι → Sort*}


namespace set

section set

@[simp] lemma Inter_of_empty (s : ι → set α) [is_empty ι] : (⋂ i, s i) = univ := infi_of_empty _
@[simp] lemma Union_of_empty (s : ι → set α) [is_empty ι] : (⋃ i, s i) = ∅ := supr_of_empty _

lemma image_Inter [nonempty ι] {f : α → β} (hf : injective f) (s : ι → set α) :
  (f '' ⋂ (i : ι), s i) = ⋂ i, f '' s i :=
begin
  refine (image_Inter_subset _ _).antisymm (λ b hb, _),
  rw mem_Inter at hb,
  obtain ⟨a, -, rfl⟩ := hb (classical.arbitrary _),
  exact mem_image_of_mem _ (mem_Inter.2 $ λ i, hf.mem_set_image.1 $ hb _),
end

end set

section mul_action

variables [group α] [mul_action α β]

@[simp] lemma smul_compl_set (a : α) (s : set β) : a • sᶜ = (a • s)ᶜ :=
image_compl_eq $ mul_action.bijective _

lemma smul_set_Inter (a : α) (s : ι → set β) : a • (⋂ i, s i) = ⋂ i, a • (s i) :=
begin
  obtain _ | _ := is_empty_or_nonempty ι,
  { unfreezingI { refine eq.trans _ (Inter_of_empty _).symm },
    rw Inter_of_empty,
    exact smul_set_univ },
  { unfreezingI { exact image_Inter (mul_action.injective _) _ } }
end

lemma smul_set_Inter₂ (a : α) (s : Π i, κ i → set β) : a • (⋂ i j, s i j) = ⋂ i j, a • (s i j) :=
by simp_rw smul_set_Inter

open_locale classical

lemma smul_set_card_eq (a : α) (s : set β) [fintype s] : fintype.card ↥(a • s) = fintype.card s :=
begin
  change fintype.card ↥((λ x, a • x) '' s) = _,
  simp_rw set.image_eq_range (λ x, a • x) s,
  rw set.card_range_of_injective,
  apply subtype.restrict_injective,
  exact mul_action.injective a
end

end mul_action

end set
