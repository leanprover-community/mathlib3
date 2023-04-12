/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.module
import data.set.intervals.unordered_interval

/-!
# PRs to open

Feel free to PR this!
-/

section
variables {α β : Type*} [linear_order α] {f : α → β} {s : set α} {a b : α}

lemma monotone_on.map_sup [semilattice_sup β] (hf : monotone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (a ⊔ b) = f a ⊔ f b :=
(le_total a b).elim (λ h, by simp only [h, hf ha hb h, sup_of_le_right])
  (λ h, by simp only [h, hf hb ha h, sup_of_le_left])

lemma monotone_on.map_inf [semilattice_inf β] (hf : monotone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (a ⊓ b) = f a ⊓ f b :=
hf.dual.map_sup ha hb
end

section
variables {α β : Type*} [linear_order α] {f : α → β} {s : set α} {a b : α}

lemma antitone_on.map_sup [semilattice_inf β] (hf : antitone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (a ⊔ b) = f a ⊓ f b :=
hf.dual_right.map_sup ha hb

lemma antitone_on.map_inf [semilattice_sup β] (hf : antitone_on f s) (ha : a ∈ s) (hb : b ∈ s) :
  f (a ⊓ b) = f a ⊔ f b :=
hf.dual_right.map_inf ha hb

end

section
open set
variables {α β : Type*} [linear_order α] [lattice β] {f : α → β} {a b : α}

lemma monotone_on.image_Icc_subset (hf : monotone_on f (Icc a b)) :
  f '' Icc a b ⊆ Icc (f a) (f b) :=
image_subset_iff.2 $ λ c hc,
  ⟨hf (left_mem_Icc.2 $ hc.1.trans hc.2) hc hc.1, hf hc (right_mem_Icc.2 $ hc.1.trans hc.2) hc.2⟩

lemma monotone.image_Icc_subset (hf : monotone f) : f '' Icc a b ⊆ Icc (f a) (f b) :=
(hf.monotone_on _).image_Icc_subset

lemma monotone_on.image_uIcc_subset (hf : monotone_on f (uIcc a b)) :
  f '' uIcc a b ⊆ uIcc (f a) (f b) :=
hf.image_Icc_subset.trans $
  by rw [hf.map_sup left_mem_uIcc right_mem_uIcc, hf.map_inf left_mem_uIcc right_mem_uIcc, uIcc]

lemma monotone.image_uIcc_subset (hf : monotone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
(hf.monotone_on _).image_uIcc_subset

end

section
open function
variables {α : Type*} [linear_order α] [has_mul α] [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)] {a b c d : α}

@[to_additive max_add_add_le_max_add_max] lemma max_mul_mul_le_max_mul_max' :
  max (a * b) (c * d) ≤ max a c * max b d :=
max_le (mul_le_mul' (le_max_left _ _) $ le_max_left _ _) $
  mul_le_mul' (le_max_right _ _) $ le_max_right _ _

--TODO: Also missing `min_mul_min_le_min_mul_mul`
@[to_additive min_add_min_le_min_add_add] lemma min_mul_min_le_min_mul_mul' :
  min a c * min b d ≤ min (a * b) (c * d) :=
le_min (mul_le_mul' (min_le_left _ _) $ min_le_left _ _) $
  mul_le_mul' (min_le_right _ _) $ min_le_right _ _

end

section
variables {α β : Type*} [linear_ordered_semiring α] [linear_ordered_add_comm_monoid β]
  [smul_with_zero α β] [ordered_smul α β] {a : α}

lemma smul_max (ha : 0 ≤ a) (b₁ b₂ : β) : a • max b₁ b₂ = max (a • b₁) (a • b₂) :=
(monotone_smul_left ha : monotone (_ : β → β)).map_max

lemma smul_min (ha : 0 ≤ a) (b₁ b₂ : β) : a • min b₁ b₂ = min (a • b₁) (a • b₂) :=
(monotone_smul_left ha : monotone (_ : β → β)).map_min

end

section
variables {α β : Type*} [linear_ordered_ring α] [linear_ordered_add_comm_group β]
  [module α β] [ordered_smul α β] {a : α}

lemma smul_max_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • max b₁ b₂ = min (a • b₁) (a • b₂) :=
(antitone_smul_left ha : antitone (_ : β → β)).map_max

lemma smul_min_of_nonpos (ha : a ≤ 0) (b₁ b₂ : β) : a • min b₁ b₂ = max (a • b₁) (a • b₂) :=
(antitone_smul_left ha : antitone (_ : β → β)).map_min

end
