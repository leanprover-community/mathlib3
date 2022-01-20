/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import data.set.lattice

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `data.set.intervals.basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `data.set.lattice`, including `disjoint`.
-/

universes u v w

variables {ι : Sort u} {α : Type v} {β : Type w}

open set order_dual (to_dual)

namespace set

section preorder
variables [preorder α] {a b c : α}

@[simp] lemma Iic_disjoint_Ioi (h : a ≤ b) : disjoint (Iic a) (Ioi b) :=
λ x ⟨ha, hb⟩, not_le_of_lt (h.trans_lt hb) ha

@[simp] lemma Iic_disjoint_Ioc (h : a ≤ b) : disjoint (Iic a) (Ioc b c) :=
(Iic_disjoint_Ioi h).mono (le_refl _) (λ _, and.left)

@[simp] lemma Ioc_disjoint_Ioc_same {a b c : α} : disjoint (Ioc a b) (Ioc b c) :=
(Iic_disjoint_Ioc (le_refl b)).mono (λ _, and.right) (le_refl _)

@[simp] lemma Ico_disjoint_Ico_same {a b c : α} : disjoint (Ico a b) (Ico b c) :=
λ x hx, not_le_of_lt hx.1.2 hx.2.1

@[simp] lemma Ici_disjoint_Iic : disjoint (Ici a) (Iic b) ↔ ¬(a ≤ b) :=
by rw [set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]

@[simp] lemma Iic_disjoint_Ici : disjoint (Iic a) (Ici b) ↔ ¬(b ≤ a) :=
disjoint.comm.trans Ici_disjoint_Iic

end preorder

section linear_order
variables [linear_order α] {a₁ a₂ b₁ b₂ : α}

@[simp] lemma Ico_disjoint_Ico : disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ :=
by simp_rw [set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff,
  inf_eq_min, sup_eq_max, not_lt]

@[simp] lemma Ioc_disjoint_Ioc : disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ :=
have h : _ ↔ min (to_dual a₁) (to_dual b₁) ≤ max (to_dual a₂) (to_dual b₂) := Ico_disjoint_Ico,
by simpa only [dual_Ico] using h

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
lemma eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α}
  (h : disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂) (h2 : x₂ ∈ Ico y₁ y₂) :
  y₁ = x₂ :=
begin
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h,
  apply le_antisymm h2.1,
  exact h.elim (λ h, absurd hx (not_lt_of_le h)) id
end

@[simp] lemma Union_Ico_eq_Iio_self_iff {f : ι → α} {a : α} :
  (⋃ i, Ico (f i) a) = Iio a ↔ ∀ x < a, ∃ i, f i ≤ x :=
by simp [← Ici_inter_Iio, ← Union_inter, subset_def]

@[simp] lemma Union_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} :
  (⋃ i, Ioc a (f i)) = Ioi a ↔ ∀ x, a < x → ∃ i, x ≤ f i :=
by simp [← Ioi_inter_Iic, ← inter_Union, subset_def]

@[simp] lemma bUnion_Ico_eq_Iio_self_iff {p : ι → Prop} {f : Π i, p i → α} {a : α} :
  (⋃ i (hi : p i), Ico (f i hi) a) = Iio a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x :=
by simp [← Ici_inter_Iio, ← Union_inter, subset_def]

@[simp] lemma bUnion_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : Π i, p i → α} {a : α} :
  (⋃ i (hi : p i), Ioc a (f i hi)) = Ioi a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi :=
by simp [← Ioi_inter_Iic, ← inter_Union, subset_def]

end linear_order

end set

section Union_Ixx

variables [linear_order α] {s : set α} {a : α} {f : ι → α}

lemma is_glb.bUnion_Ioi_eq (h : is_glb s a) : (⋃ x ∈ s, Ioi x) = Ioi a :=
begin
  refine (bUnion_subset $ λ x hx, _).antisymm (λ x hx, _),
  { exact Ioi_subset_Ioi (h.1 hx) },
  { rcases h.exists_between hx with ⟨y, hys, hay, hyx⟩,
    exact mem_bUnion hys hyx }
end

lemma is_glb.Union_Ioi_eq (h : is_glb (range f) a) :
  (⋃ x, Ioi (f x)) = Ioi a :=
bUnion_range.symm.trans h.bUnion_Ioi_eq

lemma is_lub.bUnion_Iio_eq (h : is_lub s a) :
  (⋃ x ∈ s, Iio x) = Iio a :=
h.dual.bUnion_Ioi_eq

lemma is_lub.Union_Iio_eq (h : is_lub (range f) a) :
  (⋃ x, Iio (f x)) = Iio a :=
h.dual.Union_Ioi_eq

end Union_Ixx
