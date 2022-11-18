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
disjoint_left.mpr $ λ x ha hb, (h.trans_lt hb).not_le ha

@[simp] lemma Iic_disjoint_Ioc (h : a ≤ b) : disjoint (Iic a) (Ioc b c) :=
(Iic_disjoint_Ioi h).mono le_rfl (λ _, and.left)

@[simp] lemma Ioc_disjoint_Ioc_same {a b c : α} : disjoint (Ioc a b) (Ioc b c) :=
(Iic_disjoint_Ioc (le_refl b)).mono (λ _, and.right) le_rfl

@[simp] lemma Ico_disjoint_Ico_same {a b c : α} : disjoint (Ico a b) (Ico b c) :=
disjoint_left.mpr $ λ x hab hbc, hab.2.not_le hbc.1

@[simp] lemma Ici_disjoint_Iic : disjoint (Ici a) (Iic b) ↔ ¬(a ≤ b) :=
by rw [set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]

@[simp] lemma Iic_disjoint_Ici : disjoint (Iic a) (Ici b) ↔ ¬(b ≤ a) :=
disjoint.comm.trans Ici_disjoint_Iic

@[simp] lemma Union_Iic : (⋃ a : α, Iic a) = univ := Union_eq_univ_iff.2 $ λ x, ⟨x, right_mem_Iic⟩
@[simp] lemma Union_Ici : (⋃ a : α, Ici a) = univ := Union_eq_univ_iff.2 $ λ x, ⟨x, left_mem_Ici⟩

@[simp] lemma Union_Icc_right (a : α) : (⋃ b, Icc a b) = Ici a :=
by simp only [← Ici_inter_Iic, ← inter_Union, Union_Iic, inter_univ]

@[simp] lemma Union_Ioc_right (a : α) : (⋃ b, Ioc a b) = Ioi a :=
by simp only [← Ioi_inter_Iic, ← inter_Union, Union_Iic, inter_univ]

@[simp] lemma Union_Icc_left (b : α) : (⋃ a, Icc a b) = Iic b :=
by simp only [← Ici_inter_Iic, ← Union_inter, Union_Ici, univ_inter]

@[simp] lemma Union_Ico_left (b : α) : (⋃ a, Ico a b) = Iio b :=
by simp only [← Ici_inter_Iio, ← Union_inter, Union_Ici, univ_inter]

@[simp] lemma Union_Iio [no_max_order α] : (⋃ a : α, Iio a) = univ :=
Union_eq_univ_iff.2 exists_gt

@[simp] lemma Union_Ioi [no_min_order α] : (⋃ a : α, Ioi a) = univ :=
Union_eq_univ_iff.2 exists_lt

@[simp] lemma Union_Ico_right [no_max_order α] (a : α) : (⋃ b, Ico a b) = Ici a :=
by simp only [← Ici_inter_Iio, ← inter_Union, Union_Iio, inter_univ]

@[simp] lemma Union_Ioo_right [no_max_order α] (a : α) : (⋃ b, Ioo a b) = Ioi a :=
by simp only [← Ioi_inter_Iio, ← inter_Union, Union_Iio, inter_univ]

@[simp] lemma Union_Ioc_left [no_min_order α] (b : α) : (⋃ a, Ioc a b) = Iic b :=
by simp only [← Ioi_inter_Iic, ← Union_inter, Union_Ioi, univ_inter]

@[simp] lemma Union_Ioo_left [no_min_order α] (b : α) : (⋃ a, Ioo a b) = Iio b :=
by simp only [← Ioi_inter_Iio, ← Union_inter, Union_Ioi, univ_inter]

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
  refine (Union₂_subset $ λ x hx, _).antisymm (λ x hx, _),
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

lemma is_glb.bUnion_Ici_eq_Ioi (a_glb : is_glb s a) (a_not_mem : a ∉ s) :
  (⋃ x ∈ s, Ici x) = Ioi a :=
begin
  refine (Union₂_subset $ λ x hx, _).antisymm (λ x hx, _),
  { exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) (λ h, (h ▸ a_not_mem) hx)), },
  { rcases a_glb.exists_between hx with ⟨y, hys, hay, hyx⟩,
    apply mem_Union₂.mpr ,
    refine ⟨y, hys, hyx.le⟩, },
end

lemma is_glb.bUnion_Ici_eq_Ici (a_glb : is_glb s a) (a_mem : a ∈ s) :
  (⋃ x ∈ s, Ici x) = Ici a :=
begin
  refine (Union₂_subset $ λ x hx, _).antisymm (λ x hx, _),
  { exact Ici_subset_Ici.mpr (mem_lower_bounds.mp a_glb.1 x hx), },
  { apply mem_Union₂.mpr,
    refine ⟨a, a_mem, hx⟩, },
end

lemma is_lub.bUnion_Iic_eq_Iio (a_lub : is_lub s a) (a_not_mem : a ∉ s) :
  (⋃ x ∈ s, Iic x) = Iio a :=
a_lub.dual.bUnion_Ici_eq_Ioi a_not_mem

lemma is_lub.bUnion_Iic_eq_Iic (a_lub : is_lub s a) (a_mem : a ∈ s) :
  (⋃ x ∈ s, Iic x) = Iic a :=
a_lub.dual.bUnion_Ici_eq_Ici a_mem

lemma Union_Ici_eq_Ioi_infi {R : Type*} [complete_linear_order R]
  {f : ι → R} (no_least_elem : (⨅ i, f i) ∉ range f) :
  (⋃ (i : ι), Ici (f i)) = Ioi (⨅ i, f i) :=
by simp only [← is_glb.bUnion_Ici_eq_Ioi (@is_glb_infi _ _ _ f) no_least_elem,
              mem_range, Union_exists, Union_Union_eq']

lemma Union_Iic_eq_Iio_supr {R : Type*} [complete_linear_order R]
  {f : ι → R} (no_greatest_elem : (⨆ i, f i) ∉ range f) :
  (⋃ (i : ι), Iic (f i)) = Iio (⨆ i, f i) :=
@Union_Ici_eq_Ioi_infi ι (order_dual R) _ f no_greatest_elem

lemma Union_Ici_eq_Ici_infi {R : Type*} [complete_linear_order R]
  {f : ι → R} (has_least_elem : (⨅ i, f i) ∈ range f) :
  (⋃ (i : ι), Ici (f i)) = Ici (⨅ i, f i) :=
by simp only [← is_glb.bUnion_Ici_eq_Ici (@is_glb_infi _ _ _ f) has_least_elem,
              mem_range, Union_exists, Union_Union_eq']

lemma Union_Iic_eq_Iic_supr {R : Type*} [complete_linear_order R]
  {f : ι → R} (has_greatest_elem : (⨆ i, f i) ∈ range f) :
  (⋃ (i : ι), Iic (f i)) = Iic (⨆ i, f i) :=
@Union_Ici_eq_Ici_infi ι (order_dual R) _ f has_greatest_elem

open_locale topological_space

open filter

lemma infi_eq_of_forall_le_of_tendsto {R : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  {x : R} {as : ι → R} (x_le : ∀ i, x ≤ as i) {F : filter ι} [filter.ne_bot F]
  (as_lim : filter.tendsto as F (𝓝 x)) :
  (⨅ i, as i) = x :=
begin
  refine infi_eq_of_forall_ge_of_forall_gt_exists_lt (λ i, x_le i) _,
  apply λ w x_lt_w, ne_bot.nonempty_of_mem ‹filter.ne_bot F› (eventually_lt_of_tendsto_lt x_lt_w as_lim),
end

lemma supr_eq_of_forall_le_of_tendsto {R : Type*}
  [complete_linear_order R] [topological_space R] [order_topology R]
  {x : R} {as : ι → R} (le_x : ∀ i, as i ≤ x) {F : filter ι} [filter.ne_bot F]
  (as_lim : filter.tendsto as F (𝓝 x)) :
  (⨆ i, as i) = x :=
@infi_eq_of_forall_le_of_tendsto ι (order_dual R) _ _ _ x as le_x F _ as_lim

end Union_Ixx
