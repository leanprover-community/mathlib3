/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import ring_theory.ideal.basic
import ring_theory.ideal.operations
import linear_algebra.finsupp
import ring_theory.graded_algebra.basic

/-!

# Homogeneous ideal of a graded algebra

This file defines homogeneous ideals of `graded_algebra A` where `A : ι → ideal R`and operations on
them:
* `mul`, `inf`, `Inf` of homogeneous ideals are homogeneous;
* `⊤`, `⊥`, i.e. the trivial ring and `R` are homogeneous;
* `radical` of a homogeneous ideal is homogeneous.
-/

open_locale big_operators pointwise

section is_homogeneous_ideal_defs

open set_like direct_sum set

lemma ideal.is_homogeneous.exists_subset_iff_eq_span :
  (∃ s : set A, s ⊆ set_of (is_homogeneous 𝒜) ∧ I = ideal.span s) ↔
    I = ideal.span (I ∩ set_of (is_homogeneous 𝒜)) :=
begin
  split,
  { rintros ⟨s, hs, rfl⟩,
    apply le_antisymm,
    { exact ideal.span_mono (subset_inter ideal.subset_span hs) },
    { exact ideal.span_le.2 (inter_subset_left _ _) } },
  { intros hI,
    exact ⟨_, inter_subset_right _ _, hI⟩, }
end

variables [decidable_eq ι] [add_comm_monoid ι]  [graded_algebra 𝒜]

/--An `I : ideal R` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def ideal.is_homogeneous : Prop :=
∀ (i : ι) ⦃r : A⦄, r ∈ I → (graded_algebra.decompose 𝒜 r i : A) ∈ I

lemma ideal.is_homogeneous_iff_forall_subset :
  ideal.is_homogeneous 𝒜 I ↔ ∀ i, (I : set A) ⊆ graded_algebra.proj 𝒜 i ⁻¹' I :=
iff.rfl

lemma ideal.is_homogeneous_iff_subset_Inter :
  ideal.is_homogeneous 𝒜 I ↔ (I : set A) ⊆ ⋂ i, graded_algebra.proj 𝒜 i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma ideal.is_homogeneous.exists_iff_eq_span :
  (∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S)) ↔
  I = ideal.span {x | x ∈ I ∧ is_homogeneous 𝒜 x} :=
(subtype.exists_set_subtype _).trans (ideal.is_homogeneous.exists_subset_iff_eq_span _ _)

lemma mul_homogeneous_element_mem_of_mem
  {I : ideal A} (r x : A) (hx₁ : is_homogeneous 𝒜 x) (hx₂ : x ∈ I) (j : ι) :
  graded_algebra.proj 𝒜 j (r * x) ∈ I :=
begin
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw [←graded_algebra.sum_support_decompose 𝒜 r, finset.sum_mul, linear_map.map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (graded_algebra.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) := graded_monoid.mul_mem
    (submodule.coe_mem _) hi,
  rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem 𝒜 mem₁,
    coe_of_submodule_apply 𝒜, submodule.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end

lemma ideal.is_homogeneous.iff_eq :
  ideal.is_homogeneous 𝒜 I ↔ I = ideal.span {x | x ∈ I ∧ is_homogeneous 𝒜 x} :=
⟨ λ hI, begin
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  ext, split; intro hx,
  { rw ←graded_algebra.sum_support_decompose 𝒜 x,
    refine ideal.sum_mem _ _,
    intros j hj,
    rw ideal.mem_span, intros J HJ,
    refine HJ ⟨hI j hx, j, submodule.coe_mem _⟩, },
  { rw [ideal.mem_span] at hx,
    apply hx,
    exact inter_subset_left _ _, },
  end,
  λ hI, begin
    intros i r hr,
    rw ←graded_algebra.proj_apply,
    rw [ideal.span, finsupp.span_eq_range_total] at hI,
    rw hI at hr,
    obtain ⟨s, rfl⟩ := hr,
    simp_rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum, smul_eq_mul],
    refine ideal.sum_mem I _,
    rintros ⟨j, ⟨hj₁, hj₂⟩⟩ hj₃,
    exact mul_homogeneous_element_mem_of_mem _ _ _ hj₂ hj₁ _,
  end ⟩

lemma ideal.is_homogeneous.iff_eq_homogeneous_core :
  I.is_homogeneous 𝒜 ↔ I = ideal.homogeneous_core 𝒜 I :=
begin
  rw [ideal.homogeneous_core, image_preimage_eq_inter_range,
    subtype.range_coe, ideal.is_homogeneous.iff_eq],
  refl
end

lemma ideal.is_homogeneous.iff_exists :
  ideal.is_homogeneous 𝒜 I ↔ ∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S) :=
by rw [ideal.is_homogeneous.exists_iff_eq_span, ideal.is_homogeneous.iff_eq]

end is_homogeneous_ideal_defs

section operations

open set_like direct_sum set

variables {ι R : Type*} [comm_ring R] [decidable_eq ι] [add_comm_monoid ι]
variables (A : ι → ideal R) [graded_algebra A]
variable (I : ideal R)

/--For any `comm_ring R`, we collect the homogeneous ideals of `R` into a type.-/
abbreviation homogeneous_ideal : Type* := { I : ideal A // ideal.is_homogeneous 𝒜 I }

lemma ideal.is_homogeneous.bot : ideal.is_homogeneous 𝒜 ⊥ := λ i r hr,
begin
  simp only [ideal.mem_bot] at hr,
  rw [hr, alg_equiv.map_zero, zero_apply],
  apply ideal.zero_mem
end

instance homogeneous_ideal.inhabited : inhabited (homogeneous_ideal 𝒜) :=
{ default := ⟨⊥, ideal.is_homogeneous.bot _⟩}

instance homogeneous_ideal.has_top :
  has_top (homogeneous_ideal 𝒜) :=
⟨⟨⊤, λ _ _ _, by simp only [submodule.mem_top]⟩⟩

@[simp] lemma homogeneous_ideal.eq_top_iff
  (I : homogeneous_ideal 𝒜) : I = ⊤ ↔ I.1 = ⊤ :=
⟨ λ h, by { rw h, refl },
  λ h, begin
    have h' : I.val = (⊤ : homogeneous_ideal 𝒜).val,
    rw h, refl,
    apply subtype.val_injective h',
  end ⟩

instance homogeneous_ideal.order : partial_order (homogeneous_ideal 𝒜) :=
partial_order.lift _ subtype.coe_injective

instance homogeneous_ideal.has_mem : has_mem A (homogeneous_ideal 𝒜) :=
{ mem := λ r I, r ∈ I.1 }

variables {𝒜}

lemma ideal.is_homogeneous.inf {I J : ideal A}
  (HI : ideal.is_homogeneous 𝒜 I) (HJ : ideal.is_homogeneous 𝒜 J) :
  ideal.is_homogeneous 𝒜 (I ⊓ J) :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma homogeneous_ideal.Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  ideal.is_homogeneous 𝒜 (Inf ℐ) :=
begin
  intros i x Hx, simp only [ideal.mem_Inf] at Hx ⊢,
  intros J HJ,
  exact h _ HJ _ (Hx HJ),
end

lemma ideal.is_homogeneous.mul {I J : ideal A}
  (HI : ideal.is_homogeneous 𝒜 I) (HJ : ideal.is_homogeneous 𝒜 J) :
  ideal.is_homogeneous 𝒜 (I * J) :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw [ideal.span_mul_span'],
  refine ⟨s₁ * s₂, _⟩,
  apply congr_arg,
  ext, split; intro hx,
  { rw set.mem_mul at hx,
    obtain ⟨y1, y2, h1, h2, h3⟩ := hx,
    rw set.mem_image at h1, obtain ⟨z1, h1⟩ := h1,
    have hy1 : y1 ∈ set_like.homogeneous_submonoid 𝒜,
    rw ←h1.2, exact z1.2,
    rw set.mem_image at h2, obtain ⟨z2, h2⟩ := h2,
    have hy2 : y2 ∈ set_like.homogeneous_submonoid 𝒜,
    rw ←h2.2, exact z2.2,

    use y1 * y2, apply submonoid.mul_mem,
    exact hy1, exact hy2,
    refine ⟨_, h3⟩, rw set.mem_mul, use y1, assumption,
    use y2, assumption, tidy, },
  { rw set.mem_image at hx,
    obtain ⟨y, hy1, hy⟩ := hx,
    rw set.mem_mul at hy1 ⊢,
    obtain ⟨z1, z2, hz1, hz2, hz3⟩ := hy1,
    use z1, use z2, split, rw set.mem_image, use z1, refine ⟨hz1, rfl⟩,
    split, rw set.mem_image, use z2, refine ⟨hz2, rfl⟩, tidy, }
end

lemma ideal.is_homogeneous.sup {I J : ideal A}
  (HI : ideal.is_homogeneous 𝒜 I) (HJ : ideal.is_homogeneous 𝒜 J) :
  ideal.is_homogeneous 𝒜 (I ⊔ J) :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

lemma ideal.is_homogeneous.Sup {ℐ : set (ideal A)} (Hℐ : ∀ (I ∈ ℐ), ideal.is_homogeneous 𝒜 I) :
  ideal.is_homogeneous 𝒜 (Sup ℐ) :=
begin
  simp_rw [ideal.is_homogeneous.iff_exists] at Hℐ,
  set 𝓈 : ℐ → set (homogeneous_submonoid 𝒜) := λ I : ℐ, Exists.some (Hℐ I _) with 𝓈_eq,
  have h𝓈 : ∀ I : ℐ, I.1 = ideal.span (coe '' 𝓈 I) := λ I : ℐ, Exists.some_spec (Hℐ I _),
  rw ideal.is_homogeneous.iff_exists,
  use sUnion (set.range 𝓈),
  rw [sUnion_range, image_Union, ideal.span, submodule.span_Union],
  ext r, split,
  { suffices : Sup ℐ ≤ _, revert r, exact this,
    rw Sup_le_iff, intros I HI,
    have ineq1 : I ≤ ideal.span I := ideal.subset_span, refine le_trans ineq1 _,
    rw ideal.span_le, simp only [coe_subset_coe, ideal.submodule_span_eq], intros x hx,
    rw submodule.mem_supr, intros J HJ,
    apply HJ ⟨I, HI⟩, rw ←h𝓈 ⟨I, HI⟩, assumption },
  { suffices : _ ≤  Sup ℐ, revert r, exact this,
    rw supr_le_iff, intros I, rw submodule.span_le, intros x hx,
    simp only [mem_image] at hx, obtain ⟨x', hx1, hx2⟩ := hx,
    simp only [mem_coe, subtype.val_eq_coe], dsimp only at hx1,
    apply ideal.mem_Sup_of_mem, use I.2,
    simp only [subtype.val_eq_coe] at h𝓈 ⊢, rw h𝓈,
    refine ideal.subset_span _, rw [mem_image], use x', refine ⟨hx1, hx2⟩, },
  intros I, exact I.2,
end

variables (𝒜)

instance : has_inf (homogeneous_ideal 𝒜) :=
{ inf := λ I J, ⟨I ⊓ J, I.prop.inf J.prop⟩ }

instance : has_Inf (homogeneous_ideal 𝒜) :=
{ Inf := λ ℐ, ⟨Inf (coe '' ℐ), homogeneous_ideal.Inf $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

instance : has_sup (homogeneous_ideal 𝒜) :=
{ sup := λ I J, ⟨I ⊔ J, I.prop.sup J.prop⟩ }

instance : has_Sup (homogeneous_ideal 𝒜) :=
{ Sup := λ ℐ, ⟨Sup (coe '' ℐ), ideal.is_homogeneous.Sup $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

instance : has_mul (homogeneous_ideal 𝒜) :=
{ mul := λ I J, ⟨I * J, I.prop.mul J.prop⟩ }

instance : has_add (homogeneous_ideal 𝒜) := ⟨(⊔)⟩

end operations

section homogeneous_core

variables {ι R A : Type*} [comm_ring R] [comm_ring A]
variables [algebra R A] [decidable_eq ι] [add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.is_homogeneous.homogeneous_core :
  ideal.is_homogeneous 𝒜 (ideal.homogeneous_core 𝒜 I) :=
begin
  rw ideal.is_homogeneous.iff_exists,
  exact ⟨_, rfl⟩,
end

lemma ideal.is_homogeneous.homogeneous_core_eq_self [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]
  (h : ideal.is_homogeneous 𝒜 I) :
  ideal.homogeneous_core 𝒜 I = I :=
begin
  ext x, split; intros hx,
  { apply ideal.homogeneous_core_le_ideal 𝒜, exact hx, },
  { rw ←graded_algebra.sum_support_decompose 𝒜 x,
    refine ideal.sum_mem _ _,
    intros i hi, rw ←(ideal.is_homogeneous.iff_eq_homogeneous_core 𝒜 I).mp h,
    apply h, exact hx, },
end

lemma ideal.homogeneous_core.eq_Sup [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)] :
  ideal.homogeneous_core 𝒜 I = Sup { J : ideal A| ideal.is_homogeneous 𝒜 J ∧ J ≤ I } :=
begin
  ext, split; intros hx,
  { rw [ideal.homogeneous_core, ideal.span, mem_span_set] at hx,
    obtain ⟨c, hc1, hc2⟩ := hx,
    rw ←hc2, refine ideal.sum_mem _ _,
    intros r hc, dsimp only, rw [smul_eq_mul], refine ideal.mul_mem_left _ _ _,
    have hr0 := hc1 hc, rw [mem_image] at hr0,
    have hr1 : is_homogeneous 𝒜 r,
    { obtain ⟨⟨x, ⟨k, hx1⟩⟩, hx2, rfl⟩ := hr0,
      use k, exact hx1, },
    obtain ⟨i, hi⟩ := hr1,
    have mem1 : ideal.span {r} ∈ {J : ideal A | ideal.is_homogeneous 𝒜 J ∧ J ≤ I},
    { split, rw ideal.is_homogeneous.iff_exists,
      refine ⟨{(⟨r, ⟨i, hi⟩⟩ : homogeneous_submonoid 𝒜)}, _⟩,
      congr, simp only [image_singleton, subtype.coe_mk], rw ideal.span_le,
      simp only [mem_coe, singleton_subset_iff],
      { obtain ⟨⟨x, ⟨k, hx1⟩⟩, hx2, rfl⟩ := hr0,  rw mem_preimage at hx2, exact hx2, }, },
    apply ideal.mem_Sup_of_mem mem1, rw ideal.mem_span_singleton },
  { have hom1 := ideal.is_homogeneous.homogeneous_core 𝒜 I,
    have hom2 : ideal.is_homogeneous 𝒜 (Sup {J : ideal A | ideal.is_homogeneous 𝒜 J ∧ J ≤ I}),
    { apply ideal.is_homogeneous.Sup, rintros J ⟨HJ1, HJ2⟩, exact HJ1, },
    rw [ideal.homogeneous_core, ideal.mem_span],
    unfold has_Sup.Sup at hx, unfold conditionally_complete_lattice.Sup at hx,
    unfold complete_lattice.Sup at hx, rw ideal.mem_Inf at hx,
    intros J HJ, apply hx, rintro K ⟨HK1, HK2⟩, intros r hr,
    rw ←graded_algebra.sum_support_decompose 𝒜 r, refine ideal.sum_mem _ _,
    intros i hi, apply HJ,
    rw mem_image,
    refine ⟨⟨graded_algebra.decompose 𝒜 r i, ⟨i, submodule.coe_mem _⟩⟩, _, rfl⟩,
    rw mem_preimage, apply HK2, apply HK1, exact hr, }
end

end homogeneous_core

section homogeneous_hull

variables {ι R A : Type*} [comm_ring R] [comm_ring A]
variables [algebra R A] [decidable_eq ι] [add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

/--For any `I : ideal R`, not necessarily homogeneous, there is a homogeneous ideal associated with
`I` spanned by all homogeneous components of elements in `I`. -/
def ideal.homogeneous_hull : ideal A :=
  ideal.span {r : A | ∃ (i : ι) (x : I), (graded_algebra.decompose 𝒜 x i : A) = r}

lemma ideal.is_homogeneous.homogeneous_hull :
  ideal.is_homogeneous 𝒜 (ideal.homogeneous_hull 𝒜 I) :=
begin
  rw ideal.is_homogeneous.iff_exists,
  use {x : homogeneous_submonoid 𝒜 | ∃ (i : ι) (r : I), (graded_algebra.decompose 𝒜 r i : A) = x},
  rw [ideal.homogeneous_hull], congr, ext r, split; intros h,
  { obtain ⟨i, ⟨x, hx1⟩, hx2⟩ := h,
    exact ⟨⟨(graded_algebra.decompose 𝒜 x i),
      ⟨i, submodule.coe_mem _⟩⟩, ⟨⟨i, ⟨⟨x, hx1⟩, rfl⟩⟩, hx2⟩⟩,},
  { obtain ⟨_, ⟨⟨i, ⟨⟨r, hr⟩, h⟩⟩, rfl⟩⟩ := h,
    use i, use ⟨r, hr⟩, exact h }
end

lemma ideal.ideal_le_homogeneous_hull [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)] :
  I ≤ ideal.homogeneous_hull 𝒜 I :=
begin
  intros r hr,
  rw [←graded_algebra.sum_support_decompose 𝒜 r, ideal.homogeneous_hull],
  refine ideal.sum_mem _ _, intros j hj,
  apply ideal.subset_span, use j, use ⟨r, hr⟩, refl,
end

lemma ideal.homogeneous_hull_is_mono : monotone (ideal.homogeneous_hull 𝒜) := λ I J I_le_J,
begin
  apply ideal.span_mono, rintros r ⟨hr1, ⟨x, hx⟩, rfl⟩,
  refine ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩,
end

lemma ideal.homogeneous_hull.eq_Inf [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)] :
  ideal.homogeneous_hull 𝒜 I = Inf { J : ideal A | ideal.is_homogeneous 𝒜 J ∧ I ≤ J } :=
begin
  ext, split; intros hx,
  { rw ideal.mem_Inf, rintros K ⟨HK1, HK2⟩,
    rw [ideal.homogeneous_hull, ideal.mem_span] at hx,
    apply hx K, rintros r ⟨i, ⟨⟨y, hy⟩, rfl⟩⟩,
    apply HK1, apply HK2, exact hy, },
  { rw ideal.mem_Inf at hx,
    refine @hx (ideal.homogeneous_hull 𝒜 I) _,
    exact ⟨ideal.is_homogeneous.homogeneous_hull _ _, ideal.ideal_le_homogeneous_hull _ _⟩, }
end

lemma ideal.is_homogeneous.homogeneous_hull_eq_self [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]
  (h : ideal.is_homogeneous 𝒜 I) :
  ideal.homogeneous_hull 𝒜 I = I :=
begin
  rw ideal.homogeneous_hull.eq_Inf, ext x, split; intros hx,
  rw ideal.mem_Inf at hx, apply hx, refine ⟨h, le_refl I⟩,
  rw ideal.mem_Inf, rintros J ⟨HJ1, HJ2⟩, apply HJ2, exact hx,
end

end homogeneous_hull


section galois_connection

variables {ι R A : Type*} [comm_ring R] [comm_ring A]
variables [algebra R A] [decidable_eq ι] [add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]

lemma ideal.homgeneous_hull.gc :
  galois_connection
    (λ I, ⟨ideal.homogeneous_hull 𝒜 I, ideal.is_homogeneous.homogeneous_hull 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜)
    (λ I, I.1 : homogeneous_ideal 𝒜 → ideal A)
   := λ I J,
⟨ λ H, begin
    dsimp only at H,
    refine le_trans _ H,
    apply ideal.ideal_le_homogeneous_hull,
  end,
  λ H, begin
    suffices : ideal.homogeneous_hull 𝒜 I ≤ J.val,
    exact this,
    rw ←ideal.is_homogeneous.homogeneous_hull_eq_self 𝒜 J.1 J.2,
    exact ideal.homogeneous_hull_is_mono 𝒜 H,
  end ⟩

lemma ideal.homogeneous_core.gc :
  galois_connection
    (λ I, I.1 : homogeneous_ideal 𝒜 → ideal A)
    (λ I, ⟨ideal.homogeneous_core 𝒜 I, ideal.is_homogeneous.homogeneous_core 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜)
     := λ I J,
⟨ λ H, begin
    dsimp only at H,
    suffices : I.1 ≤ ideal.homogeneous_core 𝒜 J,
    exact this,
    rw ←ideal.is_homogeneous.homogeneous_core_eq_self 𝒜 I.1 I.2,
    exact ideal.homogeneous_core_is_mono 𝒜 H,
  end, λ H, begin
    refine le_trans H _,
    apply ideal.homogeneous_core_le_ideal,
  end⟩

/--There is a galois insertion between homogeneous ideals and ideals via
`ideal.homgeneous_hull A` and `(λ I, I.1)`-/
def ideal.homogeneous_hull.gi :
  galois_insertion
    (λ I, ⟨ideal.homogeneous_hull 𝒜 I, ideal.is_homogeneous.homogeneous_hull 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜)
    (λ I, I.1 : homogeneous_ideal 𝒜 → ideal A) :=
{ choice := λ I H, ⟨I, begin
    have eq : I = ideal.homogeneous_hull 𝒜 I,
    have ineq1 : I ≤ ideal.homogeneous_hull 𝒜 I := ideal.ideal_le_homogeneous_hull 𝒜 I,
    exact le_antisymm ineq1 H,
    rw eq, apply ideal.is_homogeneous.homogeneous_hull,
  end⟩,
  gc := ideal.homgeneous_hull.gc 𝒜,
  le_l_u := λ ⟨I, HI⟩, by { apply ideal.ideal_le_homogeneous_hull },
  choice_eq := λ I H, begin
    refine le_antisymm _ H, apply ideal.ideal_le_homogeneous_hull,
  end }

/--There is a galois coinsertion between homogeneous ideals and ideals via
`(λ I, I.1)` and `ideal.homogeneous_core`-/
def ideal.homogeneous_core.gi :
  galois_coinsertion
    (λ I, I.1 : homogeneous_ideal 𝒜 → ideal A)
    (λ I, ⟨ideal.homogeneous_core 𝒜 I, ideal.is_homogeneous.homogeneous_core 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜) :=
{ choice := λ I HI, ⟨I, begin
    have eq : I = ideal.homogeneous_core 𝒜 I,
    refine le_antisymm HI _,
    apply (ideal.homogeneous_core_le_ideal 𝒜 I),
    rw eq, apply ideal.is_homogeneous.homogeneous_core,
  end⟩,
  gc := ideal.homogeneous_core.gc 𝒜,
  u_l_le := λ I, by apply ideal.homogeneous_core_le_ideal,
  choice_eq := λ I H, begin
    apply le_antisymm, exact H, apply ideal.homogeneous_core_le_ideal,
  end, }

end galois_connection

section linear_ordered_cancel_add_comm_monoid

variables {ι : Type*} [linear_ordered_cancel_add_comm_monoid ι] [decidable_eq ι]
variables {R : Type*} [comm_ring R]
variables (A : ι → ideal R) [graded_algebra A]
variable [Π (I : homogeneous_ideal A) (x : R),
  decidable_pred (λ (i : ι), graded_algebra.proj A i x ∉ I)]
variable [Π (i : ι) (x : A i), decidable (x ≠ 0)]

lemma homogeneous_ideal.is_prime_iff
  (I : homogeneous_ideal A)
  (I_ne_top : I ≠ ⊤)
  (homogeneous_mem_or_mem : ∀ {x y : R},
    set_like.is_homogeneous A x → set_like.is_homogeneous A y
    → (x * y ∈ I.1 → x ∈ I.1 ∨ y ∈ I.1)) : ideal.is_prime I.1 :=
⟨λ rid, begin
  have rid' : I.val = (⊤ : homogeneous_ideal A).val,
  unfold has_top.top, simp only [rid], refl,
  apply I_ne_top, exact subtype.val_injective rid',
end, begin
  intros x y hxy, by_contradiction rid,
  obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
  set set₁ := (graded_algebra.support A x).filter (λ i, graded_algebra.proj A i x ∉ I) with set₁_eq,
  set set₂ := (graded_algebra.support A y).filter (λ i, graded_algebra.proj A i y ∉ I) with set₂_eq,
  have set₁_nonempty : set₁.nonempty,
  { replace rid₁ : ¬(∀ (i : ι), (graded_algebra.decompose A x i : R) ∈ I.val),
    { intros rid, apply rid₁, rw ←graded_algebra.sum_support_decompose A x,
      apply ideal.sum_mem, intros, apply rid, },
    rw [not_forall] at rid₁,
    obtain ⟨i, h⟩ := rid₁,
    refine ⟨i, _⟩, rw set₁_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩, rw graded_algebra.mem_support_iff, intro rid₃,
    rw graded_algebra.proj_apply at rid₃, rw rid₃ at h,
    simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
  have set₂_nonempty : set₂.nonempty,
  { replace rid₂ : ¬(∀ (i : ι), (graded_algebra.decompose A y i : R) ∈ I.val),
    { intros rid, apply rid₂, rw ←graded_algebra.sum_support_decompose A y,
      apply ideal.sum_mem, intros, apply rid, },
    rw [not_forall] at rid₂,
    obtain ⟨i, h⟩ := rid₂,
    refine ⟨i, _⟩, rw set₂_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩, rw graded_algebra.mem_support_iff, intro rid₃,
    rw graded_algebra.proj_apply at rid₃, rw rid₃ at h,
    simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
  set max₁ := set₁.max' set₁_nonempty with max₁_eq,
  set max₂ := set₂.max' set₂_nonempty with max₂_eq,
  have mem_max₁ := finset.max'_mem set₁ set₁_nonempty,
  rw [←max₁_eq, set₁_eq] at mem_max₁,
  have mem_max₂ := finset.max'_mem set₂ set₂_nonempty,
  rw [←max₂_eq, set₂_eq] at mem_max₂,
  replace hxy : ∀ (i : ι), (graded_algebra.decompose A (x * y) i : R) ∈ I.val,
  { intros i, apply I.2, exact hxy, },
  specialize hxy (max₁ + max₂),
  have eq :=
    calc  graded_algebra.proj A (max₁ + max₂) (x * y)
        = ∑ ij in ((graded_algebra.support A x).product (graded_algebra.support A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂),
            (graded_algebra.proj A ij.1 x) * (graded_algebra.proj A ij.2 y)
        : _ --(0)
    ... = ∑ ij in ((graded_algebra.support A x).product (graded_algebra.support A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)} ∪ {(max₁, max₂)},
            (graded_algebra.proj A ij.1 x) * (graded_algebra.proj A ij.2 y)
        : _ -- (1),
    ... = ∑ (ij : ι × ι) in ((graded_algebra.support A x).product
            (graded_algebra.support A y)).filter
            (λ (z : ι × ι), prod.fst z + z.snd = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_algebra.proj A (prod.fst ij) x) * (graded_algebra.proj A ij.snd y)
        + ∑ ij in {(max₁, max₂)}, (graded_algebra.proj A (prod.fst ij) x)
            * (graded_algebra.proj A ij.snd y)
        : _ -- (2)
    ... = ∑ ij in ((graded_algebra.support A x).product (graded_algebra.support A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_algebra.proj A ij.1 x) * (graded_algebra.proj A ij.2 y)
        + _
        : by rw finset.sum_singleton,

  have eq₂ :
    (graded_algebra.proj A (max₁, max₂).fst) x * (graded_algebra.proj A (max₁, max₂).snd) y
          = graded_algebra.proj A (max₁ + max₂) (x * y)
          - ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_algebra.support A x).product (graded_algebra.support A y)) \ {(max₁, max₂)},
              (graded_algebra.proj A ij.fst) x * (graded_algebra.proj A ij.snd) y,
  { rw eq, ring },

  have mem_I₂ : ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_algebra.support A x).product (graded_algebra.support A y)) \ {(max₁, max₂)},
              (graded_algebra.proj A ij.fst) x * (graded_algebra.proj A ij.snd) y ∈ I,
  { apply ideal.sum_mem, rintros ⟨i, j⟩ H,
    simp only [not_and, prod.mk.inj_iff, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
       finset.mem_singleton, finset.mem_filter, finset.mem_product] at H,
    obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩ := H,
    cases lt_trichotomy i max₁,
    { -- in this case `i < max₁`, so `max₂ < j`, so `of A j (y j) ∈ I`
      have ineq : max₂ < j,
      { by_contra rid₂, rw not_lt at rid₂,
        have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
        conv_lhs at rid₃ { rw add_comm },
        conv_rhs at rid₃ { rw add_comm },
        rw H₃ at rid₃, exact lt_irrefl _ rid₃, },
      have not_mem_j : j ∉ set₂,
      { intro rid₂,
        rw max₂_eq at ineq,
        have rid₃ := (finset.max'_lt_iff set₂ set₂_nonempty).mp ineq j rid₂,
        exact lt_irrefl _ rid₃, },
      rw set₂_eq at not_mem_j,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_filter] at not_mem_j,
      specialize not_mem_j H₂,
      apply ideal.mul_mem_left,
      convert not_mem_j, },
    { cases h,
      { -- in this case `i = max₁`, so `max₂ = j`, contradictory
        have : j = max₂,
        { rw h at H₃,
          exact linear_ordered_cancel_add_comm_monoid.add_left_cancel _ _ _ H₃, },
        exfalso,
        exact H₄ h this, },
      { -- in this case `i > max₁`, so `i < max₁`, so `of A i (x i) ∈ I`
        have ineq : max₁ < i,
        { by_contra rid₂, rw not_lt at rid₂,
          have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
          conv_lhs at rid₃ { rw linear_ordered_cancel_add_comm_monoid.add_comm },
          exact lt_irrefl _ rid₃, },
        have not_mem_i : i ∉ set₁,
        { intro rid₂,
          rw max₁_eq at ineq,
          have rid₃ := (finset.max'_lt_iff set₁ set₁_nonempty).mp ineq i rid₂,
          exact lt_irrefl _ rid₃,},
        rw set₁_eq at not_mem_i,
        simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
          finset.mem_filter] at not_mem_i,
        specialize not_mem_i H₁,
        apply ideal.mul_mem_right,
        convert not_mem_i, }, } },
  have mem_I₃ :
    (graded_algebra.proj A (max₁, max₂).fst) x * (graded_algebra.proj A (max₁, max₂).snd) y ∈ I,
  { rw eq₂, apply ideal.sub_mem,
    have HI := I.2,
    specialize HI (max₁ + max₂) hxy, exact hxy, exact mem_I₂, },
  specialize homogeneous_mem_or_mem ⟨max₁, _⟩ ⟨max₂, _⟩ mem_I₃,
  rw [graded_algebra.proj_apply], exact submodule.coe_mem _,
  rw [graded_algebra.proj_apply], exact submodule.coe_mem _,
  cases homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
  refine mem_max₁.2 homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
  refine mem_max₂.2 homogeneous_mem_or_mem,

  -- (0)
  rw [graded_algebra.proj_apply, alg_equiv.map_mul, graded_algebra.support, graded_algebra.support,
       direct_sum.coe_mul_apply_submodule], refl,

  -- (1)
  congr, ext, split; intros H,
  { simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product] at H,
    rw finset.mem_union,
    by_cases a = (max₁, max₂),
    right, rw h, exact finset.mem_singleton_self (max₁, max₂),
    left, rw finset.mem_sdiff, split,
    simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
    exact H, intro rid, simp only [finset.mem_singleton] at rid, exact h rid, },
  { rw finset.mem_union at H, cases H,
    rw finset.mem_sdiff at H, exact H.1,
    simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
    simp only [finset.mem_singleton] at H, rw H,
    refine ⟨⟨_, _⟩, rfl⟩,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
    exact mem_max₁.1,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
    exact mem_max₂.1, },

  -- (2)
  rw [finset.sum_union],
  apply finset.disjoint_iff_inter_eq_empty.mpr,
  rw finset.eq_empty_iff_forall_not_mem, rintros ⟨i, j⟩ Hij,
  rw [finset.mem_inter, finset.mem_sdiff, finset.mem_filter] at Hij,
  simp only [not_and, prod.mk.inj_iff, ne.def, dfinsupp.mem_support_to_fun, finset.mem_singleton,
    finset.mem_product] at Hij,
  exact Hij.1.2 Hij.2.1 Hij.2.2,
end⟩

lemma homogeneous_ideal.rad_eq (I : homogeneous_ideal A) :
  I.1.radical = Inf {J | I.1 ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime} :=
begin
  have subset₁ : I.1.radical ≤ Inf {J | I.1 ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime},
  { rw ideal.radical_eq_Inf, intros x hx,
    rw [submodule.mem_Inf] at hx ⊢, intros J HJ, apply hx,
    obtain ⟨HJ₁, _, HJ₂⟩ := HJ,
    refine ⟨HJ₁, HJ₂⟩, },
  have subset₂ : Inf {J | I.1 ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime} ≤ I.1.radical,
  { intros x hx,
    rw ideal.radical_eq_Inf,
    rw [submodule.mem_Inf] at hx ⊢,
    rintros J ⟨HJ₁, HJ₂⟩,
    specialize hx (ideal.homogeneous_core A J) _,
    refine ⟨_, ideal.is_homogeneous.homogeneous_core A _, _⟩,
    { have HI := I.2,
      rw [ideal.is_homogeneous.iff_eq] at HI,
      rw HI, apply ideal.span_mono, intros y hy,
      obtain ⟨hy₁, ⟨z, hz⟩⟩ := hy,
      specialize HJ₁ hy₁, refine ⟨⟨z, hz⟩, HJ₁⟩, },
    { set J' := ideal.homogeneous_core A J with eq_J',
      have homogeneity₀ := ideal.is_homogeneous.homogeneous_core A J,
      apply homogeneous_ideal.is_prime_iff A ⟨J', homogeneity₀⟩,
      intro rid,
      have rid' : J = ⊤,
      { have : J' ≤ J := ideal.homogeneous_core_le_ideal A J,
        simp only [homogeneous_ideal.eq_top_iff] at rid,
        rw rid at this, rw top_le_iff at this, exact this, },
      apply HJ₂.1, exact rid',
      rintros x y hx hy hxy,
      have H := HJ₂.mem_or_mem (ideal.homogeneous_core_le_ideal A J hxy),
      cases H,
      { left,
        have : ∀ i : ι, (graded_algebra.decompose A x i : R) ∈
          (⟨J', homogeneity₀⟩ : homogeneous_ideal A),
        { intros i, apply homogeneity₀, apply ideal.subset_span,
          simp only [set.mem_inter_eq, set_like.mem_coe, set.mem_set_of_eq],
          refine ⟨hx, H⟩, },
        rw ←graded_algebra.sum_support_decompose A x, apply ideal.sum_mem J',
        intros j hj, apply this, },
      { right,
        have : ∀ i : ι, (graded_algebra.decompose A y i : R) ∈
          (⟨J', homogeneity₀⟩ : homogeneous_ideal A),
        { intros i, apply homogeneity₀, apply ideal.subset_span,
          simp only [set.mem_inter_eq, set_like.mem_coe, set.mem_set_of_eq],
          refine ⟨hy, H⟩, }, rw ←graded_algebra.sum_support_decompose A y, apply ideal.sum_mem J',
        intros j hj, apply this, }, },
      refine (ideal.homogeneous_core_le_ideal A J) hx, },

  ext x, split; intro hx,
  exact subset₁ hx, exact subset₂ hx,
end

lemma homogeneous_ideal.rad (I : homogeneous_ideal A)  :
  ideal.is_homogeneous A I.1.radical :=
begin
  have radI_eq := homogeneous_ideal.rad_eq A I,
  rw radI_eq,
  have : Inf {J : ideal R | I.val ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime} =
  (Inf {J : homogeneous_ideal A | I.1 ≤ J.1 ∧ J.1.is_prime }).1,
  simp only [subtype.coe_le_coe, subtype.val_eq_coe], congr, ext J, split; intro H,
  { use ⟨J, H.2.1⟩, split, refine ⟨H.1, H.2.2⟩, refl, },
  { obtain ⟨K, ⟨⟨HK₁, HK₂⟩, HK₃⟩⟩ := H,
    split, convert HK₁, rw ←HK₃, split,
    rw ←HK₃, exact K.2, rw ←HK₃, exact HK₂, },
  rw this,
  refine (Inf {J : homogeneous_ideal A | I.val ≤ J.val ∧ J.val.is_prime}).2,
end

end linear_ordered_cancel_add_comm_monoid
