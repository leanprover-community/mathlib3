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

open set_like direct_sum set
open_locale big_operators pointwise direct_sum

section homogeneous_core

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variable (I : ideal A)

/-- For any `I : ideal R`, not necessarily homogeneous, there is a homogeneous ideal associated with
`I` spanned by all homogeneous elements in `I`. This construction is used when proving that the
radical of a homogeneous ideal is homogeneous. -/
def ideal.homogeneous_core : ideal A :=
ideal.span (coe '' ((coe : subtype (is_homogeneous 𝒜) → A) ⁻¹' I))

lemma ideal.homogeneous_core_is_mono : monotone (ideal.homogeneous_core 𝒜) :=
λ I J I_le_J, ideal.span_mono $ set.image_subset _ $ λ x, @I_le_J _

lemma ideal.homogeneous_core_le_ideal : ideal.homogeneous_core 𝒜 I ≤ I :=
ideal.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_ideal_defs

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variable (I : ideal A)

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
    I = ideal.homogeneous_core 𝒜 I :=
(set.image_preimage.compose (submodule.gi _ _).gc).exists_eq_l _

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

lemma ideal.is_homogeneous.homogeneous_core : (I.homogeneous_core 𝒜).is_homogeneous 𝒜 :=
begin
  rintros i r hr,
  rw [ideal.homogeneous_core, ideal.span, finsupp.span_eq_range_total] at hr,
  rw linear_map.mem_range at hr,
  obtain ⟨s, rfl⟩ := hr,
  rw [←graded_algebra.proj_apply, finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  refine ideal.sum_mem _ _,
  rintros z hz1,
  rw [smul_eq_mul],
  refine mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i,
  rcases z with ⟨z, hz2⟩, rw subtype.image_preimage_coe at hz2, exact hz2.2,
  apply ideal.subset_span, exact z.2,
end

lemma ideal.is_homogeneous.homogeneous_core_eq_self (h : ideal.is_homogeneous 𝒜 I) :
  I = ideal.homogeneous_core 𝒜 I :=
begin
  apply le_antisymm _ (I.homogeneous_core_le_ideal 𝒜),
  intros x hx,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw ←graded_algebra.sum_support_decompose 𝒜 x,
  refine ideal.sum_mem _ _,
  intros j hj, apply ideal.subset_span,
  rw [set.mem_image],
  refine ⟨⟨(graded_algebra.decompose 𝒜 x j : A), ⟨j, submodule.coe_mem _⟩⟩, _, rfl⟩,
  rw [set.mem_preimage], apply h, exact hx,
end

lemma ideal.is_homogeneous.iff_eq :
  ideal.is_homogeneous 𝒜 I ↔ I = ideal.homogeneous_core 𝒜 I :=
⟨ λ hI, (ideal.is_homogeneous.homogeneous_core_eq_self _ _ hI),
  λ hI, hI.symm ▸ ideal.is_homogeneous.homogeneous_core 𝒜 I ⟩

lemma ideal.is_homogeneous.iff_exists :
  ideal.is_homogeneous 𝒜 I ↔ ∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S) :=
by rw [ideal.is_homogeneous.exists_iff_eq_span, ideal.is_homogeneous.iff_eq]

end is_homogeneous_ideal_defs

section operations

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables [decidable_eq ι] [add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

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

@[simp] lemma homogeneous_ideal.eq_top_iff (I : homogeneous_ideal 𝒜) : I = ⊤ ↔ I.1 = ⊤ :=
subtype.ext_iff

instance homogeneous_ideal.order : partial_order (homogeneous_ideal 𝒜) :=
partial_order.lift _ subtype.coe_injective

instance homogeneous_ideal.has_mem : has_mem A (homogeneous_ideal 𝒜) :=
{ mem := λ r I, r ∈ I.1 }

variables {𝒜}

lemma ideal.is_homogeneous.inf {I J : ideal A}
  (HI : ideal.is_homogeneous 𝒜 I) (HJ : ideal.is_homogeneous 𝒜 J) :
  ideal.is_homogeneous 𝒜 (I ⊓ J) :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma ideal.is_homogeneous.Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
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

lemma ideal.is_homogeneous.Sup
  {ℐ : set (ideal A)} (Hℐ : ∀ (I ∈ ℐ), ideal.is_homogeneous 𝒜 I) :
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
{ Inf := λ ℐ, ⟨Inf (coe '' ℐ), ideal.is_homogeneous.Inf $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

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

lemma ideal.ideal_le_homogeneous_hull :
  I ≤ ideal.homogeneous_hull 𝒜 I :=
begin
  intros r hr,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw [←graded_algebra.sum_support_decompose 𝒜 r, ideal.homogeneous_hull],
  refine ideal.sum_mem _ _, intros j hj,
  apply ideal.subset_span, use j, use ⟨r, hr⟩, refl,
end

lemma ideal.homogeneous_hull_is_mono : monotone (ideal.homogeneous_hull 𝒜) := λ I J I_le_J,
begin
  apply ideal.span_mono, rintros r ⟨hr1, ⟨x, hx⟩, rfl⟩,
  refine ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩,
end

lemma ideal.homogeneous_hull.eq_Inf :
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

lemma ideal.is_homogeneous.homogeneous_hull_eq_self (h : ideal.is_homogeneous 𝒜 I) :
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
    (subtype.val : homogeneous_ideal 𝒜 → ideal A)
    (λ I, ⟨ideal.homogeneous_core 𝒜 I, ideal.is_homogeneous.homogeneous_core 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜) :=
λ I J, ⟨
  λ H, show I.1 ≤ ideal.homogeneous_core 𝒜 J, begin
    rw ideal.is_homogeneous.homogeneous_core_eq_self 𝒜 I.1 I.2,
    exact ideal.homogeneous_core_is_mono 𝒜 H,
  end,
  λ H, le_trans H (ideal.homogeneous_core_le_ideal _ _)⟩

/--There is a galois insertion between homogeneous ideals and ideals via
`ideal.homgeneous_hull A` and `(λ I, I.1)`-/
def ideal.homogeneous_hull.gi :
  galois_insertion
    (λ I, ⟨ideal.homogeneous_hull 𝒜 I, ideal.is_homogeneous.homogeneous_hull 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜)
    (subtype.val : homogeneous_ideal 𝒜 → ideal A) :=
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
    (subtype.val : homogeneous_ideal 𝒜 → ideal A)
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
