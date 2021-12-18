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

This file defines homogeneous ideals of `graded_algebra A` where `A : ι → submodule R R`and
operations on them:
* `mul`, `inf`, `Inf` of homogeneous ideals are homogeneous;
* `⊤`, `⊥`, i.e. the trivial ring and `R` are homogeneous;
* `radical` of a homogeneous ideal is homogeneous.
-/

noncomputable theory

section is_homogeneous_ideal_defs

open set_like direct_sum set
open_locale big_operators

variables {ι R : Type*} [comm_ring R] [decidable_eq ι] [add_comm_monoid ι]
variables (A : ι → submodule R R) [graded_algebra A]
variable (I : ideal R)

/--An `I : ideal R` is called homogeneous if for every `r ∈ I`, every homogeneous component of `r`
  is in `I`.-/
def ideal.is_homogeneous : Prop :=
∀ (i : ι) ⦃r : R⦄, r ∈ I → (graded_algebra.decompose A r i : R) ∈ I

lemma ideal.is_homogeneous_iff_forall_subset :
  ideal.is_homogeneous A I ↔ ∀ i, (I : set R) ⊆ graded_algebra.proj A i ⁻¹' I :=
iff.rfl

lemma ideal.is_homogeneous_iff_subset_Inter :
  ideal.is_homogeneous A I ↔ (I : set R) ⊆ ⋂ i, graded_algebra.proj A i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma ideal.is_homogeneous.exists_iff_eq_span :
  (∃ (S : set (homogeneous_submonoid A)), I = ideal.span (coe '' S)) ↔
  I = ideal.span {x | x ∈ I ∧ is_homogeneous A x} :=
-- get rid of the messy subtypes and set coercions
suffices (∃ s : set R, s ⊆ set_of (is_homogeneous A) ∧ I = ideal.span s) ↔
  I = ideal.span (I ∩ set_of (is_homogeneous A)),
from (subtype.exists_set_subtype _).trans this,
begin
  split,
  { rintros ⟨s, hs, rfl⟩,
    apply le_antisymm,
    { exact ideal.span_mono (subset_inter (ideal.subset_span) hs) },
    { exact ideal.span_le.2 (inter_subset_left _ _) } },
  { intros hI,
    exact ⟨(I : set R) ∩ set_of (is_homogeneous A), inter_subset_right _ _, hI⟩, }
end

lemma mul_homogeneous_element_mem_of_mem
  {I : ideal R} (r x : R) (hx₁ : is_homogeneous A x) (hx₂ : x ∈ I) (j : ι) :
  graded_algebra.proj A j (r * x) ∈ I :=
begin
  letI : Π (i : ι) (x : A i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw [←graded_algebra.sum_support_decompose A r, finset.sum_mul, linear_map.map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (graded_algebra.decompose A r k : R) * x ∈ A (k + i) := graded_monoid.mul_mem
    (submodule.coe_mem _) hi,
  rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem A mem₁,
    coe_of_submodule_apply A, submodule.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end

lemma ideal.is_homogeneous.iff_eq :
  ideal.is_homogeneous A I ↔ I = ideal.span {x | x ∈ I ∧ is_homogeneous A x} :=
⟨ λ hI, begin
  letI : Π (i : ι) (x : A i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  ext, split; intro hx,
  { rw ←graded_algebra.sum_support_decompose A x,
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

lemma ideal.is_homogeneous.iff_exists :
  ideal.is_homogeneous A I ↔ ∃ (S : set (homogeneous_submonoid A)), I = ideal.span (coe '' S) :=
by rw [ideal.is_homogeneous.exists_iff_eq_span, ideal.is_homogeneous.iff_eq]

end is_homogeneous_ideal_defs

section operations

open set_like direct_sum set
open_locale big_operators pointwise

variables {ι R : Type*} [comm_ring R] [decidable_eq ι] [add_comm_monoid ι]
variables (A : ι → submodule R R) [graded_algebra A]
variable (I : ideal R)

/--For any `comm_ring R`, we collect the homogeneous ideals of `R` into a type.-/
abbreviation homogeneous_ideal : Type* := { I : ideal R // ideal.is_homogeneous A I }

lemma ideal.is_homogeneous.bot : ideal.is_homogeneous A ⊥ := λ i r hr,
begin
  simp only [ideal.mem_bot] at hr,
  rw [hr, alg_equiv.map_zero, zero_apply],
  apply ideal.zero_mem
end

instance homogeneous_ideal.inhabited : inhabited (homogeneous_ideal A) :=
{ default := ⟨⊥, ideal.is_homogeneous.bot _⟩}

instance homogeneous_ideal.has_top :
  has_top (homogeneous_ideal A) :=
⟨⟨⊤, λ _ _ _, by simp only [submodule.mem_top]⟩⟩

@[simp] lemma homogeneous_ideal.eq_top_iff
  (I : homogeneous_ideal A) : I = ⊤ ↔ I.1 = ⊤ :=
⟨ λ h, by { rw h, refl },
  λ h, begin
    have h' : I.val = (⊤ : homogeneous_ideal A).val,
    rw h, refl,
    apply subtype.val_injective h',
  end ⟩

instance homogeneous_ideal.order : partial_order (homogeneous_ideal A) :=
partial_order.lift _ subtype.coe_injective

instance homogeneous_ideal.has_mem : has_mem R (homogeneous_ideal A) :=
{ mem := λ r I, r ∈ I.1 }

variables {A}

lemma ideal.is_homogeneous.inf {I J : ideal R}
  (HI : ideal.is_homogeneous A I) (HJ : ideal.is_homogeneous A J) :
  ideal.is_homogeneous A (I ⊓ J) :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma homogeneous_ideal.Inf {ℐ : set (ideal R)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous A I) :
  ideal.is_homogeneous A (Inf ℐ) :=
begin
  intros i x Hx, simp only [ideal.mem_Inf] at Hx ⊢,
  intros J HJ,
  exact h _ HJ _ (Hx HJ),
end

lemma ideal.is_homogeneous.mul {I J : ideal R}
  (HI : ideal.is_homogeneous A I) (HJ : ideal.is_homogeneous A J) :
  ideal.is_homogeneous A (I * J) :=
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
    have hy1 : y1 ∈ set_like.homogeneous_submonoid A,
    rw ←h1.2, exact z1.2,
    rw set.mem_image at h2, obtain ⟨z2, h2⟩ := h2,
    have hy2 : y2 ∈ set_like.homogeneous_submonoid A,
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

lemma ideal.is_homogeneous.sup {I J : ideal R}
  (HI : ideal.is_homogeneous A I) (HJ : ideal.is_homogeneous A J) :
  ideal.is_homogeneous A (I ⊔ J) :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

lemma ideal.is_homogeneous.Sup {ℐ : set (ideal R)} (Hℐ : ∀ (I ∈ ℐ), ideal.is_homogeneous A I) :
  ideal.is_homogeneous A (Sup ℐ) :=
begin
  simp_rw [ideal.is_homogeneous.iff_exists] at Hℐ,
  set 𝓈 : ℐ → set (homogeneous_submonoid A) := λ I : ℐ, Exists.some (Hℐ I _) with 𝓈_eq,
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

variables (A)

instance : has_inf (homogeneous_ideal A) :=
{ inf := λ I J, ⟨I ⊓ J, I.prop.inf J.prop⟩ }

instance : has_Inf (homogeneous_ideal A) :=
{ Inf := λ ℐ, ⟨Inf (coe '' ℐ), homogeneous_ideal.Inf $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

instance : has_sup (homogeneous_ideal A) :=
{ sup := λ I J, ⟨I ⊔ J, I.prop.sup J.prop⟩ }

instance : has_Sup (homogeneous_ideal A) :=
{ Sup := λ ℐ, ⟨Sup (coe '' ℐ), ideal.is_homogeneous.Sup $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

instance : has_mul (homogeneous_ideal A) :=
{ mul := λ I J, ⟨I * J, I.prop.mul J.prop⟩ }

instance : has_add (homogeneous_ideal A) := ⟨(⊔)⟩

end operations

section homogenisation

open set_like direct_sum set

variables {ι R : Type*} [comm_ring R]
variables (A : ι → submodule R R)
variable (I : ideal R)

/--For any `I : ideal R`, not necessarily homogeneous, there is a homogeneous ideal asscoiated with
`I` spaned by all homogeneous elements in `I`. This construction will be used when proving radical
of homogeneous ideal is homogeneous-/
def ideal.homogenisation : ideal R := ideal.span (set_of (is_homogeneous A) ∩ I)

lemma ideal.homgenisation_le_ideal :
  ideal.homogenisation A I ≤ I :=
begin
  rw ideal.homogenisation,
  conv_rhs { rw ←ideal.span_eq I },
  apply ideal.span_mono, exact (set_of (is_homogeneous A)).inter_subset_right ↑I,
end

variables [add_comm_monoid ι] [decidable_eq ι]
variables [graded_algebra A]

lemma is_homogeneous_ideal.homogeneous_ideal_of_ideal :
  ideal.is_homogeneous A (ideal.homogenisation A I) :=
begin
  rw ideal.is_homogeneous.iff_exists,
  use ({x | ↑x ∈ I}),
  rw ideal.homogenisation, congr, ext, split; intro hx;
  simp only [mem_inter_eq, mem_set_of_eq, set_like.mem_coe] at hx ⊢,
  use x, exact hx.1, refine ⟨hx.2, rfl⟩,
  obtain ⟨y, hy₁, hy₂⟩ := hx, simp only [mem_set_of_eq] at hy₁, split, rw ←hy₂,
  rcases y with ⟨y, ⟨i, hy₃⟩⟩, use i, refine hy₃,
  rw ←hy₂, refine hy₁,
end

end homogenisation
