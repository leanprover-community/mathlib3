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
@[reducible] def is_homogeneous_ideal : Prop :=
  ∀ {i : ι} {r : R}, r ∈ I → (graded_algebra.decompose A r i : R) ∈ I

lemma is_homogeneous_ideal_iff_forall_subset (I : ideal R) :
  is_homogeneous_ideal A I ↔ ∀ i, (I : set R) ⊆ graded_algebra.proj A i ⁻¹' I :=
iff.rfl

lemma is_homogeneous_ideal_iff_subset_Inter (I : ideal R) :
  is_homogeneous_ideal A I ↔ (I : set R) ⊆ ⋂ i, graded_algebra.proj A i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma is_homogeneous_ideal.exists_iff_eq_span :
  (∃ (S : set (homogeneous_submonoid A)), I = ideal.span (coe '' S)) ↔
  I = ideal.span {x | x ∈ I ∧ is_homogeneous A x} :=
⟨λ ⟨S, hI⟩, begin
    ext r, split; intro hr,
  { rw hI at hr,
    suffices : coe '' S ⊆ {x | x ∈ I ∧ is_homogeneous A x},
    exact (ideal.span_mono this) hr,
    intros s hs, split, rw hI,
    refine ideal.subset_span hs,
    obtain ⟨⟨s', homs'⟩, hs₁, hs₂⟩ := hs,
    convert homs', rw ←hs₂, refl },
  { obtain ⟨l, hl⟩ := (finsupp.mem_span_iff_total R _ _).mp hr,
    rw ←hl, apply ideal.sum_mem, rintros ⟨x, hx₁, hx₂⟩ hx₃,
    simp only [linear_map.id_coe, id.def, finsupp.mem_support_iff, linear_map.coe_smul_right,
      ne.def, smul_eq_mul, subtype.coe_mk] at hx₁ hx₂ hx₃ ⊢,
    exact ideal.mul_mem_left _ _ hx₁, }
  end, λ hI, ⟨{x : homogeneous_submonoid A | ↑x ∈ I}, begin
    rw hI, congr, ext r, split; intros hr,
    { rcases hr with ⟨r_mem, ⟨i, r_eq⟩⟩,
      use r, exact ⟨i, r_eq⟩, refine ⟨_, rfl⟩,
      simp only [mem_set_of_eq, subtype.coe_mk], convert ←r_mem, },
    { rcases hr with ⟨⟨r', hr'⟩, hr₁, hr₂⟩,
      simp only [mem_set_of_eq, subtype.coe_mk] at hr₁,
      rw ←hr₂, rw ←hI at hr₁, refine ⟨hr₁, hr'⟩, }
  end⟩⟩

variable [Π (i : ι) (x : A i), decidable (x ≠ 0)]

lemma is_homogeneous_ideal.mul_homogeneous_element
  {I : ideal R} (r x : R) (hx₁ : is_homogeneous A x) (hx₂ : x ∈ I) (j : ι) :
  graded_algebra.proj A j (r * x) ∈ I :=
begin
  rw [←graded_algebra.sum_support_decompose A r, finset.sum_mul, linear_map.map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (graded_algebra.proj A k) r * x ∈ A (k + i) := graded_monoid.mul_mem
   (by { rw [graded_algebra.proj_apply], exact submodule.coe_mem _, }) hi,
  by_cases k + i = j,
  { rw ←h, rw graded_algebra.proj_apply at ⊢ mem₁,
    rw graded_algebra.decompose_of_mem A mem₁, simp only [of_eq_same, submodule.coe_mk],
    apply I.mul_mem_left _ hx₂, },
  { rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne],
    exact I.zero_mem, exact mem₁, intro rid, apply h rid, }
end

lemma is_homogeneous_ideal.homogeneous_component
  {I : ideal R} (HI : ∃ (S : set (homogeneous_submonoid A)), I = ideal.span (coe '' S))
  (x : R) (hx : x ∈ I) (i : ι) :
  graded_algebra.proj A i x ∈ I :=
begin
  have HI' := HI,
  rw [is_homogeneous_ideal.exists_iff_eq_span, ideal.span,
      finsupp.span_eq_range_total] at HI',
  rw HI' at hx,
  obtain ⟨s, rfl⟩ := hx,
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  refine ideal.sum_mem I _,
  rintros ⟨j, ⟨hj₁, hj₂⟩⟩ hj₃,
  simp only [algebra.id.smul_eq_mul, subtype.coe_mk, smul_eq_mul],
  apply is_homogeneous_ideal.mul_homogeneous_element, exact hj₂, exact hj₁,
end

lemma is_homogeneous_ideal_iff_eq :
  is_homogeneous_ideal A I ↔ I = ideal.span {x | x ∈ I ∧ is_homogeneous A x} :=
⟨ λ hI, begin
  ext, split; intro hx,
  { rw ←graded_algebra.sum_support_decompose A x,
    refine ideal.sum_mem _ _,
    intros j hj,
    replace hI := @hI j x hx,
    rw ideal.mem_span, intros J HJ,
    refine HJ _,
    simp only [mem_set_of_eq],
    refine ⟨hI, _⟩, refine ⟨j, _⟩, exact submodule.coe_mem _, },
  { rw [ideal.mem_span] at hx,
    apply hx,
    intros y hy,
    exact hy.1,  },
  end,
  λ hI, begin
    intros i r hr, rw ←is_homogeneous_ideal.exists_iff_eq_span at hI,
    apply is_homogeneous_ideal.homogeneous_component A hI r hr,
  end ⟩

lemma is_homogeneous_ideal_iff_exists :
  is_homogeneous_ideal A I ↔ ∃ (S : set (homogeneous_submonoid A)), I = ideal.span (coe '' S) :=
by rw [is_homogeneous_ideal.exists_iff_eq_span, is_homogeneous_ideal_iff_eq]

lemma is_homogeneous_ideal.tfae : tfae
  [ is_homogeneous_ideal A I
  , ∀ i, (I : set R) ⊆ graded_algebra.proj A i ⁻¹' I
  , (I : set R) ⊆ ⋂ i, graded_algebra.proj A i ⁻¹' ↑I
  , ∃ (S : set (homogeneous_submonoid A)), I = ideal.span (coe '' S)
  , I = ideal.span {x | x ∈ I ∧ is_homogeneous A x}] :=
begin
  tfae_have : 1↔2, exact is_homogeneous_ideal_iff_forall_subset A I,
  tfae_have : 1↔3, exact is_homogeneous_ideal_iff_subset_Inter A I,
  tfae_have : 4↔5, exact is_homogeneous_ideal.exists_iff_eq_span A I,
  tfae_have : 1↔4, exact is_homogeneous_ideal_iff_exists A I,
  tfae_finish
end

end is_homogeneous_ideal_defs

section operations

open set_like direct_sum set
open_locale big_operators pointwise

variables {ι R : Type*} [comm_ring R] [decidable_eq ι] [add_comm_monoid ι]
variables (A : ι → submodule R R) [graded_algebra A]
variable (I : ideal R)

/--We collect all homogeneous ideal into a type.-/
def homogeneous_ideal : Type* := { I : ideal R // is_homogeneous_ideal A I }

instance homogeneous_ideal.inhabited : inhabited (homogeneous_ideal A) :=
⟨⟨⊥, begin
    intros i r hr, simp only [ideal.mem_bot] at hr,
    rw [hr, alg_equiv.map_zero, zero_apply],
    apply ideal.zero_mem
  end⟩⟩

instance homogeneous_ideal.has_bot : has_bot (homogeneous_ideal A) :=
⟨⟨⊥, begin
    intros i r hr, simp only [ideal.mem_bot] at hr,
    rw [hr, alg_equiv.map_zero, zero_apply],
    apply ideal.zero_mem
  end⟩⟩

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

instance homogeneous_ideal.has_le : has_le (homogeneous_ideal A) :=
{ le := λ I J, I.1 ≤ J.1 }

instance homogeneous_ideal.order : preorder (homogeneous_ideal A) :=
{ le_refl := λ I, by {unfold has_le.le, exact le_refl I.1, },
  le_trans := λ I J K HIJ HJK,
    by {unfold has_le.le at HIJ HJK ⊢, exact @le_trans _ _ I.1 J.1 K.1 HIJ HJK, },
  ..(homogeneous_ideal.has_le A)}

instance homogeneous_ideal.has_mem : has_mem R (homogeneous_ideal A) :=
{ mem := λ r I, r ∈ I.1 }


instance homogeneous_ideal.has_inf : has_inf (homogeneous_ideal A) :=
{ inf := λ I J, begin
  refine ⟨I.1 ⊓ J.1, _⟩,
  intros i r hr, split, apply I.2 hr.1, apply J.2 hr.2,
end }

instance homogeneous_ideal.has_Inf  :
  has_Inf (homogeneous_ideal A) :=
{ Inf := λ ℐ, ⟨Inf (set.image (λ x : homogeneous_ideal A, x.val) ℐ), begin
    intros i x Hx, simp only [submodule.mem_Inf] at Hx ⊢,
    intros J HJ, simp only [set.mem_image, subtype.val_eq_coe] at HJ,
    obtain ⟨K, HK₁, HK₂⟩ := HJ, rw ←HK₂,
    have HK₃ := K.2,
    apply HK₃, apply Hx, simp only [set.mem_image, subtype.val_eq_coe], use K, exact ⟨HK₁, rfl⟩,
end⟩ }


variable [Π (i : ι) (x : A i), decidable (x ≠ 0)]

instance homogeneous_ideal.has_mul :
  has_mul (homogeneous_ideal A) :=
{ mul := λ I J, ⟨I.1 * J.1, begin
    have HI := I.2, have HJ := J.2,
    rw is_homogeneous_ideal_iff_exists at HI HJ,
    choose s₁ hI using HI,
    choose s₂ hJ using HJ,
    rw is_homogeneous_ideal_iff_exists,
    rw [hI, hJ, ideal.span_mul_span'],
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
  end⟩ }

instance homogeneous_ideal.has_sup : has_sup (homogeneous_ideal A) :=
{ sup := λ ⟨I, HI⟩ ⟨J, HJ⟩, ⟨I ⊔ J, begin
    rw is_homogeneous_ideal_iff_exists at HI HJ,
    choose s₁ hI using HI,
    choose s₂ hJ using HJ,
    rw is_homogeneous_ideal_iff_exists,
    refine ⟨s₁ ∪ s₂, _⟩,
    rw [set.image_union, ideal.span, hI, hJ],
    exact (submodule.span_union _ _).symm,
end⟩ }

instance homogeneous_ideal.has_Sup : has_Sup (homogeneous_ideal A) :=
{ Sup := λ ℐ, ⟨Sup (set.image (λ x : homogeneous_ideal A, x.val) ℐ), begin
    have Hℐ : ∀ I : ℐ, is_homogeneous_ideal A I.1.1 := λ I, I.1.2,
    simp_rw [is_homogeneous_ideal_iff_exists] at Hℐ,
    set 𝓈 : ℐ → set (homogeneous_submonoid A) := λ I : ℐ, Exists.some (Hℐ I) with 𝓈_eq,
    have h𝓈 : ∀ I : ℐ, I.1.1 = ideal.span (coe '' 𝓈 I) := λ I : ℐ, Exists.some_spec (Hℐ I),
    rw is_homogeneous_ideal_iff_exists,
    use sUnion (set.range 𝓈),
    rw [sUnion_range, image_Union, ideal.span, submodule.span_Union],
    ext r, split,
    { suffices : Sup ((λ (x : homogeneous_ideal A), x.val) '' ℐ) ≤ _, revert r, exact this,
      rw Sup_le_iff, intros I HI,
      have ineq1 : I ≤ ideal.span I := ideal.subset_span, refine le_trans ineq1 _,
      rw ideal.span_le, simp only [coe_subset_coe, ideal.submodule_span_eq], intros x hx,
      simp only [mem_image, subtype.val_eq_coe] at HI,
      obtain ⟨I', HI1, HI2⟩ := HI, rw submodule.mem_supr, intros J HJ,
      apply HJ ⟨I', HI1⟩, rw ←h𝓈 ⟨I', HI1⟩,simp only [subtype.val_eq_coe], rw HI2, assumption },
    { suffices : _ ≤  Sup ((λ (x : homogeneous_ideal A), x.val) '' ℐ), revert r, exact this,
      rw supr_le_iff, intros I, rw submodule.span_le, intros x hx,
      simp only [mem_image] at hx, obtain ⟨x', hx1, hx2⟩ := hx,
      simp only [mem_coe, subtype.val_eq_coe], dsimp only at hx1,
      apply ideal.mem_Sup_of_mem, simp only [mem_image], use I.1, refine ⟨I.2, rfl⟩,
      simp only [subtype.val_eq_coe] at h𝓈 ⊢, rw h𝓈,
      refine ideal.subset_span _, rw [mem_image], use x', refine ⟨hx1, hx2⟩, }
  end⟩ }

instance homogeneous_ideal.has_add : has_add (homogeneous_ideal A) := ⟨(⊔)⟩

end operations

section of_ideal

open set_like direct_sum set

variables {ι R : Type*} [comm_ring R]
variables (A : ι → submodule R R)
variable (I : ideal R)

/--For any `I : ideal R`, not necessarily homogeneous, there is a homogeneous ideal asscoiated with
`I` spaned by all homogeneous elements in `I`. This construction will be used when proving radical
of homogeneous ideal is homogeneous-/
@[reducible] def homogeneous_ideal_of_ideal : ideal R := ideal.span (set_of (is_homogeneous A) ∩ I)

lemma homogeneous_ideal_of_ideal_le_ideal (I : ideal R) :
  homogeneous_ideal_of_ideal A I ≤ I :=
begin
  rw homogeneous_ideal_of_ideal,
  conv_rhs { rw ←ideal.span_eq I },
  apply ideal.span_mono, exact (set_of (is_homogeneous A)).inter_subset_right ↑I,
end

variables [add_comm_monoid ι] [decidable_eq ι]
variables [graded_algebra A] [Π (i : ι) (x : A i), decidable (x ≠ 0)]

lemma is_homogeneous_ideal.homogeneous_ideal_of_ideal :
  is_homogeneous_ideal A (homogeneous_ideal_of_ideal A I) :=
begin
  rw is_homogeneous_ideal_iff_exists,
  use ({x | ↑x ∈ I}),
  rw homogeneous_ideal_of_ideal, congr, ext, split; intro hx;
  simp only [mem_inter_eq, mem_set_of_eq, set_like.mem_coe] at hx ⊢,
  use x, exact hx.1, refine ⟨hx.2, rfl⟩,
  obtain ⟨y, hy₁, hy₂⟩ := hx, simp only [mem_set_of_eq] at hy₁, split, rw ←hy₂,
  rcases y with ⟨y, ⟨i, hy₃⟩⟩, use i, refine hy₃,
  rw ←hy₂, refine hy₁,
end

end of_ideal
