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

lemma ideal.homogeneous_core_le_ideal : I.homogeneous_core 𝒜 ≤ I :=
ideal.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_ideal_defs

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variables [decidable_eq ι] [add_comm_monoid ι]  [graded_algebra 𝒜]
variable (I : ideal A)

/--An `I : ideal R` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def ideal.is_homogeneous : Prop :=
∀ (i : ι) ⦃r : A⦄, r ∈ I → (graded_algebra.decompose 𝒜 r i : A) ∈ I

lemma ideal.is_homogeneous_iff_forall_subset :
  I.is_homogeneous 𝒜 ↔ ∀ i, (I : set A) ⊆ graded_algebra.proj 𝒜 i ⁻¹' I :=
iff.rfl

lemma ideal.is_homogeneous_iff_subset_Inter :
  I.is_homogeneous 𝒜 ↔ (I : set A) ⊆ ⋂ i, graded_algebra.proj 𝒜 i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma ideal.is_homogeneous.exists_iff_eq_span :
  (∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S)) ↔
    I = I.homogeneous_core 𝒜 :=
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

lemma ideal.is_homogeneous_homogeneous_core : (I.homogeneous_core 𝒜).is_homogeneous 𝒜 :=
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
  { rcases z with ⟨z, hz2⟩,
    rw subtype.image_preimage_coe at hz2,
    exact hz2.2, },
  { exact ideal.subset_span z.2 },
end

variables {𝒜 I}

lemma ideal.is_homogeneous.homogeneous_core_eq_self (h : I.is_homogeneous 𝒜) :
  I = I.homogeneous_core 𝒜 :=
begin
  apply le_antisymm _ (I.homogeneous_core_le_ideal 𝒜),
  intros x hx,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw ←graded_algebra.sum_support_decompose 𝒜 x,
  refine ideal.sum_mem _ _,
  intros j hj,
  apply ideal.subset_span,
  exact ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩,
end

variables (𝒜 I)

lemma ideal.is_homogeneous.iff_eq :
  I.is_homogeneous 𝒜 ↔ I = I.homogeneous_core 𝒜 :=
⟨ λ hI, hI.homogeneous_core_eq_self,
  λ hI, hI.symm ▸ I.is_homogeneous_homogeneous_core 𝒜 ⟩

lemma ideal.is_homogeneous.iff_exists :
  I.is_homogeneous 𝒜 ↔ ∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S) :=
by rw [ideal.is_homogeneous.exists_iff_eq_span, ideal.is_homogeneous.iff_eq]

end is_homogeneous_ideal_defs

section operations

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables [decidable_eq ι] [add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

/--For any `comm_ring R`, we collect the homogeneous ideals of `R` into a type.-/
abbreviation homogeneous_ideal : Type* := { I : ideal A // I.is_homogeneous 𝒜 }

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
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I ⊓ J).is_homogeneous 𝒜 :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma ideal.is_homogeneous.Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Inf ℐ).is_homogeneous 𝒜 :=
begin
  intros i x Hx, simp only [ideal.mem_Inf] at Hx ⊢,
  intros J HJ,
  exact h _ HJ _ (Hx HJ),
end

lemma ideal.is_homogeneous.mul {I J : ideal A}
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I * J).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw ideal.span_mul_span',
  refine ⟨s₁ * s₂, congr_arg _ _⟩,
  exact (set.image_mul (submonoid.subtype _).to_mul_hom).symm,
end

lemma ideal.is_homogeneous.sup {I J : ideal A}
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I ⊔ J).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

lemma ideal.is_homogeneous.Sup
  {ℐ : set (ideal A)} (Hℐ : ∀ (I ∈ ℐ), ideal.is_homogeneous 𝒜 I) :
  (Sup ℐ).is_homogeneous 𝒜 :=
begin
  simp_rw ideal.is_homogeneous.iff_exists at Hℐ ⊢,
  choose 𝓈 h𝓈 using Hℐ,
  refine ⟨⋃ I hI, 𝓈 I hI, _⟩,
  simp_rw [set.image_Union, ideal.span_Union, Sup_eq_supr],
  conv in (ideal.span _) { rw ←h𝓈 i x },
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

lemma ideal.homogeneous_core.gc :
  galois_connection
    (subtype.val : homogeneous_ideal 𝒜 → ideal A)
    (λ I, ⟨I.homogeneous_core 𝒜, I.is_homogeneous_homogeneous_core 𝒜⟩ :
      ideal A → homogeneous_ideal 𝒜) :=
λ I J, ⟨
  λ H, show I.1 ≤ ideal.homogeneous_core 𝒜 J, begin
    rw I.2.homogeneous_core_eq_self,
    exact ideal.homogeneous_core_is_mono 𝒜 H,
  end,
  λ H, le_trans H (ideal.homogeneous_core_le_ideal _ _)⟩

/--There is a galois coinsertion between homogeneous ideals and ideals via
`(λ I, I.1)` and `ideal.homogeneous_core`-/
def ideal.homogeneous_core.gi :
  galois_coinsertion
    (subtype.val : homogeneous_ideal 𝒜 → ideal A)
    (λ I, ⟨I.homogeneous_core 𝒜, I.is_homogeneous_homogeneous_core 𝒜⟩ :
      ideal A → homogeneous_ideal 𝒜) :=
{ choice := λ I HI, ⟨I, begin
    have eq : I = I.homogeneous_core 𝒜,
    refine le_antisymm HI _,
    apply (ideal.homogeneous_core_le_ideal 𝒜 I),
    rw eq, apply ideal.is_homogeneous_homogeneous_core,
  end⟩,
  gc := ideal.homogeneous_core.gc 𝒜,
  u_l_le := λ I, by apply ideal.homogeneous_core_le_ideal,
  choice_eq := λ I H, le_antisymm H (I.homogeneous_core_le_ideal _) }

lemma ideal.homogeneous_core_eq_Sup :
  I.homogeneous_core 𝒜 = Sup {J : ideal A | J.is_homogeneous 𝒜 ∧ J ≤ I} :=
begin
  refine (is_lub.Sup_eq _).symm,
  apply is_greatest.is_lub,
  have coe_mono : monotone (coe : {I : ideal A // I.is_homogeneous 𝒜} → ideal A) := λ _ _, id,
  convert coe_mono.map_is_greatest (ideal.homogeneous_core.gc 𝒜).is_greatest_u using 1,
  simp only [subtype.coe_image, exists_prop, mem_set_of_eq, subtype.coe_mk],
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

lemma ideal.is_homogeneous.homogeneous_hull : (I.homogeneous_hull 𝒜).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists,
  use {x : homogeneous_submonoid 𝒜 | ∃ (i : ι) (r : I), (graded_algebra.decompose 𝒜 r i : A) = x},
  rw [ideal.homogeneous_hull], congr, ext r, split; intros h,
  { obtain ⟨i, ⟨x, hx1⟩, hx2⟩ := h,
    exact ⟨⟨_, is_homogeneous_coe _⟩, ⟨⟨i, ⟨⟨x, hx1⟩, rfl⟩⟩, hx2⟩⟩,},
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
  ideal.homogeneous_hull 𝒜 I = Inf { J : ideal A | J.is_homogeneous 𝒜 ∧ I ≤ J } :=
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

lemma homogeneous_hull_eq_supr :
  I.homogeneous_hull 𝒜 = ⨆ i, ideal.span (graded_algebra.proj 𝒜 i '' I) :=
begin
  rw ←ideal.span_Union,
  apply congr_arg ideal.span _,
  ext1, simp only [set.mem_Union, set.mem_image, mem_set_of_eq, graded_algebra.proj_apply,
    set_like.exists, exists_prop, subtype.coe_mk, set_like.mem_coe],
end

variables {𝒜 I}

lemma ideal.is_homogeneous.homogeneous_hull_eq_self (h : I.is_homogeneous 𝒜) :
  ideal.homogeneous_hull 𝒜 I = I :=
begin
  rw ideal.homogeneous_hull.eq_Inf, ext x, split; intros hx,
  rw ideal.mem_Inf at hx, apply hx, refine ⟨h, le_refl I⟩,
  rw ideal.mem_Inf, rintros J ⟨HJ1, HJ2⟩, apply HJ2, exact hx,
end

variables (𝒜 I)

end homogeneous_hull

section galois_connection

variables {ι R A : Type*} [comm_ring R] [comm_ring A]
variables [algebra R A] [decidable_eq ι] [add_comm_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

lemma ideal.homgeneous_hull.gc :
  galois_connection
    (λ I, ⟨ideal.homogeneous_hull 𝒜 I, ideal.is_homogeneous.homogeneous_hull 𝒜 I⟩ :
      ideal A → homogeneous_ideal 𝒜)
    (λ I, I.1 : homogeneous_ideal 𝒜 → ideal A) :=
λ I J,
⟨ λ H, begin
    refine le_trans _ H,
    apply ideal.ideal_le_homogeneous_hull,
  end,
  λ H, begin
    show ideal.homogeneous_hull 𝒜 I ≤ J.val,
    rw ←J.2.homogeneous_hull_eq_self,
    exact ideal.homogeneous_hull_is_mono 𝒜 H,
  end ⟩


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

end galois_connection
