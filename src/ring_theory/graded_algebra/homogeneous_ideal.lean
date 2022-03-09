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
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `graded_algebra 𝒜` where `𝒜 : ι → submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous 𝒜 I`: The property that an ideal is closed under `graded_algebra.proj`.
* `homogeneous_ideal 𝒜`: The subtype of ideals which satisfy `ideal.is_homogeneous`
* `ideal.homogeneous_core I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `ideal.homogeneous_hull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `homogeneous_ideal.complete_lattice`: `ideal.is_homogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `ideal.homogeneous_core.gi`: `ideal.homogeneous_core` forms a galois insertion with coercion.
* `ideal.homogeneous_hull.gi`: `ideal.homogeneous_hull` forms a galois insertion with coercion.

## Implementation notes

We introduce `ideal.homogeneous_core'` earlier than might be expected so that we can get access
to `ideal.is_homogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/

open set_like direct_sum set
open_locale big_operators pointwise direct_sum

variables {ι R A : Type*}

section homogeneous_def

variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variables [decidable_eq ι] [add_monoid ι] [graded_algebra 𝒜]
variable (I : ideal A)

/--An `I : ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def ideal.is_homogeneous : Prop :=
∀ (i : ι) ⦃r : A⦄, r ∈ I → (graded_algebra.decompose 𝒜 r i : A) ∈ I

/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
abbreviation homogeneous_ideal : Type* := { I : ideal A // I.is_homogeneous 𝒜 }

instance : has_mem A (homogeneous_ideal 𝒜) :=
{ mem := λ r I, r ∈ (I : ideal A) }

end homogeneous_def

section homogeneous_core

variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variable (I : ideal A)

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def ideal.homogeneous_core' : ideal A :=
ideal.span (coe '' ((coe : subtype (is_homogeneous 𝒜) → A) ⁻¹' I))

lemma ideal.homogeneous_core'_mono : monotone (ideal.homogeneous_core' 𝒜) :=
λ I J I_le_J, ideal.span_mono $ set.image_subset _ $ λ x, @I_le_J _

lemma ideal.homogeneous_core'_le : I.homogeneous_core' 𝒜 ≤ I :=
ideal.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_ideal_defs

variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variables [decidable_eq ι] [add_monoid ι] [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.is_homogeneous_iff_forall_subset :
  I.is_homogeneous 𝒜 ↔ ∀ i, (I : set A) ⊆ graded_algebra.proj 𝒜 i ⁻¹' I :=
iff.rfl

lemma ideal.is_homogeneous_iff_subset_Inter :
  I.is_homogeneous 𝒜 ↔ (I : set A) ⊆ ⋂ i, graded_algebra.proj 𝒜 i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma ideal.mul_homogeneous_element_mem_of_mem
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
  erw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem 𝒜 mem₁,
    coe_of_submodule_apply 𝒜, submodule.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end

lemma ideal.is_homogeneous_span (s : set A) (h : ∀ x ∈ s, is_homogeneous 𝒜 x) :
  (ideal.span s).is_homogeneous 𝒜 :=
begin
  rintros i r hr,
  rw [ideal.span, finsupp.span_eq_range_total] at hr,
  rw linear_map.mem_range at hr,
  obtain ⟨s, rfl⟩ := hr,
  rw [←graded_algebra.proj_apply, finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  refine ideal.sum_mem _ _,
  rintros z hz1,
  rw [smul_eq_mul],
  refine ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i,
  { rcases z with ⟨z, hz2⟩,
    apply h _ hz2, },
  { exact ideal.subset_span z.2 },
end

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.-/
def ideal.homogeneous_core : homogeneous_ideal 𝒜 :=
⟨ideal.homogeneous_core' 𝒜 I,
  ideal.is_homogeneous_span _ _ (λ x h, by { rw [subtype.image_preimage_coe] at h, exact h.2 })⟩

lemma ideal.homogeneous_core_mono : monotone (ideal.homogeneous_core 𝒜) :=
ideal.homogeneous_core'_mono 𝒜

lemma ideal.coe_homogeneous_core_le : ↑(I.homogeneous_core 𝒜) ≤ I :=
ideal.homogeneous_core'_le 𝒜 I

variables {𝒜 I}

lemma ideal.mem_homogeneous_core_of_is_homogeneous_of_mem {x : A}
  (h : set_like.is_homogeneous 𝒜 x) (hmem : x ∈ I) : x ∈ I.homogeneous_core 𝒜 :=
ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

lemma ideal.is_homogeneous.coe_homogeneous_core_eq_self (h : I.is_homogeneous 𝒜) :
  ↑(I.homogeneous_core 𝒜) = I :=
begin
  apply le_antisymm (I.homogeneous_core'_le 𝒜) _,
  intros x hx,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw ←graded_algebra.sum_support_decompose 𝒜 x,
  exact ideal.sum_mem _ (λ j hj, ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩)
end

@[simp] lemma homogeneous_ideal.homogeneous_core_coe_eq_self (I : homogeneous_ideal 𝒜) :
  (I : ideal A).homogeneous_core 𝒜 = I :=
subtype.coe_injective $ ideal.is_homogeneous.coe_homogeneous_core_eq_self I.prop

variables (𝒜 I)

lemma ideal.is_homogeneous.iff_eq : I.is_homogeneous 𝒜 ↔ ↑(I.homogeneous_core 𝒜) = I :=
⟨ λ hI, hI.coe_homogeneous_core_eq_self,
  λ hI, hI ▸ (ideal.homogeneous_core 𝒜 I).2 ⟩

lemma ideal.is_homogeneous.iff_exists :
  I.is_homogeneous 𝒜 ↔ ∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S) :=
begin
  rw [ideal.is_homogeneous.iff_eq, eq_comm],
  exact ((set.image_preimage.compose (submodule.gi _ _).gc).exists_eq_l _).symm,
end

end is_homogeneous_ideal_defs

/-! ### Operations

In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/

section operations

section semiring

variables [comm_semiring R] [semiring A] [algebra R A]
variables [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

namespace ideal.is_homogeneous

lemma bot : ideal.is_homogeneous 𝒜 ⊥ := λ i r hr,
begin
  simp only [ideal.mem_bot] at hr,
  rw [hr, alg_equiv.map_zero, zero_apply],
  apply ideal.zero_mem
end

lemma top : ideal.is_homogeneous 𝒜 ⊤ :=
λ i r hr, by simp only [submodule.mem_top]

variables {𝒜}

lemma inf {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊓ J).is_homogeneous 𝒜 :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Inf ℐ).is_homogeneous 𝒜 :=
begin
  intros i x Hx,
  simp only [ideal.mem_Inf] at Hx ⊢,
  intros J HJ,
  exact h _ HJ _ (Hx HJ),
end

lemma sup {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊔ J).is_homogeneous 𝒜 :=
begin
  rw iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

lemma Sup {ℐ : set (ideal A)} (Hℐ : ∀ (I ∈ ℐ), ideal.is_homogeneous 𝒜 I) :
  (Sup ℐ).is_homogeneous 𝒜 :=
begin
  simp_rw iff_exists at Hℐ ⊢,
  choose 𝓈 h𝓈 using Hℐ,
  refine ⟨⋃ I hI, 𝓈 I hI, _⟩,
  simp_rw [set.image_Union, ideal.span_Union, Sup_eq_supr],
  conv in (ideal.span _) { rw ←h𝓈 i x },
end

end ideal.is_homogeneous

variables {𝒜}

namespace homogeneous_ideal

instance : partial_order (homogeneous_ideal 𝒜) :=
partial_order.lift _ subtype.coe_injective

instance : has_bot (homogeneous_ideal 𝒜) :=
⟨⟨⊥, ideal.is_homogeneous.bot 𝒜⟩⟩

@[simp] lemma coe_bot : ↑(⊥ : homogeneous_ideal 𝒜) = (⊥ : ideal A) := rfl

@[simp] lemma eq_bot_iff (I : homogeneous_ideal 𝒜) : I = ⊥ ↔ (I : ideal A) = ⊥ :=
subtype.ext_iff

instance : has_top (homogeneous_ideal 𝒜) :=
⟨⟨⊤, ideal.is_homogeneous.top 𝒜⟩⟩

@[simp] lemma coe_top : ↑(⊤ : homogeneous_ideal 𝒜) = (⊤ : ideal A) := rfl

@[simp] lemma eq_top_iff (I : homogeneous_ideal 𝒜) : I = ⊤ ↔ (I : ideal A) = ⊤ :=
subtype.ext_iff

instance : has_inf (homogeneous_ideal 𝒜) :=
{ inf := λ I J, ⟨I ⊓ J, I.prop.inf J.prop⟩ }

@[simp] lemma coe_inf (I J : homogeneous_ideal 𝒜) : ↑(I ⊓ J) = (I ⊓ J : ideal A) := rfl

instance : has_Inf (homogeneous_ideal 𝒜) :=
{ Inf := λ ℐ, ⟨Inf (coe '' ℐ), ideal.is_homogeneous.Inf $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

@[simp] lemma coe_Inf (ℐ : set (homogeneous_ideal 𝒜)) : ↑(Inf ℐ) = (Inf (coe '' ℐ) : ideal A) :=
rfl

@[simp] lemma coe_infi {ι' : Sort*} (s : ι' → homogeneous_ideal 𝒜) :
  ↑(⨅ i, s i) = ⨅ i, (s i : ideal A) :=
by rw [infi, infi, coe_Inf, ←set.range_comp]

instance : has_sup (homogeneous_ideal 𝒜) :=
{ sup := λ I J, ⟨I ⊔ J, I.prop.sup J.prop⟩ }

@[simp] lemma coe_sup (I J : homogeneous_ideal 𝒜) : ↑(I ⊔ J) = (I ⊔ J : ideal A) := rfl

instance : has_Sup (homogeneous_ideal 𝒜) :=
{ Sup := λ ℐ, ⟨Sup (coe '' ℐ), ideal.is_homogeneous.Sup $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

@[simp] lemma coe_Sup (ℐ : set (homogeneous_ideal 𝒜)) : ↑(Sup ℐ) = (Sup (coe '' ℐ) : ideal A) :=
rfl

@[simp] lemma coe_supr {ι' : Sort*} (s : ι' → homogeneous_ideal 𝒜) :
  ↑(⨆ i, s i) = ⨆ i, (s i : ideal A) :=
by rw [supr, supr, coe_Sup, ←set.range_comp]

instance : complete_lattice (homogeneous_ideal 𝒜) :=
subtype.coe_injective.complete_lattice _ coe_sup coe_inf coe_Sup coe_Inf coe_top coe_bot

instance : has_add (homogeneous_ideal 𝒜) := ⟨(⊔)⟩

@[simp] lemma coe_add (I J : homogeneous_ideal 𝒜) : ↑(I + J) = (I + J : ideal A) := rfl

instance : inhabited (homogeneous_ideal 𝒜) := { default := ⊥ }

end homogeneous_ideal

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [algebra R A]
variables [decidable_eq ι] [add_monoid ι]
variables {𝒜 : ι → submodule R A} [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.is_homogeneous.mul {I J : ideal A}
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I * J).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw ideal.span_mul_span',
  refine ⟨s₁ * s₂, congr_arg _ _⟩,
  exact (set.image_mul (submonoid.subtype _).to_mul_hom).symm,
end

variables {𝒜}

instance : has_mul (homogeneous_ideal 𝒜) :=
{ mul := λ I J, ⟨I * J, I.prop.mul J.prop⟩ }

@[simp] lemma homogeneous_ideal.coe_mul (I J : homogeneous_ideal 𝒜) :
  ↑(I * J) = (I * J : ideal A) := rfl

end comm_semiring

end operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/

section homogeneous_core

variables [comm_semiring R] [semiring A]
variables [algebra R A] [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.homogeneous_core.gc : galois_connection coe (ideal.homogeneous_core 𝒜) :=
λ I J, ⟨
  λ H, I.homogeneous_core_coe_eq_self ▸ ideal.homogeneous_core_mono 𝒜 H,
  λ H, le_trans H (ideal.homogeneous_core'_le _ _)⟩

/--`coe : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def ideal.homogeneous_core.gi : galois_coinsertion coe (ideal.homogeneous_core 𝒜) :=
{ choice := λ I HI, ⟨I, le_antisymm (I.coe_homogeneous_core_le 𝒜) HI ▸ subtype.prop _⟩,
  gc := ideal.homogeneous_core.gc 𝒜,
  u_l_le := λ I, ideal.homogeneous_core'_le _ _,
  choice_eq := λ I H, le_antisymm H (I.coe_homogeneous_core_le _) }

lemma ideal.homogeneous_core_eq_Sup :
  I.homogeneous_core 𝒜 = Sup {J : homogeneous_ideal 𝒜 | ↑J ≤ I} :=
eq.symm $ is_lub.Sup_eq $ (ideal.homogeneous_core.gc 𝒜).is_greatest_u.is_lub

lemma ideal.homogeneous_core'_eq_Sup :
  I.homogeneous_core' 𝒜 = Sup {J : ideal A | J.is_homogeneous 𝒜 ∧ J ≤ I} :=
begin
  refine (is_lub.Sup_eq _).symm,
  apply is_greatest.is_lub,
  have coe_mono : monotone (coe : {I : ideal A // I.is_homogeneous 𝒜} → ideal A) := λ _ _, id,
  convert coe_mono.map_is_greatest (ideal.homogeneous_core.gc 𝒜).is_greatest_u using 1,
  simp only [subtype.coe_image, exists_prop, mem_set_of_eq, subtype.coe_mk],
end

end homogeneous_core

/-! ### Homogeneous hulls -/

section homogeneous_hull

variables [comm_semiring R] [semiring A]
variables [algebra R A] [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def ideal.homogeneous_hull : homogeneous_ideal 𝒜 :=
⟨ideal.span {r : A | ∃ (i : ι) (x : I), (graded_algebra.decompose 𝒜 x i : A) = r}, begin
  refine ideal.is_homogeneous_span _ _ (λ x hx, _),
  obtain ⟨i, x, rfl⟩ := hx,
  apply set_like.is_homogeneous_coe
end⟩

lemma ideal.le_coe_homogeneous_hull :
  I ≤ ideal.homogeneous_hull 𝒜 I :=
begin
  intros r hr,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw [←graded_algebra.sum_support_decompose 𝒜 r],
  refine ideal.sum_mem _ _, intros j hj,
  apply ideal.subset_span, use j, use ⟨r, hr⟩, refl,
end

lemma ideal.homogeneous_hull_mono : monotone (ideal.homogeneous_hull 𝒜) := λ I J I_le_J,
begin
  apply ideal.span_mono,
  rintros r ⟨hr1, ⟨x, hx⟩, rfl⟩,
  refine ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩,
end

variables {I 𝒜}

lemma ideal.is_homogeneous.homogeneous_hull_eq_self (h : I.is_homogeneous 𝒜) :
  ↑(ideal.homogeneous_hull 𝒜 I) = I :=
begin
  apply le_antisymm _ (ideal.le_coe_homogeneous_hull _ _),
  apply (ideal.span_le).2,
  rintros _ ⟨i, x, rfl⟩,
  exact h _ x.prop,
end

@[simp] lemma homogeneous_ideal.homogeneous_hull_coe_eq_self (I : homogeneous_ideal 𝒜) :
  (I : ideal A).homogeneous_hull 𝒜 = I :=
subtype.coe_injective $ ideal.is_homogeneous.homogeneous_hull_eq_self I.prop

variables (I 𝒜)

lemma ideal.coe_homogeneous_hull_eq_supr :
  ↑(I.homogeneous_hull 𝒜) = ⨆ i, ideal.span (graded_algebra.proj 𝒜 i '' I) :=
begin
  rw ←ideal.span_Union,
  apply congr_arg ideal.span _,
  ext1,
  simp only [set.mem_Union, set.mem_image, mem_set_of_eq, graded_algebra.proj_apply,
    set_like.exists, exists_prop, subtype.coe_mk, set_like.mem_coe],
end

lemma ideal.homogeneous_hull_eq_supr :
  (I.homogeneous_hull 𝒜) =
  ⨆ i, ⟨ideal.span (graded_algebra.proj 𝒜 i '' I), ideal.is_homogeneous_span 𝒜 _
    (by {rintros _ ⟨x, -, rfl⟩, apply set_like.is_homogeneous_coe})⟩ :=
by { ext1, rw [ideal.coe_homogeneous_hull_eq_supr, homogeneous_ideal.coe_supr], refl, }

end homogeneous_hull

section galois_connection

variables [comm_semiring R] [semiring A]
variables [algebra R A] [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

lemma ideal.homogeneous_hull.gc : galois_connection (ideal.homogeneous_hull 𝒜) coe :=
λ I J, ⟨
  le_trans (ideal.le_coe_homogeneous_hull _ _),
  λ H, J.homogeneous_hull_coe_eq_self ▸ ideal.homogeneous_hull_mono 𝒜 H⟩

/-- `ideal.homogeneous_hull 𝒜` and `coe : homogeneous_ideal 𝒜 → ideal A` forms a galois insertion-/
def ideal.homogeneous_hull.gi : galois_insertion (ideal.homogeneous_hull 𝒜) coe :=
{ choice := λ I H, ⟨I, le_antisymm H (I.le_coe_homogeneous_hull 𝒜) ▸ subtype.prop _⟩,
  gc := ideal.homogeneous_hull.gc 𝒜,
  le_l_u := λ I, ideal.le_coe_homogeneous_hull _ _,
  choice_eq := λ I H, le_antisymm (I.le_coe_homogeneous_hull 𝒜) H}

lemma ideal.homogeneous_hull_eq_Inf (I : ideal A) :
  ideal.homogeneous_hull 𝒜 I = Inf { J : homogeneous_ideal 𝒜 | I ≤ J } :=
eq.symm $ is_glb.Inf_eq $ (ideal.homogeneous_hull.gc 𝒜).is_least_l.is_glb

end galois_connection
