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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines homogeneous ideals of `graded_ring 𝒜` where `𝒜 : ι → submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous 𝒜 I`: The property that an ideal is closed under `graded_ring.proj`.
* `homogeneous_ideal 𝒜`: The structure extending ideals which satisfy `ideal.is_homogeneous`
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

variables {ι σ R A : Type*}

section homogeneous_def

variables [semiring A]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ)
variables [decidable_eq ι] [add_monoid ι] [graded_ring 𝒜]
variable (I : ideal A)
include A

/--An `I : ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def ideal.is_homogeneous : Prop :=
∀ (i : ι) ⦃r : A⦄, r ∈ I → (direct_sum.decompose 𝒜 r i : A) ∈ I

/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
structure homogeneous_ideal extends submodule A A :=
(is_homogeneous' : ideal.is_homogeneous 𝒜 to_submodule)

variable {𝒜}
/--Converting a homogeneous ideal to an ideal-/
def homogeneous_ideal.to_ideal (I : homogeneous_ideal 𝒜) : ideal A := I.to_submodule

lemma homogeneous_ideal.is_homogeneous (I : homogeneous_ideal 𝒜) :
  I.to_ideal.is_homogeneous 𝒜 := I.is_homogeneous'

lemma homogeneous_ideal.to_ideal_injective :
  function.injective (homogeneous_ideal.to_ideal : homogeneous_ideal 𝒜 → ideal A) :=
λ ⟨x, hx⟩ ⟨y, hy⟩ (h : x = y), by simp [h]

instance homogeneous_ideal.set_like : set_like (homogeneous_ideal 𝒜) A :=
{ coe := λ I, I.to_ideal,
  coe_injective' := λ I J h, homogeneous_ideal.to_ideal_injective $ set_like.coe_injective h }

@[ext] lemma homogeneous_ideal.ext {I J : homogeneous_ideal 𝒜}
  (h : I.to_ideal = J.to_ideal) : I = J := homogeneous_ideal.to_ideal_injective h

@[simp] lemma homogeneous_ideal.mem_iff {I : homogeneous_ideal 𝒜} {x : A} :
  x ∈ I.to_ideal ↔ x ∈ I := iff.rfl

end homogeneous_def

section homogeneous_core

variables [semiring A]
variables [set_like σ A]  (𝒜 : ι → σ)
variable (I : ideal A)
include A

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def ideal.homogeneous_core' (I : ideal A) : ideal A :=
ideal.span (coe '' ((coe : subtype (is_homogeneous 𝒜) → A) ⁻¹' I))

lemma ideal.homogeneous_core'_mono : monotone (ideal.homogeneous_core' 𝒜) :=
λ I J I_le_J, ideal.span_mono $ set.image_subset _ $ λ x, @I_le_J _

lemma ideal.homogeneous_core'_le : I.homogeneous_core' 𝒜 ≤ I :=
ideal.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_ideal_defs

variables [semiring A]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ)
variables [decidable_eq ι] [add_monoid ι] [graded_ring 𝒜]
variable (I : ideal A)
include A

lemma ideal.is_homogeneous_iff_forall_subset :
  I.is_homogeneous 𝒜 ↔ ∀ i, (I : set A) ⊆ graded_ring.proj 𝒜 i ⁻¹' I :=
iff.rfl

lemma ideal.is_homogeneous_iff_subset_Inter :
  I.is_homogeneous 𝒜 ↔ (I : set A) ⊆ ⋂ i, graded_ring.proj 𝒜 i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma ideal.mul_homogeneous_element_mem_of_mem
  {I : ideal A} (r x : A) (hx₁ : is_homogeneous 𝒜 x) (hx₂ : x ∈ I) (j : ι) :
  graded_ring.proj 𝒜 j (r * x) ∈ I :=
begin
  classical,
  rw [←direct_sum.sum_support_decompose 𝒜 r, finset.sum_mul, map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (direct_sum.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) := graded_monoid.mul_mem
    (set_like.coe_mem _) hi,
  erw [graded_ring.proj_apply, direct_sum.decompose_of_mem 𝒜 mem₁,
    coe_of_apply, set_like.coe_mk],
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
  rw [finsupp.total_apply, finsupp.sum, decompose_sum, dfinsupp.finset_sum_apply,
    add_submonoid_class.coe_finset_sum],
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

lemma ideal.to_ideal_homogeneous_core_le : (I.homogeneous_core 𝒜).to_ideal ≤ I :=
ideal.homogeneous_core'_le 𝒜 I

variables {𝒜 I}

lemma ideal.mem_homogeneous_core_of_is_homogeneous_of_mem {x : A}
  (h : set_like.is_homogeneous 𝒜 x) (hmem : x ∈ I) : x ∈ I.homogeneous_core 𝒜 :=
ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

lemma ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self (h : I.is_homogeneous 𝒜) :
  (I.homogeneous_core 𝒜).to_ideal = I :=
begin
  apply le_antisymm (I.homogeneous_core'_le 𝒜) _,
  intros x hx,
  classical,
  rw ←direct_sum.sum_support_decompose 𝒜 x,
  exact ideal.sum_mem _ (λ j hj, ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩)
end

@[simp] lemma homogeneous_ideal.to_ideal_homogeneous_core_eq_self (I : homogeneous_ideal 𝒜) :
  I.to_ideal.homogeneous_core 𝒜 = I :=
by ext1; convert ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self I.is_homogeneous

variables (𝒜 I)

lemma ideal.is_homogeneous.iff_eq : I.is_homogeneous 𝒜 ↔ (I.homogeneous_core 𝒜).to_ideal = I :=
⟨ λ hI, hI.to_ideal_homogeneous_core_eq_self,
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

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
include A

namespace ideal.is_homogeneous

lemma bot : ideal.is_homogeneous 𝒜 ⊥ := λ i r hr,
begin
  simp only [ideal.mem_bot] at hr,
  rw [hr, decompose_zero, zero_apply],
  apply ideal.zero_mem
end

lemma top : ideal.is_homogeneous 𝒜 ⊤ :=
λ i r hr, by simp only [submodule.mem_top]

variables {𝒜}

lemma inf {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊓ J).is_homogeneous 𝒜 :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma sup {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊔ J).is_homogeneous 𝒜 :=
begin
  rw iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

protected lemma supr {κ : Sort*} {f : κ → ideal A} (h : ∀ i, (f i).is_homogeneous 𝒜) :
  (⨆ i, f i).is_homogeneous 𝒜 :=
begin
  simp_rw iff_exists at h ⊢,
  choose s hs using h,
  refine ⟨⋃ i, s i, _⟩,
  simp_rw [set.image_Union, ideal.span_Union],
  congr',
  exact funext hs,
end

protected lemma infi {κ : Sort*} {f : κ → ideal A} (h : ∀ i, (f i).is_homogeneous 𝒜) :
  (⨅ i, f i).is_homogeneous 𝒜 :=
begin
  intros i x hx,
  simp only [ideal.mem_infi] at ⊢ hx,
  exact λ j, h _ _ (hx j),
end

lemma supr₂ {κ : Sort*} {κ' : κ → Sort*} {f : Π i, κ' i → ideal A}
  (h : ∀ i j, (f i j).is_homogeneous 𝒜) :
  (⨆ i j, f i j).is_homogeneous 𝒜 :=
is_homogeneous.supr $ λ i, is_homogeneous.supr $ h i

lemma infi₂ {κ : Sort*} {κ' : κ → Sort*} {f : Π i, κ' i → ideal A}
  (h : ∀ i j, (f i j).is_homogeneous 𝒜) :
  (⨅ i j, f i j).is_homogeneous 𝒜 :=
is_homogeneous.infi $ λ i, is_homogeneous.infi $ h i

lemma Sup {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Sup ℐ).is_homogeneous 𝒜 :=
by { rw Sup_eq_supr, exact supr₂ h }

lemma Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Inf ℐ).is_homogeneous 𝒜 :=
by { rw Inf_eq_infi, exact infi₂ h }

end ideal.is_homogeneous

variables {𝒜}

namespace homogeneous_ideal

instance : partial_order (homogeneous_ideal 𝒜) := set_like.partial_order

instance : has_top (homogeneous_ideal 𝒜) := ⟨⟨⊤, ideal.is_homogeneous.top 𝒜⟩⟩
instance : has_bot (homogeneous_ideal 𝒜) := ⟨⟨⊥, ideal.is_homogeneous.bot 𝒜⟩⟩
instance : has_sup (homogeneous_ideal 𝒜) := ⟨λ I J, ⟨_, I.is_homogeneous.sup J.is_homogeneous⟩⟩
instance : has_inf (homogeneous_ideal 𝒜) := ⟨λ I J, ⟨_, I.is_homogeneous.inf J.is_homogeneous⟩⟩
instance : has_Sup (homogeneous_ideal 𝒜) :=
⟨λ S, ⟨⨆ s ∈ S, to_ideal s, ideal.is_homogeneous.supr₂ $ λ s _, s.is_homogeneous⟩⟩
instance : has_Inf (homogeneous_ideal 𝒜) :=
⟨λ S, ⟨⨅ s ∈ S, to_ideal s, ideal.is_homogeneous.infi₂ $ λ s _, s.is_homogeneous⟩⟩

@[simp] lemma coe_top : ((⊤ : homogeneous_ideal 𝒜) : set A) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : homogeneous_ideal 𝒜) : set A) = 0 := rfl
@[simp] lemma coe_sup (I J : homogeneous_ideal 𝒜) : ↑(I ⊔ J) = (I + J : set A) :=
submodule.coe_sup _ _
@[simp] lemma coe_inf (I J : homogeneous_ideal 𝒜) : (↑(I ⊓ J) : set A) = I ∩ J := rfl

@[simp] lemma to_ideal_top : (⊤ : homogeneous_ideal 𝒜).to_ideal = (⊤ : ideal A) := rfl
@[simp] lemma to_ideal_bot : (⊥ : homogeneous_ideal 𝒜).to_ideal = (⊥ : ideal A) := rfl

@[simp] lemma to_ideal_sup (I J : homogeneous_ideal 𝒜) :
  (I ⊔ J).to_ideal = I.to_ideal ⊔ J.to_ideal := rfl

@[simp] lemma to_ideal_inf (I J : homogeneous_ideal 𝒜) :
  (I ⊓ J).to_ideal = I.to_ideal ⊓ J.to_ideal := rfl

@[simp] lemma to_ideal_Sup (ℐ : set (homogeneous_ideal 𝒜)) :
  (Sup ℐ).to_ideal = ⨆ s ∈ ℐ, to_ideal s := rfl

@[simp] lemma to_ideal_Inf (ℐ : set (homogeneous_ideal 𝒜)) :
  (Inf ℐ).to_ideal = ⨅ s ∈ ℐ, to_ideal s := rfl

@[simp] lemma to_ideal_supr {κ : Sort*} (s : κ → homogeneous_ideal 𝒜) :
  (⨆ i, s i).to_ideal = ⨆ i, (s i).to_ideal :=
by rw [supr, to_ideal_Sup, supr_range]

@[simp] lemma to_ideal_infi {κ : Sort*} (s : κ → homogeneous_ideal 𝒜) :
  (⨅ i, s i).to_ideal = ⨅ i, (s i).to_ideal :=
by rw [infi, to_ideal_Inf, infi_range]

@[simp] lemma to_ideal_supr₂ {κ : Sort*} {κ' : κ → Sort*} (s : Π i, κ' i → homogeneous_ideal 𝒜) :
  (⨆ i j, s i j).to_ideal = ⨆ i j, (s i j).to_ideal :=
by simp_rw to_ideal_supr

@[simp] lemma to_ideal_infi₂ {κ : Sort*} {κ' : κ → Sort*} (s : Π i, κ' i → homogeneous_ideal 𝒜) :
  (⨅ i j, s i j).to_ideal = ⨅ i j, (s i j).to_ideal :=
by simp_rw to_ideal_infi

@[simp] lemma eq_top_iff (I : homogeneous_ideal 𝒜) : I = ⊤ ↔ I.to_ideal = ⊤ :=
to_ideal_injective.eq_iff.symm

@[simp] lemma eq_bot_iff (I : homogeneous_ideal 𝒜) : I = ⊥ ↔ I.to_ideal = ⊥ :=
to_ideal_injective.eq_iff.symm

instance : complete_lattice (homogeneous_ideal 𝒜) :=
to_ideal_injective.complete_lattice _ to_ideal_sup to_ideal_inf to_ideal_Sup to_ideal_Inf
  to_ideal_top to_ideal_bot

instance : has_add (homogeneous_ideal 𝒜) := ⟨(⊔)⟩

@[simp] lemma to_ideal_add (I J : homogeneous_ideal 𝒜) :
  (I + J).to_ideal = I.to_ideal + J.to_ideal := rfl

instance : inhabited (homogeneous_ideal 𝒜) := { default := ⊥ }

end homogeneous_ideal

end semiring

section comm_semiring
variables [comm_semiring A]
variables [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] {𝒜 : ι → σ} [graded_ring 𝒜]
variable (I : ideal A)
include A

lemma ideal.is_homogeneous.mul {I J : ideal A}
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I * J).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw ideal.span_mul_span',
  exact ⟨s₁ * s₂, congr_arg _ $ (set.image_mul (homogeneous_submonoid 𝒜).subtype).symm⟩,
end

variables {𝒜}

instance : has_mul (homogeneous_ideal 𝒜) :=
{ mul := λ I J, ⟨I.to_ideal * J.to_ideal, I.is_homogeneous.mul J.is_homogeneous⟩ }

@[simp] lemma homogeneous_ideal.to_ideal_mul (I J : homogeneous_ideal 𝒜) :
  (I * J).to_ideal = I.to_ideal * J.to_ideal := rfl

end comm_semiring

end operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/

section homogeneous_core

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
variable (I : ideal A)
include A

lemma ideal.homogeneous_core.gc : galois_connection to_ideal (ideal.homogeneous_core 𝒜) :=
λ I J, ⟨
  λ H, I.to_ideal_homogeneous_core_eq_self ▸ ideal.homogeneous_core_mono 𝒜 H,
  λ H, le_trans H (ideal.homogeneous_core'_le _ _)⟩

/--`to_ideal : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def ideal.homogeneous_core.gi : galois_coinsertion to_ideal (ideal.homogeneous_core 𝒜) :=
{ choice := λ I HI,
    ⟨I, le_antisymm (I.to_ideal_homogeneous_core_le 𝒜) HI ▸ homogeneous_ideal.is_homogeneous _⟩,
  gc := ideal.homogeneous_core.gc 𝒜,
  u_l_le := λ I, ideal.homogeneous_core'_le _ _,
  choice_eq := λ I H, le_antisymm H (I.to_ideal_homogeneous_core_le _) }

lemma ideal.homogeneous_core_eq_Sup :
  I.homogeneous_core 𝒜 = Sup {J : homogeneous_ideal 𝒜 | J.to_ideal ≤ I} :=
eq.symm $ is_lub.Sup_eq $ (ideal.homogeneous_core.gc 𝒜).is_greatest_u.is_lub

lemma ideal.homogeneous_core'_eq_Sup :
  I.homogeneous_core' 𝒜 = Sup {J : ideal A | J.is_homogeneous 𝒜 ∧ J ≤ I} :=
begin
  refine (is_lub.Sup_eq _).symm,
  apply is_greatest.is_lub,
  have coe_mono : monotone (to_ideal : homogeneous_ideal 𝒜 → ideal A) := λ x y, id,
  convert coe_mono.map_is_greatest (ideal.homogeneous_core.gc 𝒜).is_greatest_u using 1,
  ext,
  rw [mem_image, mem_set_of_eq],
  refine ⟨λ hI, ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, by rintro ⟨x, ⟨hx, rfl⟩⟩; exact ⟨x.is_homogeneous, hx⟩⟩,
end

end homogeneous_core

/-! ### Homogeneous hulls -/

section homogeneous_hull

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
variable (I : ideal A)
include A

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def ideal.homogeneous_hull : homogeneous_ideal 𝒜 :=
⟨ideal.span {r : A | ∃ (i : ι) (x : I), (direct_sum.decompose 𝒜 (x : A) i : A) = r}, begin
  refine ideal.is_homogeneous_span _ _ (λ x hx, _),
  obtain ⟨i, x, rfl⟩ := hx,
  apply set_like.is_homogeneous_coe
end⟩

lemma ideal.le_to_ideal_homogeneous_hull :
  I ≤ (ideal.homogeneous_hull 𝒜 I).to_ideal :=
begin
  intros r hr,
  classical,
  rw [←direct_sum.sum_support_decompose 𝒜 r],
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

lemma ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self (h : I.is_homogeneous 𝒜) :
  (ideal.homogeneous_hull 𝒜 I).to_ideal = I :=
begin
  apply le_antisymm _ (ideal.le_to_ideal_homogeneous_hull _ _),
  apply (ideal.span_le).2,
  rintros _ ⟨i, x, rfl⟩,
  exact h _ x.prop,
end

@[simp] lemma homogeneous_ideal.homogeneous_hull_to_ideal_eq_self (I : homogeneous_ideal 𝒜) :
  I.to_ideal.homogeneous_hull 𝒜 = I :=
homogeneous_ideal.to_ideal_injective $ I.is_homogeneous.to_ideal_homogeneous_hull_eq_self

variables (I 𝒜)

lemma ideal.to_ideal_homogeneous_hull_eq_supr :
  (I.homogeneous_hull 𝒜).to_ideal = ⨆ i, ideal.span (graded_ring.proj 𝒜 i '' I) :=
begin
  rw ←ideal.span_Union,
  apply congr_arg ideal.span _,
  ext1,
  simp only [set.mem_Union, set.mem_image, mem_set_of_eq, graded_ring.proj_apply,
    set_like.exists, exists_prop, subtype.coe_mk, set_like.mem_coe],
end

lemma ideal.homogeneous_hull_eq_supr :
  (I.homogeneous_hull 𝒜) =
  ⨆ i, ⟨ideal.span (graded_ring.proj 𝒜 i '' I), ideal.is_homogeneous_span 𝒜 _
    (by {rintros _ ⟨x, -, rfl⟩, apply set_like.is_homogeneous_coe})⟩ :=
by { ext1, rw [ideal.to_ideal_homogeneous_hull_eq_supr, to_ideal_supr], refl }

end homogeneous_hull

section galois_connection

open homogeneous_ideal

variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
include A

lemma ideal.homogeneous_hull.gc : galois_connection (ideal.homogeneous_hull 𝒜) to_ideal :=
λ I J, ⟨
  le_trans (ideal.le_to_ideal_homogeneous_hull _ _),
  λ H, J.homogeneous_hull_to_ideal_eq_self ▸ ideal.homogeneous_hull_mono 𝒜 H⟩

/-- `ideal.homogeneous_hull 𝒜` and `to_ideal : homogeneous_ideal 𝒜 → ideal A` form a galois
insertion-/
def ideal.homogeneous_hull.gi : galois_insertion (ideal.homogeneous_hull 𝒜) to_ideal :=
{ choice := λ I H, ⟨I, le_antisymm H (I.le_to_ideal_homogeneous_hull 𝒜) ▸ is_homogeneous _⟩,
  gc := ideal.homogeneous_hull.gc 𝒜,
  le_l_u := λ I, ideal.le_to_ideal_homogeneous_hull _ _,
  choice_eq := λ I H, le_antisymm (I.le_to_ideal_homogeneous_hull 𝒜) H}

lemma ideal.homogeneous_hull_eq_Inf (I : ideal A) :
  ideal.homogeneous_hull 𝒜 I = Inf { J : homogeneous_ideal 𝒜 | I ≤ J.to_ideal } :=
eq.symm $ is_glb.Inf_eq $ (ideal.homogeneous_hull.gc 𝒜).is_least_l.is_glb

end galois_connection

section irrelevant_ideal

variables [semiring A]
variables [decidable_eq ι]
variables [canonically_ordered_add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]
include A

open graded_ring set_like.graded_monoid direct_sum

/--
For a graded ring `⨁ᵢ 𝒜ᵢ` graded by a `canonically_ordered_add_monoid ι`, the irrelevant ideal
refers to `⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj`
construction where `ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.

# Future work
Here in the definition, `ι` is assumed to be `canonically_ordered_add_monoid`. However, the notion
of irrelevant ideal makes sense in a more general setting by defining it as the ideal of elements
with `0` as i-th coordinate for all `i ≤ 0`, i.e. `{a | ∀ (i : ι), i ≤ 0 → aᵢ = 0}`.
-/
def homogeneous_ideal.irrelevant : homogeneous_ideal 𝒜 :=
⟨(graded_ring.proj_zero_ring_hom 𝒜).ker, λ i r (hr : (decompose 𝒜 r 0 : A) = 0), begin
  change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0,
  by_cases h : i = 0,
  { rw [h, hr, decompose_zero, zero_apply, zero_mem_class.coe_zero] },
  { rw [decompose_of_mem_ne 𝒜 (set_like.coe_mem _) h] }
end⟩

@[simp] lemma homogeneous_ideal.mem_irrelevant_iff (a : A) :
  a ∈ homogeneous_ideal.irrelevant 𝒜 ↔ proj 𝒜 0 a = 0 := iff.rfl

@[simp] lemma homogeneous_ideal.to_ideal_irrelevant :
  (homogeneous_ideal.irrelevant 𝒜).to_ideal = (graded_ring.proj_zero_ring_hom 𝒜).ker := rfl

end irrelevant_ideal
