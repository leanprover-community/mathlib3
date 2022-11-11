/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
import category_theory.abelian.opposite
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.limits.preserves.shapes.zero
import category_theory.limits.preserves.shapes.kernels
import category_theory.preadditive.left_exact
import category_theory.adjunction.limits
import algebra.homology.exact
import algebra.homology.short_complex_short_exact
import algebra.homology.short_complex_image_to_kernel
import tactic.tfae

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* `(f, g)` is exact if and only if `f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`. This
  characterisation tends to be less cumbersome to work with than the original definition involving
  the comparison map `image f ⟶ kernel g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* An exact functor preserves exactness, more specifically, `F` preserves finite colimits and
  finite limits, if and only if `exact f g` implies `exact (F.map f) (F.map g)`.
-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.preadditive

variables {C : Type u₁} [category.{v₁} C] [abelian C]

namespace category_theory

namespace abelian

variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

local attribute [instance] has_equalizers_of_has_kernels

/--
In an abelian category, a pair of morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` is exact
iff `image_subobject f = kernel_subobject g`.
-/
theorem exact_iff_image_eq_kernel : exact f g ↔ image_subobject f = kernel_subobject g :=
begin
  split,
  { intro h,
    simpa only [exact_iff_exact_short_complex _ _ h.w, short_complex.exact_iff_image_eq_kernel]
      using h, },
  { intro h,
    simpa only [exact_iff_exact_short_complex _ _ (comp_eq_zero_of_image_eq_kernel f g h),
      short_complex.exact_iff_image_eq_kernel] using h, },
end

theorem exact_iff : exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 :=
begin
  split,
  { intro h,
    exact ⟨h.w, by simpa only [exact_iff_exact_short_complex _ _ h.w,
      short_complex.exact_iff_kernel_ι_comp_cokernel_π_zero] using h⟩, },
  { rintro ⟨h₁, h₂⟩,
    simpa only [exact_iff_exact_short_complex _ _ h₁,
      short_complex.exact_iff_kernel_ι_comp_cokernel_π_zero] using h₂, },
end

theorem exact_iff' {cg : kernel_fork g} (hg : is_limit cg)
  {cf : cokernel_cofork f} (hf : is_colimit cf) : exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 :=
begin
  split,
  { intro h,
    exact ⟨h.1, fork_ι_comp_cofork_π h cg cf⟩ },
  { rw exact_iff,
    refine λ h, ⟨h.1, _⟩,
    apply zero_of_epi_comp (is_limit.cone_point_unique_up_to_iso hg (limit.is_limit _)).hom,
    apply zero_of_comp_mono
      (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).hom,
    simp [h.2] }
end

theorem exact_tfae :
  tfae [exact f g,
        f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0,
        image_subobject f = kernel_subobject g] :=
begin
  tfae_have : 1 ↔ 2, { apply exact_iff },
  tfae_have : 1 ↔ 3, { apply exact_iff_image_eq_kernel },
  tfae_finish
end

lemma is_equivalence.exact_iff {D : Type u₁} [category.{v₁} D] [abelian D]
  (F : C ⥤ D) [is_equivalence F] :
  exact (F.map f) (F.map g) ↔ exact f g :=
begin
  simp only [exact_iff, ← F.map_eq_zero_iff, F.map_comp, category.assoc,
    ← kernel_comparison_comp_ι g F, ← π_comp_cokernel_comparison f F],
  rw [is_iso.comp_left_eq_zero (kernel_comparison g F), ← category.assoc,
    is_iso.comp_right_eq_zero _ (cokernel_comparison f F)],
end

/-- If `(f, g)` is exact, then `abelian.image.ι f` is a kernel of `g`. -/
def is_limit_image (h : exact f g) :
  is_limit
    (kernel_fork.of_ι (abelian.image.ι f) (image_ι_comp_eq_zero h.1) : kernel_fork g) :=
begin
  rw exact_iff at h,
  refine kernel_fork.is_limit.of_ι _ _ _ _ _,
  { refine λ W u hu, kernel.lift (cokernel.π f) u _,
    rw [←kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero] },
  tidy
end

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def is_limit_image' (h : exact f g) :
  is_limit (kernel_fork.of_ι (limits.image.ι f) (limits.image_ι_comp_eq_zero h.1)) :=
is_kernel.iso_kernel _ _ (is_limit_image f g h) (image_iso_image f).symm $ is_image.lift_fac _ _

/-- If `(f, g)` is exact, then `coimages.coimage.π g` is a cokernel of `f`. -/
def is_colimit_coimage (h : exact f g) : is_colimit (cokernel_cofork.of_π (abelian.coimage.π g)
  (abelian.comp_coimage_π_eq_zero h.1) : cokernel_cofork f) :=
begin
  rw exact_iff at h,
  refine cokernel_cofork.is_colimit.of_π _ _ _ _ _,
  { refine λ W u hu, cokernel.desc (kernel.ι g) u _,
    rw [←cokernel.π_desc f u hu, ←category.assoc, h.2, has_zero_morphisms.zero_comp] },
  tidy
end

/-- If `(f, g)` is exact, then `factor_thru_image g` is a cokernel of `f`. -/
def is_colimit_image (h : exact f g) : is_colimit
  (cokernel_cofork.of_π (limits.factor_thru_image g) (comp_factor_thru_image_eq_zero h.1)) :=
is_cokernel.cokernel_iso _ _ (is_colimit_coimage f g h) (coimage_iso_image' g) $
  (cancel_mono (limits.image.ι g)).1 $ by simp

lemma exact_cokernel : exact f (cokernel.π f) :=
by { rw exact_iff, tidy }

instance (h : exact f g) : mono (cokernel.desc f g h.w) :=
suffices h : cokernel.desc f g h.w =
  (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) (is_colimit_image f g h)).hom
    ≫ limits.image.ι g, by { rw h, apply mono_comp },
(cancel_epi (cokernel.π f)).1 $ by simp

/-- If `ex : exact f g` and `epi g`, then `cokernel.desc _ _ ex.w` is an isomorphism. -/
instance (ex : exact f g) [epi g] : is_iso (cokernel.desc f g ex.w) :=
is_iso_of_mono_of_epi (limits.cokernel.desc f g ex.w)

@[simp, reassoc]
lemma cokernel.desc.inv [epi g] (ex : exact f g) :
  g ≫ inv (cokernel.desc _ _ ex.w) = cokernel.π _ :=
by simp

instance (ex : exact f g) [mono f] : is_iso (kernel.lift g f ex.w) :=
is_iso.of_iso (is_limit.cone_point_unique_up_to_iso
    ex.exact.f_is_kernel (kernel_is_kernel g))

@[simp, reassoc]
lemma kernel.lift.inv [mono f] (ex : exact f g) :
  inv (kernel.lift _ _ ex.w) ≫ f = kernel.ι g :=
by simp

/-- If `X ⟶ Y ⟶ Z ⟶ 0` is exact, then the second map is a cokernel of the first. -/
def is_colimit_of_exact_of_epi [epi g] (h : exact f g) :
  is_colimit (cokernel_cofork.of_π _ h.w) :=
is_colimit.of_iso_colimit (colimit.is_colimit _) $ cocones.ext
  ⟨cokernel.desc _ _ h.w, epi_desc g (cokernel.π f) ((exact_iff _ _).1 h).2,
    (cancel_epi (cokernel.π f)).1 (by tidy), (cancel_epi g).1 (by tidy)⟩ (λ j, by cases j; simp)

/-- If `0 ⟶ X ⟶ Y ⟶ Z` is exact, then the first map is a kernel of the second. -/
def is_limit_of_exact_of_mono [mono f] (h : exact f g) :
  is_limit (kernel_fork.of_ι _ h.w) :=
is_limit.of_iso_limit (limit.is_limit _) $ cones.ext
 ⟨mono_lift f (kernel.ι g) ((exact_iff _ _).1 h).2, kernel.lift _ _ h.w,
  (cancel_mono (kernel.ι g)).1 (by tidy), (cancel_mono f).1 (by tidy)⟩ (λ j, by cases j; simp)

lemma exact_of_is_cokernel (w : f ≫ g = 0)
  (h : is_colimit (cokernel_cofork.of_π _ w)) : exact f g :=
begin
  refine (exact_iff _ _).2 ⟨w, _⟩,
  have := h.fac (cokernel_cofork.of_π _ (cokernel.condition f)) walking_parallel_pair.one,
  simp only [cofork.of_π_ι_app] at this,
  rw [← this, ← category.assoc, kernel.condition, zero_comp]
end

lemma exact_of_is_kernel (w : f ≫ g = 0)
  (h : is_limit (kernel_fork.of_ι _ w)) : exact f g :=
begin
  refine (exact_iff _ _).2 ⟨w, _⟩,
  have := h.fac (kernel_fork.of_ι _ (kernel.condition g)) walking_parallel_pair.zero,
  simp only [fork.of_ι_π_app] at this,
  rw [← this, category.assoc, cokernel.condition, comp_zero]
end

lemma exact_iff_exact_image_ι : exact f g ↔ exact (abelian.image.ι f) g :=
by conv_lhs { rw ← abelian.image.fac f }; apply exact_epi_comp_iff

lemma exact_iff_exact_coimage_π : exact f g ↔ exact f (coimage.π g) :=
by conv_lhs { rw ← abelian.coimage.fac g}; apply exact_comp_mono_iff

end abelian

namespace functor

section

variables {D : Type u₂} [category.{v₂} D] [abelian D]
variables (F : C ⥤ D) [preserves_zero_morphisms F]

@[priority 100]
instance reflects_exact_sequences_of_preserves_zero_morphisms_of_faithful [faithful F] :
  reflects_exact_sequences F :=
{ reflects := λ X Y Z f g hfg,
  begin
    rw [abelian.exact_iff, ← F.map_comp, F.map_eq_zero_iff] at hfg,
    refine (abelian.exact_iff _ _).2 ⟨hfg.1, F.zero_of_map_zero _ _⟩,
    obtain ⟨k, hk⟩ := kernel.lift' (F.map g) (F.map (kernel.ι g))
      (by simp only [← F.map_comp, kernel.condition, category_theory.functor.map_zero]),
    obtain ⟨l, hl⟩ := cokernel.desc' (F.map f) (F.map (cokernel.π f))
      (by simp only [← F.map_comp, cokernel.condition, category_theory.functor.map_zero]),
    rw [F.map_comp, ← hk, ← hl, category.assoc, reassoc_of hfg.2, zero_comp, comp_zero]
  end }

end

end functor

namespace functor

open limits abelian

variables {A : Type u₁} {B : Type u₂} [category.{v₁} A] [category.{v₂} B]
variables [abelian A] [abelian B]
variables (L : A ⥤ B)

section

variables (h : ∀ ⦃X Y Z : A⦄ {f : X ⟶ Y} {g : Y ⟶ Z}, exact f g → exact (L.map f) (L.map g))
include h

open_locale zero_object

/-- A functor which preserves exactness preserves zero morphisms. -/
lemma preserves_zero_morphisms_of_map_exact : L.preserves_zero_morphisms :=
begin
  replace h := (h (exact_of_zero (𝟙 0) (𝟙 0))).w,
  rw [L.map_id, category.comp_id] at h,
  exact preserves_zero_morphisms_of_map_zero_object (id_zero_equiv_iso_zero _ h),
end

/-- A functor which preserves exactness preserves monomorphisms. -/
lemma preserves_monomorphisms_of_map_exact : L.preserves_monomorphisms :=
{ preserves := λ X Y f hf,
  begin
    letI := preserves_zero_morphisms_of_map_exact L h,
    apply ((tfae_mono (L.obj 0) (L.map f)).out 2 0).mp,
    rw ←L.map_zero,
    exact h (((tfae_mono 0 f).out 0 2).mp hf)
  end }

/-- A functor which preserves exactness preserves epimorphisms. -/
lemma preserves_epimorphisms_of_map_exact : L.preserves_epimorphisms :=
{ preserves := λ X Y f hf,
  begin
    letI := preserves_zero_morphisms_of_map_exact L h,
    apply ((tfae_epi (L.obj 0) (L.map f)).out 2 0).mp,
    rw ←L.map_zero,
    exact h (((tfae_epi 0 f).out 0 2).mp hf)
  end }

/-- A functor which preserves exactness preserves kernels. -/
def preserves_kernels_of_map_exact (X Y : A) (f : X ⟶ Y) :
  preserves_limit (parallel_pair f 0) L :=
{ preserves := λ c ic,
  begin
    letI := preserves_zero_morphisms_of_map_exact L h,
    letI := preserves_monomorphisms_of_map_exact L h,
    letI := mono_of_is_limit_fork ic,
    have hf := (is_limit_map_cone_fork_equiv' L (kernel_fork.condition c)).symm
      (is_limit_of_exact_of_mono (L.map (fork.ι c)) (L.map f)
        (h (exact_of_is_kernel (fork.ι c) f (kernel_fork.condition c)
          (ic.of_iso_limit (iso_of_ι _))))),
    exact hf.of_iso_limit ((cones.functoriality _ L).map_iso (iso_of_ι _).symm),
  end }

/-- A functor which preserves exactness preserves zero cokernels. -/
def preserves_cokernels_of_map_exact (X Y : A) (f : X ⟶ Y) :
  preserves_colimit (parallel_pair f 0) L :=
{ preserves := λ c ic,
  begin
    letI := preserves_zero_morphisms_of_map_exact L h,
    letI := preserves_epimorphisms_of_map_exact L h,
    letI := epi_of_is_colimit_cofork ic,
    have hf := (is_colimit_map_cocone_cofork_equiv' L (cokernel_cofork.condition c)).symm
      (is_colimit_of_exact_of_epi (L.map f) (L.map (cofork.π c))
        (h (exact_of_is_cokernel f (cofork.π c) (cokernel_cofork.condition c)
          (ic.of_iso_colimit (iso_of_π _))))),
    exact hf.of_iso_colimit ((cocones.functoriality _ L).map_iso (iso_of_π _).symm),
  end }

/-- A functor which preserves exactness is left exact, i.e. preserves finite limits.
This is part of the inverse implication to `functor.map_exact`. -/
def preserves_finite_limits_of_map_exact : preserves_finite_limits L :=
begin
  letI := preserves_zero_morphisms_of_map_exact L h,
  letI := preserves_kernels_of_map_exact L h,
  apply preserves_finite_limits_of_preserves_kernels,
end

/-- A functor which preserves exactness is right exact, i.e. preserves finite colimits.
This is part of the inverse implication to `functor.map_exact`. -/
def preserves_finite_colimits_of_map_exact : preserves_finite_colimits L :=
begin
  letI := preserves_zero_morphisms_of_map_exact L h,
  letI := preserves_cokernels_of_map_exact L h,
  apply preserves_finite_colimits_of_preserves_cokernels,
end

end

section

/-- A functor preserving zero morphisms, monos, and cokernels preserves finite limits. -/
def preserves_finite_limits_of_preserves_monos_and_cokernels
  [preserves_zero_morphisms L] [preserves_monomorphisms L]
  [∀ {X Y} (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) L] : preserves_finite_limits L :=
begin
  apply preserves_finite_limits_of_map_exact,
  intros X Y Z f g h,
  rw [← abelian.coimage.fac g, L.map_comp, exact_comp_mono_iff],
  exact exact_of_is_cokernel _ _ _
    (is_colimit_cofork_map_of_is_colimit' L _ (is_colimit_coimage f g h))
end

/-- A functor preserving zero morphisms, epis, and kernels preserves finite colimits. -/
def preserves_finite_colimits_of_preserves_epis_and_kernels
  [preserves_zero_morphisms L] [preserves_epimorphisms L]
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) L] : preserves_finite_colimits L :=
begin
  apply preserves_finite_colimits_of_map_exact,
  intros X Y Z f g h,
  rw [← abelian.image.fac f, L.map_comp, exact_epi_comp_iff],
  exact exact_of_is_kernel _ _ _ (is_limit_fork_map_of_is_limit' L _ (is_limit_image f g h))
end

end

end functor

end category_theory
