/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.additive_functor
import category_theory.abelian.basic
import category_theory.limits.preserves.shapes.kernels
import category_theory.adjunction.limits

/-!
# Transferring "abelian-ness" across a functor

If `𝒜` is an additive category, `ℬ` is an abelian category,
we have `a : 𝒜 ⥤ ℬ` `b : ℬ ⥤ 𝒜` (both preserving zero morphisms),
`b` is left exact (that is, preserves finite limits),
and further we have `adj : b ⊣ a` and `i : a ⋙ b ≅ 𝟭 𝒜`,
then `𝒜` is also abelian.

See https://stacks.math.columbia.edu/tag/03A3

## Notes
The hypotheses, following the statement from the Stacks project,
may appear suprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : a ⋙ b ≅ 𝟭 𝒜`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `𝒜` is a reflective subcategory of `ℬ`.

Someone may like to formalize that lemma, and restate this theorem in terms of `reflective`.
-/

noncomputable theory

namespace category_theory
open category_theory.limits

universes v u₁ u₂

namespace abelian_of_adjunction

variables {𝒜 : Type u₁} [category.{v} 𝒜] [preadditive 𝒜]
variables {ℬ : Type u₂} [category.{v} ℬ] [abelian ℬ]
variables (a : 𝒜 ⥤ ℬ)
variables (b : ℬ ⥤ 𝒜) [functor.preserves_zero_morphisms b]
variables (i : a ⋙ b ≅ 𝟭 𝒜) (adj : b ⊣ a)

include i

/-- No point making this an instance, as it requires `i`. -/
lemma has_kernels [preserves_finite_limits b] : has_kernels 𝒜 :=
{ has_limit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_kernel (b.map (a.map f) ≫ i.hom.app _) := limits.has_kernel_comp_mono _ _,
    apply limits.has_kernel_iso_comp,
  end }

include adj

/-- No point making this an instance, as it requires `i` and `adj`. -/
lemma has_cokernels : has_cokernels 𝒜 :=
{ has_colimit := λ X Y f, begin
    haveI : preserves_colimits b := adj.left_adjoint_preserves_colimits,
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_cokernel (b.map (a.map f) ≫ i.hom.app _) := limits.has_cokernel_comp_iso _ _,
    apply limits.has_cokernel_epi_comp,
  end }

/-- Auxiliary construction for `coimage_iso_image` -/
def cokernel_iso {X Y : 𝒜} (f : X ⟶ Y) : begin
  haveI := has_cokernels a b i adj,
  exact b.obj (cokernel (a.map f)) ≅ cokernel f
end :=
begin
  haveI := has_cokernels a b i adj,
  -- We have to write an explicit `preserves_colimits` type here,
  -- as `left_adjoint_preserves_colimits` has universe variables.
  haveI : preserves_colimits b := adj.left_adjoint_preserves_colimits,
  calc b.obj (cokernel (a.map f))
      ≅ cokernel (b.map (a.map f)) : (as_iso (cokernel_comparison _ b)).symm
  ... ≅ cokernel (_ ≫ f ≫ _)       : cokernel_iso_of_eq (nat_iso.naturality_2 i f).symm
  ... ≅ cokernel (f ≫ _)           : cokernel_epi_comp _ _
  ... ≅ cokernel f                 : cokernel_comp_is_iso _ _
end

variables [preserves_finite_limits b]

/-- Auxiliary construction for `coimage_iso_image` -/
def coimage_iso_image_aux {X Y : 𝒜} (f : X ⟶ Y) : begin
  haveI := has_kernels a b i, haveI := has_cokernels a b i adj,
  exact kernel (b.map (cokernel.π (a.map f))) ≅ kernel (cokernel.π f)
end :=
begin
  haveI := has_kernels a b i, haveI := has_cokernels a b i adj,
  haveI : preserves_colimits b := adj.left_adjoint_preserves_colimits,
  calc kernel (b.map (cokernel.π (a.map f)))
      ≅ kernel (cokernel.π (b.map (a.map f)) ≫ cokernel_comparison (a.map f) b)
          : kernel_iso_of_eq (π_comp_cokernel_comparison _ _).symm
  ... ≅ kernel (cokernel.π (b.map (a.map f))) : kernel_comp_mono _ _
  ... ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernel_iso_of_eq _).hom)
          : kernel_iso_of_eq (π_comp_cokernel_iso_of_eq_hom (nat_iso.naturality_2 i f)).symm
  ... ≅ kernel (cokernel.π (_ ≫ f ≫ _))       : kernel_comp_mono _ _
  ... ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernel_epi_comp (i.hom.app X) _).inv)
          : kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_epi_comp_inv])
  ... ≅ kernel (cokernel.π (f ≫ _))           : kernel_comp_mono _ _
  ... ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernel_comp_is_iso f (i.inv.app Y)).inv)
          : kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_comp_is_iso_inv,
              iso.hom_inv_id_app_assoc, nat_iso.inv_inv_app])
  ... ≅ kernel (cokernel.π f ≫ _)             : kernel_is_iso_comp _ _
  ... ≅ kernel (cokernel.π f)                 : kernel_comp_mono _ _
end

variables [functor.preserves_zero_morphisms a]

/--
Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimage_iso_image {X Y : 𝒜} (f : X ⟶ Y) : begin
  haveI := has_kernels a b i, haveI := has_cokernels a b i adj,
  exact abelian.coimage f ≅ abelian.image f
end :=
begin
  haveI := has_kernels a b i, haveI := has_cokernels a b i adj,
  haveI : preserves_limits a := adj.right_adjoint_preserves_limits,
  haveI : preserves_colimits b := adj.left_adjoint_preserves_colimits,
  calc abelian.coimage f
      ≅ cokernel (kernel.ι f)                 : iso.refl _
  ... ≅ b.obj (cokernel (a.map (kernel.ι f))) : (cokernel_iso _ _ i adj _).symm
  ... ≅ b.obj (cokernel (kernel_comparison f a ≫ (kernel.ι (a.map f))))
                                              : b.map_iso (cokernel_iso_of_eq (by simp))
  ... ≅ b.obj (cokernel (kernel.ι (a.map f))) : b.map_iso (cokernel_epi_comp _ _)
  ... ≅ b.obj (abelian.coimage (a.map f))     : iso.refl _
  ... ≅ b.obj (abelian.image (a.map f))       : b.map_iso (abelian.coimage_iso_image _)
  ... ≅ b.obj (kernel (cokernel.π (a.map f))) : iso.refl _
  ... ≅ kernel (b.map (cokernel.π (a.map f))) : preserves_kernel.iso _ _
  ... ≅ kernel (cokernel.π f)                 : coimage_iso_image_aux a b i adj f
  ... ≅ abelian.image f                       : iso.refl _,
end

local attribute [simp] cokernel_iso coimage_iso_image coimage_iso_image_aux

-- The account of this proof in the Stacks project omits this calculation.
-- Happily it's little effort: our `[ext]` and `[simp]` lemmas only need a little guidance.
lemma coimage_iso_image_hom {X Y : 𝒜} (f : X ⟶ Y) :
begin
  haveI := has_kernels a b i, haveI := has_cokernels a b i adj,
  exact (coimage_iso_image a b i adj f).hom = abelian.coimage_image_comparison f,
end :=
by { ext, simpa [-functor.map_comp, ←b.map_comp_assoc] using nat_iso.naturality_1 i f, }

end abelian_of_adjunction

open abelian_of_adjunction

/--
If `𝒜` is an additive category, `ℬ` is an abelian category,
we have `a : 𝒜 ⥤ ℬ` `b : ℬ ⥤ 𝒜` (both preserving zero morphisms),
`b` is left exact (that is, preserves finite limits),
and further we have `adj : b ⊣ a` and `i : a ⋙ b ≅ 𝟭 𝒜`,
then `𝒜` is also abelian.

See https://stacks.math.columbia.edu/tag/03A3
-/
def abelian_of_adjunction
  {𝒜 : Type u₁} [category.{v} 𝒜] [preadditive 𝒜] [has_finite_products 𝒜]
  {ℬ : Type u₂} [category.{v} ℬ] [abelian ℬ]
  (a : 𝒜 ⥤ ℬ) [functor.preserves_zero_morphisms a]
  (b : ℬ ⥤ 𝒜) [functor.preserves_zero_morphisms b] [preserves_finite_limits b]
  (i : a ⋙ b ≅ 𝟭 𝒜) (adj : b ⊣ a) : abelian 𝒜 :=
begin
  haveI := has_kernels a b i, haveI := has_cokernels a b i adj,
  haveI : ∀ {X Y : 𝒜} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f),
  { intros X Y f, rw ←coimage_iso_image_hom a b i adj f, apply_instance, },
  apply abelian.of_coimage_image_comparison_is_iso,
end

end category_theory
