
import category_theory.preadditive.additive_functor
import category_theory.abelian.basic
import category_theory.limits.preserves.shapes.kernels

noncomputable theory

open category_theory
open category_theory.limits

universes v u₁ u₂

variables {𝒜 : Type u₁} [category.{v} 𝒜] [preadditive 𝒜] [has_finite_products 𝒜]
variables {A₁ A₂ : 𝒜} (ψ : A₁ ⟶ A₂)

variables {ℬ : Type u₂} [category.{v} ℬ] [abelian ℬ]
variables (a : 𝒜 ⥤ ℬ) [functor.additive a]
variables (b : ℬ ⥤ 𝒜) [functor.additive b] [preserves_finite_limits b]
variables (adj : b ⊣ a) (i : a ⋙ b ≅ 𝟭 𝒜) -- Is this really enough? I'm suprised we don't need that `i` is the counit.

instance {B₁ B₂ : ℬ} (φ : B₁ ⟶ B₂) : has_kernel (b.map φ) := sorry
instance {B₁ B₂ : ℬ} (φ : B₁ ⟶ B₂) : has_cokernel (b.map φ) := sorry

include i

/-- No point making this an instance, as it requires `i`. -/
def xx : has_kernels 𝒜 :=
{ has_limit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_kernel (b.map (a.map f) ≫ i.hom.app _) := limits.has_kernel_comp_mono _ _,
    apply limits.has_kernel_iso_comp,
  end }

/-- No point making this an instance, as it requires `i`. -/
def yy : has_cokernels 𝒜 :=
{ has_colimit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_cokernel (b.map (a.map f) ≫ i.hom.app _) := limits.has_cokernel_comp_iso _ _,
    apply limits.has_cokernel_epi_comp,
  end }

@[simps]
def zz {X Y : 𝒜} (f : X ⟶ Y) : begin
  haveI := xx a b i, haveI := yy a b i,
  exact abelian.coimage f ≅ abelian.image f
end :=
begin
  haveI := xx a b i, haveI := yy a b i,
  haveI : is_iso (kernel_comparison f a) := sorry,
  calc abelian.coimage f
      ≅ cokernel (kernel.ι f)                 : iso.refl _
  ... ≅ b.obj (cokernel (a.map (kernel.ι f))) : sorry
  ... ≅ b.obj (cokernel (kernel_comparison f a ≫ (kernel.ι (a.map f))))
                                              : b.map_iso (cokernel_iso_of_eq (by simp))
  ... ≅ b.obj (cokernel (kernel.ι (a.map f))) : b.map_iso (cokernel_epi_comp _ _)
  ... ≅ b.obj (abelian.coimage (a.map f))     : iso.refl _
  ... ≅ b.obj (abelian.image (a.map f))       : b.map_iso (abelian.coimage_iso_image _)
  ... ≅ b.obj (kernel (cokernel.π (a.map f))) : iso.refl _
  ... ≅ kernel (b.map (cokernel.π (a.map f))) : preserves_kernel.iso _ _
  ... ≅ kernel (cokernel.π f)                 : sorry
  ... ≅ abelian.image f                       : iso.refl _,
end

-- The account of this proof in the Stacks project omits this calculation.
lemma zz_hom' {X Y : 𝒜} (f : X ⟶ Y) :
begin
  haveI := xx a b i, haveI := yy a b i,
  exact (zz a b i f).hom = abelian.coimage_image_comparison f,
end :=
by { ext, simp, sorry, }

lemma stacks_03A3 : abelian 𝒜 :=
begin
  haveI := xx a b i, haveI := yy a b i,
  haveI : ∀ {X Y : 𝒜} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f),
  { intros X Y f, rw ←zz_hom' a b i f, apply_instance, },
  apply abelian.of_coimage_image_comparison_is_iso,
end
