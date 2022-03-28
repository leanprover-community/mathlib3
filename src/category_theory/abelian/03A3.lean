
import category_theory.abelian.basic

noncomputable theory

open category_theory
open category_theory.limits

universes v u₁ u₂

variables {𝒜 : Type u₁} [category.{v} 𝒜] [preadditive 𝒜] [has_finite_products 𝒜]
variables {A₁ A₂ : 𝒜} (ψ : A₁ ⟶ A₂)

variables {ℬ : Type u₂} [category.{v} ℬ] [abelian ℬ]
variables (a : 𝒜 ⥤ ℬ) (b : ℬ ⥤ 𝒜) (adj : b ⊣ a) (i : a ⋙ b ≅ 𝟭 𝒜)
variables [functor.preserves_zero_morphisms a]

instance {B₁ B₂ : ℬ} (φ : B₁ ⟶ B₂) : has_kernel (b.map φ) := sorry
instance {B₁ B₂ : ℬ} (φ : B₁ ⟶ B₂) : has_cokernel (b.map φ) := sorry

include i

instance xx : has_kernels 𝒜 :=
{ has_limit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_kernel (b.map (a.map f) ≫ i.hom.app _),
    apply limits.has_kernel_comp_mono,
    apply limits.has_kernel_iso_comp,
  end }

instance yy : has_cokernels 𝒜 :=
{ has_colimit := λ X Y f, begin
    have := nat_iso.naturality_1 i f,
    simp at this,
    rw ←this,
    haveI : has_cokernel (b.map (a.map f) ≫ i.hom.app _),
    apply limits.has_cokernel_comp_iso,
    apply limits.has_cokernel_epi_comp,
  end }

-- local attribute [-instance] limits.comp_preserves_limit limits.comp_preserves_limits limits.comp_preserves_limits_of_shape
-- local attribute [-instance] limits.comp_preserves_colimit limits.comp_preserves_colimits limits.comp_preserves_colimits_of_shape
-- local attribute [-instance] full.to_ess_image full_subcategory.lift.full

-- #check full.to_ess_image
-- set_option trace.class_instances true
-- set_option class.instance_max_depth 500
def zz {X Y : 𝒜} (f : X ⟶ Y) : begin
  haveI := xx a b i,
  haveI := yy a b i,
  exact abelian.coimage f ≅ abelian.image f
end :=
begin
  haveI := xx a b i,
  haveI := yy a b i,
  have : kernel_comparison f a ≫ (kernel.ι (a.map f)) = a.map (kernel.ι f) := sorry,
  -- calc abelian.coimage f
  --     ≅ cokernel (kernel.ι f) : iso.refl _
  -- ... ≅ b.obj (cokernel (a.map (kernel.ι f))) : sorry
  -- ... ≅ b.obj (cokernel (kernel_comparison f a ≫ (kernel.ι (a.map f)))) : sorry
  -- ... ≅ b.obj (cokernel (kernel.ι (a.map f))) : sorry
  -- ... ≅ b.obj (abelian.coimage (a.map f)) : iso.refl _
  -- ... ≅ b.obj (abelian.image (a.map f)) : b.map_iso (abelian.coimage_iso_image _)
  -- ... ≅ b.obj (kernel (cokernel.π (a.map f))) : iso.refl _
  -- ... ≅ kernel (b.map (cokernel.π (a.map f))) : sorry
  -- ... ≅ kernel (cokernel.π f) : sorry
  -- ... ≅ abelian.image f : iso.refl _,
end

lemma zz_hom {X Y : 𝒜} (f : X ⟶ Y) :
begin
  haveI := xx a b i,
  haveI := yy a b i,
  exact (zz a b i f).hom = abelian.coimage_image_comparison f,
end :=
sorry

lemma stacks_03A3 : abelian 𝒜 :=
begin
  haveI := xx a b i,
  haveI := yy a b i,
  haveI : ∀ {X Y : 𝒜} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f),
  { intros X Y f, rw ←zz_hom a b i f, apply_instance, },
  fapply abelian.of_coimage_image_comparison_is_iso,
end
