/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer
-/
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.limits.preserves.shapes.kernels
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.preadditive.additive_functor

/-!
# Left exactness of functors between preadditive categories

We show that a functor is left exact in the sense that it preserves finite limits, if it
preserves kernels. The dual result holds for right exact functors and cokernels.
## Main results
* We first derive preservation of binary product in the lemma
  `preserves_binary_products_of_preserves_kernels`,
* then show the preservation of equalizers in `preserves_equalizer_of_preserves_kernels`,
* and then derive the preservation of all finite limits with the usual construction.

-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.preadditive

namespace category_theory

namespace functor

variables {C : Type u₁} [category.{v₁} C] [preadditive C]
  {D : Type u₂} [category.{v₂} D] [preadditive D]
  (F : C ⥤ D) [preserves_zero_morphisms F]

section finite_limits

/--
A functor between preadditive categories which preserves kernels preserves that an
arbitrary binary fan is a limit.
-/
def is_limit_map_cone_binary_fan_of_preserves_kernels {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y)
  [preserves_limit (parallel_pair π₂ 0) F] (i : is_limit (binary_fan.mk π₁ π₂)) :
  is_limit (F.map_cone (binary_fan.mk π₁ π₂)) :=
begin
  let bc := binary_bicone.of_limit_cone i,
  letI presf : preserves_limit (parallel_pair bc.snd 0) F, { simpa },
  let hf : is_limit bc.snd_kernel_fork := binary_bicone.is_limit_snd_kernel_fork i,
  exact (is_limit_map_cone_binary_fan_equiv F π₁ π₂).inv_fun
    (binary_bicone.is_bilimit_of_kernel_inl (F.map_binary_bicone bc)
      (is_limit_map_cone_fork_equiv' F _ (is_limit_of_preserves F hf))).is_limit
end

/-- A kernel preserving functor between preadditive categories preserves any pair being a limit. -/
def preserves_binary_product_of_preserves_kernels
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] {X Y : C} :
  preserves_limit (pair X Y) F :=
{ preserves := λ c hc, is_limit.of_iso_limit
    (is_limit_map_cone_binary_fan_of_preserves_kernels F _ _
      (is_limit.of_iso_limit hc (iso_binary_fan_mk c)))
    ((cones.functoriality _ F).map_iso (iso_binary_fan_mk c).symm) }

local attribute [instance] preserves_binary_product_of_preserves_kernels

/-- A kernel preserving functor between preadditive categories preserves binary products. -/
def preserves_binary_products_of_preserves_kernels
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] :
  preserves_limits_of_shape (discrete walking_pair) F :=
{ preserves_limit := λ p, preserves_limit_of_iso_diagram F (diagram_iso_pair p).symm }

local attribute [instance] preserves_binary_products_of_preserves_kernels

variables  [has_binary_biproducts C]

/--
A functor between preadditive categories preserves the equalizer of two
morphisms if it preserves all kernels. -/
def preserves_equalizer_of_preserves_kernels
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] {X Y : C}
  (f g : X ⟶ Y) : preserves_limit (parallel_pair f g) F :=
begin
  letI := preserves_binary_biproducts_of_preserves_binary_products F,
  haveI := additive_of_preserves_binary_biproducts F,
  constructor, intros c i,
  let c' := is_limit_kernel_fork_of_fork (i.of_iso_limit (fork.iso_fork_of_ι c)),
  dsimp only [kernel_fork_of_fork_of_ι] at c',
  let iFc := is_limit_fork_map_of_is_limit' F _ c',
  apply is_limit.of_iso_limit _ ((cones.functoriality _ F).map_iso (fork.iso_fork_of_ι c).symm),
  apply (is_limit_map_cone_fork_equiv F (fork.condition c)).inv_fun,
  let p : parallel_pair (F.map (f - g)) 0 ≅ parallel_pair (F.map f - F.map g) 0 :=
    parallel_pair.eq_of_hom_eq F.map_sub rfl,
  refine is_limit.of_iso_limit (is_limit_fork_of_kernel_fork
    ((is_limit.postcompose_hom_equiv p _).symm iFc)) _,
  convert fork.iso_fork_of_ι _,
  rw [fork_of_kernel_fork_ι, fork.ι_postcompose, kernel_fork.ι_of_ι,
    parallel_pair.eq_of_hom_eq_hom_app],
  erw category.comp_id
end

/--
A functor between preadditive categories preserves all equalizers if it preserves all kernels.
-/
def preserves_equalizers_of_preserves_kernels
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] :
  preserves_limits_of_shape walking_parallel_pair F :=
{ preserves_limit := λ K,
  begin
    letI := preserves_equalizer_of_preserves_kernels F
      (K.map walking_parallel_pair_hom.left) (K.map walking_parallel_pair_hom.right),
    apply preserves_limit_of_iso_diagram F (diagram_iso_parallel_pair K).symm,
  end }

/--
A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preserves_finite_limits_of_preserves_kernels
  [has_finite_products C] [has_equalizers C] [has_zero_object C] [has_zero_object D]
  [∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F] : preserves_finite_limits F :=
begin
  letI := preserves_equalizers_of_preserves_kernels F,
  letI := preserves_terminal_object_of_preserves_zero_morphisms F,
  letI := preserves_limits_of_shape_pempty_of_preserves_terminal F,
  letI p_prod := preserves_finite_products_of_preserves_binary_and_terminal F,
  apply @preserves_finite_limits_of_preserves_equalizers_and_finite_products _ _
    _ _ _ _ _ _ @p_prod,
end

end finite_limits

section finite_colimits

/--
A functor between preadditive categories which preserves cokernels preserves finite coproducts.
-/
def is_colimit_map_cocone_binary_cofan_of_preserves_cokernels {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
  [preserves_colimit (parallel_pair ι₂ 0) F] (i : is_colimit (binary_cofan.mk ι₁ ι₂)) :
  is_colimit (F.map_cocone (binary_cofan.mk ι₁ ι₂)) :=
begin
  let bc := binary_bicone.of_colimit_cocone i,
  letI presf : preserves_colimit (parallel_pair bc.inr 0) F, { simpa },
  let hf : is_colimit bc.inr_cokernel_cofork := binary_bicone.is_colimit_inr_cokernel_cofork i,
  exact (is_colimit_map_cocone_binary_cofan_equiv F ι₁ ι₂).inv_fun
    (binary_bicone.is_bilimit_of_cokernel_fst (F.map_binary_bicone bc)
      (is_colimit_map_cocone_cofork_equiv' F _ (is_colimit_of_preserves F hf))).is_colimit
end

/-- A cokernel preserving functor between preadditive categories preserves any pair being
a colimit. -/
def preserves_coproduct_of_preserves_cokernels
  [∀ {X Y} (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) F] {X Y : C} :
  preserves_colimit (pair X Y) F :=
{ preserves := λ c hc, is_colimit.of_iso_colimit
    (is_colimit_map_cocone_binary_cofan_of_preserves_cokernels F _ _
      (is_colimit.of_iso_colimit hc (iso_binary_cofan_mk c)))
    ((cocones.functoriality _ F).map_iso (iso_binary_cofan_mk c).symm) }

local attribute [instance] preserves_coproduct_of_preserves_cokernels

/-- A cokernel preserving functor between preadditive categories preserves binary coproducts. -/
def preserves_binary_coproducts_of_preserves_cokernels
  [∀ {X Y} (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) F] :
  preserves_colimits_of_shape (discrete walking_pair) F :=
{ preserves_colimit := λ p, preserves_colimit_of_iso_diagram F (diagram_iso_pair p).symm }

local attribute [instance] preserves_binary_coproducts_of_preserves_cokernels

variables [has_binary_biproducts C]

/--
A functor between preadditive categoris preserves the coequalizer of two
morphisms if it preserves all cokernels. -/
def preserves_coequalizer_of_preserves_cokernels
  [∀ {X Y} (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) F] {X Y : C}
  (f g : X ⟶ Y) : preserves_colimit (parallel_pair f g) F :=
begin
  letI := preserves_binary_biproducts_of_preserves_binary_coproducts F,
  haveI := additive_of_preserves_binary_biproducts F,
  constructor, intros c i,
  let c' := is_colimit_cokernel_cofork_of_cofork (i.of_iso_colimit (cofork.iso_cofork_of_π c)),
  dsimp only [cokernel_cofork_of_cofork_of_π] at c',
  let iFc := is_colimit_cofork_map_of_is_colimit' F _ c',
  apply is_colimit.of_iso_colimit _
    ((cocones.functoriality _ F).map_iso (cofork.iso_cofork_of_π c).symm),
  apply (is_colimit_map_cocone_cofork_equiv F (cofork.condition c)).inv_fun,
  let p : parallel_pair (F.map (f - g)) 0 ≅ parallel_pair (F.map f - F.map g) 0,
  { exact parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp) },
  refine is_colimit.of_iso_colimit (is_colimit_cofork_of_cokernel_cofork
    ((is_colimit.precompose_hom_equiv p.symm _).symm iFc)) _,
  convert cofork.iso_cofork_of_π _,
  rw [cofork_of_cokernel_cofork_π, cofork.π_precompose, cokernel_cofork.π_of_π,
    iso.symm_hom, parallel_pair.ext_inv_app, iso.refl_inv],
  erw category.id_comp
end

/--
A functor between preadditive categories preserves all coequalizers if it preserves all kernels.
-/
def preserves_coequalizers_of_preserves_cokernels
  [∀ {X Y} (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) F] :
  preserves_colimits_of_shape walking_parallel_pair F :=
{ preserves_colimit := λ K,
  begin
    letI := preserves_coequalizer_of_preserves_cokernels F
      (K.map limits.walking_parallel_pair_hom.left)
      (K.map limits.walking_parallel_pair_hom.right),
    apply preserves_colimit_of_iso_diagram F (diagram_iso_parallel_pair K).symm,
  end }

/--
A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preserves_finite_colimits_of_preserves_cokernels
  [has_finite_coproducts C] [has_coequalizers C] [has_zero_object C] [has_zero_object D]
  [∀ {X Y} (f : X ⟶ Y), preserves_colimit (parallel_pair f 0) F] : preserves_finite_colimits F :=
begin
  letI := preserves_coequalizers_of_preserves_cokernels F,
  letI := preserves_initial_object_of_preserves_zero_morphisms F,
  letI := preserves_colimits_of_shape_pempty_of_preserves_initial F,
  letI p_prod := preserves_finite_coproducts_of_preserves_binary_and_initial F,
  apply @preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts C _
    _ _ _ _ _ _ @p_prod,
end

end finite_colimits

end functor

end category_theory
