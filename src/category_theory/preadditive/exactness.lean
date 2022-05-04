/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Markus Himmel
-/
import category_theory.limits.preserves.shapes.kernels
import category_theory.preadditive.functor_category
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.shapes.biproducts

universes u₁ u₂ v

--TODO trim imports

namespace category_theory

open limits

section
variables {C : Type*} [category C] [has_zero_morphisms C]
  (X Y : C) [has_binary_product X Y]

noncomputable def kernel_fork_of_prod_snd : kernel_fork (limits.prod.snd : limits.prod X Y ⟶ Y) :=
limits.kernel_fork.of_ι (prod.lift (𝟙 X) 0) (by simp)

noncomputable def is_limit_kernel_fork_of_prod_snd :
  is_limit (kernel_fork_of_prod_snd X Y) :=
kernel_fork.is_limit.of_ι _ _ (λ W' g hg, g ≫ limits.prod.fst)
  (λ W' g' hg', by tidy)
  (λ W' g' hg' m hm, by tidy)

end

namespace functor

variables {C : Type u₁} [category.{v} C] [preadditive C]
variables {D : Type u₂} [category.{v} D] [preadditive D]
variables (F : C ⥤ D) [functor.preserves_zero_morphisms F]
variables {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y) (i : is_limit (binary_fan.mk π₁ π₂))
variables [preserves_limit (parallel_pair π₂ 0) F]

def is_limit_map_cone_of_preserves_kernels : is_limit (F.map_cone (binary_fan.mk π₁ π₂)) :=
let bc := binary_bicone.of_limit_cone i in
let ibc := bicone_is_bilimit_of_limit_cone_of_is_limit i in
begin
  haveI : preserves_limit (parallel_pair bc.snd 0) F, simpa,
  let i_f : is_limit bc.snd_kernel_fork := binary_bicone.is_limit_snd_kernel_fork i,
  let i_Ff := is_limit_of_preserves F i_f,
  let cf'' := map_cocone F bc.inl_cokernel_cofork,
  let cf : cokernel_cofork (F.map bc.inl) := cokernel_cofork.of_π (F.map bc.snd) (by sorry),
  let icf : is_colimit cf := sorry,
  let h8 := (is_bilimit_binary_bicone_of_split_mono_of_cokernel icf).is_limit,
  sorry
end

end functor

end category_theory
