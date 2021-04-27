/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homology
import algebra.homology.homotopy
import category_theory.quotient

/-!
# The homotopy category

`homotopy_category V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_object V] [preadditive V]
variables (c : complex_shape ι)

/--
`homotopy_category V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/
@[derive category]
def homotopy_category :=
category_theory.quotient (λ (C D : homological_complex V c) (f g : C ⟶ D), nonempty (homotopy f g))

namespace homotopy_category

/-- The quotient functor from complexes to the homotopy category. -/
def quotient : homological_complex V c ⥤ homotopy_category V c := category_theory.quotient.functor _

variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]

/-- The `i`-th homology, as a functor from the homotopy category. -/
def homology_functor (i : ι) : homotopy_category V c ⥤ V :=
category_theory.quotient.lift _ (homology_functor V c i)
  (λ C D f g ⟨h⟩, homology_map_eq_of_homotopy h i)

/-- The homology functor on the homotopy category is just the usual homology functor. -/
def homology_factors (i : ι) :
  quotient V c ⋙ homology_functor V c i ≅ _root_.homology_functor V c i :=
category_theory.quotient.lift.is_lift _ _ _

@[simp] lemma homology_factors_hom_app (i : ι) (C : homological_complex V c) :
  (homology_factors V c i).hom.app C = 𝟙 _ :=
rfl

@[simp] lemma homology_factors_inv_app (i : ι) (C : homological_complex V c) :
  (homology_factors V c i).inv.app C = 𝟙 _ :=
rfl

end homotopy_category
