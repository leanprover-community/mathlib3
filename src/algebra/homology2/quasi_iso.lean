import algebra.homology2.homology

open category_theory
open category_theory.limits

universes v u

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V] [has_zero_object V]
variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]
variables {c : complex_shape ι} {C D : homological_complex V c}

class quasi_iso (f : C ⟶ D) :=
(is_iso := ∀ i, is_iso ((homology_functor V c i).map f))
