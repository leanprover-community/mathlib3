/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.image_to_kernel_map

universes v u

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables [has_kernels V] [has_equalizers V] [has_images V]

namespace category_theory
section exact

/-- Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `f ≫ g = 0` and the natural map
    `image f ⟶ kernel g` is an epimorphism. -/
class exact {A B C : V} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
(w : f ≫ g = 0)
(epi : epi (image_to_kernel_map f g w))

attribute [instance] exact.epi

end exact

end category_theory
