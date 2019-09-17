/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.equalizers

universes v u

open category_theory

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C] [has_zero_morphisms.{v} C]
include 𝒞

variables {X Y : C} (f : X ⟶ Y)

section
variables [has_limit (parallel_pair f 0)]

abbreviation kernel : C := equalizer f 0

abbreviation kernel.ι : kernel f ⟶ X := equalizer.ι f 0

@[simp, reassoc] lemma kernel.condition : kernel.ι f ≫ f = 0 :=
by simp [equalizer.condition]

abbreviation kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
limit.lift (parallel_pair f 0) (fork.of_ι k (by simpa))
end

section
variables [has_colimit (parallel_pair f 0)]

abbreviation cokernel : C := coequalizer f 0

abbreviation cokernel.π : Y ⟶ cokernel f := coequalizer.π f 0

@[simp, reassoc] lemma cokernel.condition : f ≫ cokernel.π f = 0 :=
by simp [coequalizer.condition]

abbreviation cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
colimit.desc (parallel_pair f 0) (cofork.of_π k (by simpa))
end

variables (C)

class has_kernels :=
(has_limit : Π {X Y : C}, has_limit (parallel_pair f 0))
class has_cokernels :=
(has_colimit : Π {X Y : C}, has_colimit (parallel_pair f 0))

attribute [instance] has_equalizers.has_limits_of_shape has_coequalizers.has_colimits_of_shape

end category_theory.limits
