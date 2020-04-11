/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.epi_mono
import category_theory.limits.shapes.kernels

/-!
# Definitions and basic properties of regular and normal monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.
A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the constructions
* `split_mono → regular_mono`
* `normal_mono → regular_mono`, and
* `regular_mono → mono`.
-/

namespace category_theory
open category_theory.limits

universes v₁ u₁

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

variables {X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class regular_mono (f : X ⟶ Y) :=
(Z : C)
(left right : Y ⟶ Z)
(w : f ≫ left = f ≫ right)
(is_limit : is_limit (fork.of_ι f w))

/-- Every regular monomorphism is a monomorphism. -/
@[priority 100]
instance regular_mono.mono (f : X ⟶ Y) [regular_mono f] : mono f :=
mono_of_is_limit_parallel_pair regular_mono.is_limit

/-- Every split monomorphism is a regular monomorphism. -/
@[priority 100]
instance regular_mono.of_split_mono (f : X ⟶ Y) [split_mono f] : regular_mono f :=
{ Z     := Y,
  left  := 𝟙 Y,
  right := retraction f ≫ f,
  w     := by tidy,
  is_limit := split_mono_equalizes f }

section
variables [has_zero_morphisms.{v₁} C]
/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class normal_mono (f : X ⟶ Y) :=
(Z : C)
(g : Y ⟶ Z)
(w : f ≫ g = 0)
(is_limit : is_limit (kernel_fork.of_ι f w))

/-- Every normal monomorphism is a regular monomorphism. -/
@[priority 100]
instance normal_mono.regular_mono (f : X ⟶ Y) [I : normal_mono f] : regular_mono f :=
{ left := I.g,
  right := 0,
  w := (by simpa using I.w),
  ..I }
end

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class regular_epi (f : X ⟶ Y) :=
(W : C)
(left right : W ⟶ X)
(w : left ≫ f = right ≫ f)
(is_colimit : is_colimit (cofork.of_π f w))

/-- Every regular epimorphism is an epimorphism. -/
@[priority 100]
instance regular_epi.epi (f : X ⟶ Y) [regular_epi f] : epi f :=
epi_of_is_colimit_parallel_pair regular_epi.is_colimit

/-- Every split epimorphism is a regular epimorphism. -/
@[priority 100]
instance regular_epi.of_split_epi (f : X ⟶ Y) [split_epi f] : regular_epi f :=
{ W     := X,
  left  := 𝟙 X,
  right := f ≫ section_ f,
  w     := by tidy,
  is_colimit := split_epi_coequalizes f }


section
variables [has_zero_morphisms.{v₁} C]
/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class normal_epi (f : X ⟶ Y) :=
(W : C)
(g : W ⟶ X)
(w : g ≫ f = 0)
(is_colimit : is_colimit (cokernel_cofork.of_π f w))

/-- Every normal epimorphism is a regular epimorphism. -/
@[priority 100]
instance normal_epi.regular_epi (f : X ⟶ Y) [I : normal_epi f] : regular_epi f :=
{ left := I.g,
  right := 0,
  w := (by simpa using I.w),
  ..I }
end

end category_theory
