/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.equalizers

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is just the equalizer of `f`
and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

We don't yet prove much here, just provide
* `kernel : (X ⟶ Y) → C`
* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts,
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism

## Future work
* TODO: images and coimages, and then abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

universes v u

open category_theory
open category_theory.limits.walking_parallel_pair

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables {X Y : C} (f : X ⟶ Y)

section
variables [has_zero_morphisms.{v} C] [has_limit (parallel_pair f 0)]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
abbreviation kernel : C := equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
abbreviation kernel.ι : kernel f ⟶ X := equalizer.ι f 0

@[simp, reassoc] lemma kernel.condition : kernel.ι f ≫ f = 0 :=
by simp [equalizer.condition]

/-- Given any morphism `k` so `k ≫ f = 0`, `k` factors through `kernel f`. -/
abbreviation kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
limit.lift (parallel_pair f 0) (fork.of_ι k (by simpa))

/-- Every kernel of the zero morphism is an isomorphism -/
def kernel.ι_zero_is_iso [has_limit (parallel_pair (0 : X ⟶ Y) 0)] :
  is_iso (kernel.ι (0 : X ⟶ Y)) :=
by { apply limit_cone_parallel_pair_self_is_iso, apply limit.is_limit }

end

section
variables [has_zero_object.{v} C]

local attribute [instance] zero_of_zero_object
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zero_cone : cone (parallel_pair f 0) :=
{ X := 0,
  π := { app := λ j, 0 }}

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.is_limit_cone_zero_cone [mono f] : is_limit (kernel.zero_cone f) :=
{ lift := λ s, 0,
  fac' := λ s j,
  begin
    cases j,
    { erw has_zero_morphisms.zero_comp,
      convert (@zero_of_comp_mono _ _ _ _ _ _ _ f _ _).symm,
      erw fork.condition,
      convert has_zero_morphisms.comp_zero.{v} _ (s.π.app zero) _ },
    { rw ←cone_parallel_pair_right s,
      simp only [has_zero_morphisms.zero_comp],
      convert (has_zero_morphisms.comp_zero.{v} _
        (s.π.app zero) _).symm },
  end,
  uniq' := λ _ m _, has_zero_object.zero_of_to_zero m }

end

section
variables [has_zero_morphisms.{v} C] [has_colimit (parallel_pair f 0)]

/-- The cokernel of a morphism, expressed as the coekernel.is_limit_cone_zero_conequalizer with the 0 morphism. -/
abbreviation cokernel : C := coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
abbreviation cokernel.π : Y ⟶ cokernel f := coequalizer.π f 0

@[simp, reassoc] lemma cokernel.condition : f ≫ cokernel.π f = 0 :=
by simp [coequalizer.condition]

/-- Given any morphism `k` so `f ≫ k = 0`, `k` factors through `cokernel f`. -/
abbreviation cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
colimit.desc (parallel_pair f 0) (cofork.of_π k (by simpa))
end

end category_theory.limits
namespace category_theory.limits
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variables [has_zero_morphisms.{v} C]

/-- `has_kernels` represents a choice of kernel for every morphism -/
class has_kernels :=
(has_limit : Π {X Y : C} (f : X ⟶ Y), has_limit (parallel_pair f 0))

/-- `has_cokernels` represents a choice of cokernel for every morphism -/
class has_cokernels :=
(has_colimit : Π {X Y : C} (f : X ⟶ Y), has_colimit (parallel_pair f 0))

end category_theory.limits
