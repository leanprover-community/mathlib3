/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.monoidal.functor
import category_theory.monoidal.braided
import category_theory.monoidal.transport
import category_theory.skeletal

/-!
# The monoid on the skeleton of a monoidal category

The skeleton of a monoidal category is a monoid.
-/

namespace category_theory
open monoidal_category

universes v u

variables {C : Type u} [category.{v} C] [monoidal_category C]

/-- If `C` is monoidal and skeletal, it is a monoid.
See note [reducible non-instances]. -/
@[reducible]
def monoid_of_skeletal_monoidal (hC : skeletal C) : monoid C :=
{ mul := λ X Y, (X ⊗ Y : C),
  one := (𝟙_ C : C),
  one_mul := λ X, hC ⟨λ_ X⟩,
  mul_one := λ X, hC ⟨ρ_ X⟩,
  mul_assoc := λ X Y Z, hC ⟨α_ X Y Z⟩ }

/-- If `C` is braided and skeletal, it is a commutative monoid. -/
def comm_monoid_of_skeletal_braided [braided_category C] (hC : skeletal C) :
  comm_monoid C :=
{ mul_comm := λ X Y, hC ⟨β_ X Y⟩,
  ..monoid_of_skeletal_monoidal hC }

/--
The skeleton of a monoidal category has a monoidal structure itself, induced by the equivalence.
-/
noncomputable instance : monoidal_category (skeleton C) :=
monoidal.transport (skeleton_equivalence C).symm

/--
The skeleton of a monoidal category can be viewed as a monoid, where the multiplication is given by
the tensor product, and satisfies the monoid axioms since it is a skeleton.
-/
noncomputable instance : monoid (skeleton C) :=
monoid_of_skeletal_monoidal (skeleton_is_skeleton _).skel

-- TODO: Transfer the braided structure to the skeleton of C along the equivalence, and show that
-- the skeleton is a commutative monoid.

end category_theory
