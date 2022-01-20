/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.additive_functor
import category_theory.linear

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

# Implementation details

`functor.linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/

namespace category_theory

variables (R : Type*) [semiring R]

/-- An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism. -/
class functor.linear {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] [linear R C] [linear R D] (F : C ⥤ D) [F.additive] : Prop :=
(map_smul' : Π {X Y : C} {f : X ⟶ Y} {r : R}, F.map (r • f) = r • F.map f . obviously)

section linear

namespace functor

section
variables {R} {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] [category_theory.linear R C] [category_theory.linear R D]
  (F : C ⥤ D) [additive F] [linear R F]

@[simp]
lemma map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
functor.linear.map_smul'

instance : linear R (𝟭 C) :=
{}

instance {E : Type*} [category E] [preadditive E] [category_theory.linear R E]
  (G : D ⥤ E) [additive G] [linear R G]:
  linear R (F ⋙ G) :=
{}

variables (R)

/-- `F.map_linear_map` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
def map_linear_map {X Y : C} : (X ⟶ Y) →ₗ[R] (F.obj X ⟶ F.obj Y) :=
{ map_smul' := λ r f, F.map_smul r f,
  ..F.map_add_hom }

lemma coe_map_linear_map {X Y : C} : ⇑(F.map_linear_map R : (X ⟶ Y) →ₗ[R] _) = @map C _ D _ F X Y :=
rfl

end

section induced_category
variables {C : Type*} {D : Type*} [category D] [preadditive D] [category_theory.linear R D]
   (F : C → D)

instance induced_functor_linear : functor.linear R (induced_functor F) := {}

end induced_category

section

variables {R} {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D]
  (F : C ⥤ D) [additive F]

instance nat_linear : F.linear ℕ :=
{ map_smul' := λ X Y f r, F.map_add_hom.map_nsmul f r, }

instance int_linear : F.linear ℤ :=
{ map_smul' := λ X Y f r, F.map_add_hom.map_zsmul f r, }

variables [category_theory.linear ℚ C] [category_theory.linear ℚ D]

instance rat_linear : F.linear ℚ :=
{ map_smul' := λ X Y f r, F.map_add_hom.to_rat_linear_map.map_smul r f, }

end

end functor

namespace equivalence

variables {C D : Type*} [category C] [category D]
  [preadditive C] [linear R C] [preadditive D] [linear R D]

instance inverse_linear (e : C ≌ D) [e.functor.additive] [e.functor.linear R] :
  e.inverse.linear R :=
{ map_smul' := λ X Y r f, by { apply e.functor.map_injective, simp, }, }

end equivalence

end linear

end category_theory
