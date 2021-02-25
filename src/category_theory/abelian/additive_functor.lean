/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import category_theory.preadditive
import category_theory.abelian.basic

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian
groups.

# Projects (in the case of abelian categories):

- Prove that an additive functor preserves finite biproducts
- Prove that a functor is additive if it preserves finite biproducts
-/

namespace category_theory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class functor.additive {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] (F : C ⥤ D) : Prop :=
(map_zero' : Π {X Y : C}, F.map (0 : X ⟶ Y) = 0 . obviously)
(map_add' : Π {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g . obviously)

restate_axiom functor.additive.map_zero'
restate_axiom functor.additive.map_add'

attribute [simp] functor.additive.map_zero functor.additive.map_add

section preadditive

variables {C D : Type*} [category C] [category D] [preadditive C]
  [preadditive D] (F : C ⥤ D) [functor.additive F]

namespace functor

/-- `F.add_map` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps]
def map_add_hom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
{ to_fun := λ f, F.map f,
  map_zero' := additive.map_zero,
  map_add' := λ _ _, additive.map_add }

lemma coe_map_add_hom {X Y : C} : ⇑(F.map_add_hom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y := rfl

@[simp]
lemma additive.map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = - F.map f :=
F.map_add_hom.map_neg _

@[simp]
lemma additive.map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
F.map_add_hom.map_sub _ _

end functor
end preadditive

end category_theory
