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
for every two objects `X` and `Y`, there exists a morphism of additive
groups `f : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` whose underlying function
agrees with `F.map`.

To construct an instance of `functor.additive G` from proofs that
`G.map` sends `0` to `0` and is compatible with addition of morphisms,
use `functor.additive.of_is_hom`.

# Projects (in the case of abelian categories):

- Prove that an additive functor preserves finite biproducts
- Prove that a functor is additive it it preserves finite biproducts
-/

namespace category_theory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class functor.additive {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] (F : C ⥤ D) : Prop :=
(exists_hom' : ∀ (X Y : C), ∃ f : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y),
  ∀ g : X ⟶ Y, F.map g = f g)

section preadditive
variables {C D : Type*} [category C] [category D] [preadditive C]
  [preadditive D] (F : C ⥤ D) [functor.additive F]

namespace functor.additive

lemma exists_hom (X Y : C) : ∃ f : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y),
  ∀ g : X ⟶ Y, F.map g = f g := functor.additive.exists_hom' _ _

/--
Construct an additive instance for `G` from proofs that `G.map` sends `0` to `0`
and is compatible with addition of morphisms.
-/
lemma of_is_hom (G : C ⥤ D)
  (map_zero : ∀ X Y : C, G.map (0 : X ⟶ Y) = 0)
  (map_add : ∀ (X Y : C) (f g : X ⟶ Y), G.map (f + g) = G.map f + G.map g) :
  functor.additive G := functor.additive.mk $ λ X Y,
⟨⟨λ f, G.map f, map_zero _ _, map_add _ _⟩, λ g, rfl⟩

end functor.additive

namespace functor

/-- `F.add_map` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps]
def add_map {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
{ to_fun := λ f, F.map f,
  map_zero' := begin
    rcases functor.additive.exists_hom F X Y with ⟨f, hf⟩,
    simp [hf],
  end,
  map_add' := begin
    rcases functor.additive.exists_hom F X Y with ⟨f, hf⟩,
    simp [hf],
  end }

lemma add_map_spec {X Y : C} {f : X ⟶ Y} : F.add_map f = F.map f := rfl

@[simp]
lemma map_zero {X Y : C} : F.map (0 : X ⟶ Y) = 0 := F.add_map.map_zero

@[simp]
lemma map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
F.add_map.map_add _ _

@[simp]
lemma map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = - F.map f :=
F.add_map.map_neg _

@[simp]
lemma map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
F.add_map.map_sub _ _

end functor
end preadditive

end category_theory
