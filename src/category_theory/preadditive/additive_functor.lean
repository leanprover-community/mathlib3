/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import category_theory.preadditive
import category_theory.limits.shapes.biproducts

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian
groups.

# Project (in the case of abelian categories):

- Prove that a functor is additive if it preserves finite biproducts
-/

namespace category_theory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class functor.additive {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] (F : C ⥤ D) : Prop :=
(map_zero' : Π {X Y : C}, F.map (0 : X ⟶ Y) = 0 . obviously)
(map_add' : Π {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g . obviously)

section preadditive

namespace functor

section
variables {C D : Type*} [category C] [category D] [preadditive C]
  [preadditive D] (F : C ⥤ D) [functor.additive F]

@[simp]
lemma map_zero {X Y : C} : F.map (0 : X ⟶ Y) = 0 :=
functor.additive.map_zero'

@[simp]
lemma map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
functor.additive.map_add'

instance : additive (𝟭 C) :=
{}

instance {E : Type*} [category E] [preadditive E] (G : D ⥤ E) [functor.additive G] :
  additive (F ⋙ G) :=
{}

/-- `F.map_add_hom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps]
def map_add_hom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
{ to_fun := λ f, F.map f,
  map_zero' := F.map_zero,
  map_add' := λ _ _, F.map_add }

lemma coe_map_add_hom {X Y : C} : ⇑(F.map_add_hom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y := rfl

@[simp]
lemma map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = - F.map f :=
F.map_add_hom.map_neg _

@[simp]
lemma map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
F.map_add_hom.map_sub _ _

open_locale big_operators

@[simp]
lemma map_sum {X Y : C} {α : Type*} (f : α → (X ⟶ Y)) (s : finset α) :
  F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
(F.map_add_hom : (X ⟶ Y) →+ _).map_sum f s

end

section
-- To talk about preservation of biproducts we need to specify universes explicitly.

noncomputable theory
universes v u₁ u₂

variables {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D]
  [preadditive C] [preadditive D] (F : C ⥤ D) [functor.additive F]

open category_theory.limits

/--
An additive functor between preadditive categories creates finite biproducts.
-/
instance map_has_biproduct {J : Type v} [fintype J] [decidable_eq J] (f : J → C) [has_biproduct f] :
  has_biproduct (λ j, F.obj (f j)) :=
has_biproduct_of_total
{ X := F.obj (⨁ f),
  π := λ j, F.map (biproduct.π f j),
  ι := λ j, F.map (biproduct.ι f j),
  ι_π := λ j j', by { simp only [←F.map_comp], split_ifs, { subst h, simp, }, { simp [h], }, }, }
begin
  dsimp,
  simp_rw [←F.map_comp, ←F.map_sum, limits.biproduct.total, functor.map_id],
end

/--
An additive functor between preadditive categories preserves finite biproducts.
-/
-- This essentially repeats the work of the previous instance,
-- but gives good definitional reduction to `biproduct.lift` and `biproduct.desc`.
@[simps]
def map_biproduct {J : Type v} [fintype J] [decidable_eq J] (f : J → C) [has_biproduct f] :
  F.obj (⨁ f) ≅ ⨁ (λ j, F.obj (f j)) :=
{ hom := biproduct.lift (λ j, F.map (biproduct.π f j)),
  inv := biproduct.desc (λ j, F.map (biproduct.ι f j)),
  hom_inv_id' :=
  begin
    simp only [biproduct.lift_desc],
    simp only [←F.map_comp, ←F.map_sum, limits.biproduct.total, functor.map_id],
  end,
  inv_hom_id' :=
  begin
    ext j j',
    dsimp,
    simp_rw [category.comp_id,  category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      ←F.map_comp, biproduct.ι_π, F.map_dite],
    simp only [dif_ctx_congr, eq_to_hom_map, F.map_zero],
  end }

end

end functor
end preadditive

end category_theory
