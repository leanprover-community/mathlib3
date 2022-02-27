/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import category_theory.preadditive.functor_category
import category_theory.limits.preserves.shapes.zero
import category_theory.limits.shapes.biproducts

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.

We also define the category of bundled additive functors.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian
groups.

# Project:

- Prove that a functor is additive if it preserves finite biproducts
  (See https://stacks.math.columbia.edu/tag/010M.)
-/

namespace category_theory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class functor.additive {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] (F : C ⥤ D) : Prop :=
(map_add' : Π {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g . obviously)

section preadditive

namespace functor

section
variables {C D : Type*} [category C] [category D] [preadditive C]
  [preadditive D] (F : C ⥤ D) [functor.additive F]

@[simp]
lemma map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
functor.additive.map_add'

/-- `F.map_add_hom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps {fully_applied := ff}]
def map_add_hom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
add_monoid_hom.mk' (λ f, F.map f) (λ f g, F.map_add)

lemma coe_map_add_hom {X Y : C} : ⇑(F.map_add_hom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y := rfl

@[priority 100]
instance preserves_zero_morphisms_of_additive : preserves_zero_morphisms F :=
{ map_zero' := λ X Y, F.map_add_hom.map_zero }

instance : additive (𝟭 C) :=
{}

instance {E : Type*} [category E] [preadditive E] (G : D ⥤ E) [functor.additive G] :
  additive (F ⋙ G) :=
{}

@[simp]
lemma map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = - F.map f :=
F.map_add_hom.map_neg _

@[simp]
lemma map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
F.map_add_hom.map_sub _ _

-- You can alternatively just use `functor.map_smul` here, with an explicit `(r : ℤ)` argument.
lemma map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
F.map_add_hom.map_zsmul _ _

open_locale big_operators

@[simp]
lemma map_sum {X Y : C} {α : Type*} (f : α → (X ⟶ Y)) (s : finset α) :
  F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
(F.map_add_hom : (X ⟶ Y) →+ _).map_sum f s

end

section induced_category
variables {C : Type*} {D : Type*} [category D] [preadditive D] (F : C → D)

instance induced_functor_additive : functor.additive (induced_functor F) := {}

end induced_category

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
(by simp_rw [←F.map_comp, ←F.map_sum, biproduct.total, functor.map_id])

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
  by simp only [biproduct.lift_desc, ←F.map_comp, ←F.map_sum, biproduct.total, F.map_id],
  inv_hom_id' :=
  begin
    ext j j',
    simp only [category.comp_id,  category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      ←F.map_comp, biproduct.ι_π, F.map_dite, dif_ctx_congr, eq_to_hom_map, F.map_zero],
  end }

end

end functor

namespace equivalence

variables {C D : Type*} [category C] [category D] [preadditive C] [preadditive D]

instance inverse_additive (e : C ≌ D) [e.functor.additive] : e.inverse.additive :=
{ map_add' := λ X Y f g, by { apply e.functor.map_injective, simp, }, }

end equivalence

section
variables (C D : Type*) [category C] [category D] [preadditive C] [preadditive D]

/-- Bundled additive functors. -/
@[derive category, nolint has_inhabited_instance]
def AdditiveFunctor :=
{ F : C ⥤ D // functor.additive F }

infixr ` ⥤+ `:26 := AdditiveFunctor

instance : preadditive (C ⥤+ D) :=
preadditive.induced_category.category _

/-- An additive functor is in particular a functor. -/
@[derive full, derive faithful]
def AdditiveFunctor.forget : (C ⥤+ D) ⥤ (C ⥤ D) :=
full_subcategory_inclusion _

variables {C D}

/-- Turn an additive functor into an object of the catgory `AdditiveFunctor C D`. -/
def AdditiveFunctor.of (F : C ⥤ D) [F.additive] : C ⥤+ D :=
⟨F, infer_instance⟩

@[simp]
lemma AdditiveFunctor.of_fst (F : C ⥤ D) [F.additive] : (AdditiveFunctor.of F).1 = F :=
rfl

@[simp]
lemma AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
rfl

lemma AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.additive] :
  (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
rfl

@[simp]
lemma AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) :
  (AdditiveFunctor.forget C D).map α = α :=
rfl

instance : functor.additive (AdditiveFunctor.forget C D) :=
{ map_add' := λ F G α β, rfl }

instance (F : C ⥤+ D) : functor.additive F.1 :=
F.2

end

end preadditive

end category_theory
