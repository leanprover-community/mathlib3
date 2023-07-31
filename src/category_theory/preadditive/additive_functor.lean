/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import category_theory.limits.exact_functor
import category_theory.limits.preserves.finite
import category_theory.preadditive.biproducts
import category_theory.preadditive.functor_category

/-!
# Additive Functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.
Conversely, if `F : C ⥤ D` is a functor between preadditive categories, where `C` has binary
biproducts, and if `F` preserves binary biproducts, then `F` is additive.

We also define the category of bundled additive functors.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that for every two objects `X` and
`Y`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian groups.

-/

universes v₁ v₂ u₁ u₂

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
(F.map_add_hom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]
lemma map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
(F.map_add_hom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_sub _ _

lemma map_nsmul {X Y : C} {f : X ⟶ Y} {n : ℕ} : F.map (n • f) = n • F.map f :=
(F.map_add_hom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

-- You can alternatively just use `functor.map_smul` here, with an explicit `(r : ℤ)` argument.
lemma map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
(F.map_add_hom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

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

instance full_subcategory_inclusion_additive
  {C : Type*} [category C] [preadditive C] (Z : C → Prop) :
  (full_subcategory_inclusion Z).additive := {}

section
-- To talk about preservation of biproducts we need to specify universes explicitly.

noncomputable theory

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
  [preadditive C] [preadditive D] (F : C ⥤ D)

open category_theory.limits
open category_theory.preadditive

@[priority 100]
instance preserves_finite_biproducts_of_additive [additive F] : preserves_finite_biproducts F :=
{ preserves := λ J _,
  { preserves := λ f,
    { preserves := λ b hb, by exactI is_bilimit_of_total _
      begin
        simp_rw [F.map_bicone_π, F.map_bicone_ι, ← F.map_comp, ← F.map_sum],
        dsimp only [map_bicone_X],
        simp_rw [← F.map_id],
        refine congr_arg _ (hb.is_limit.hom_ext (λ j, hb.is_colimit.hom_ext (λ j', _))),
        cases j, cases j',
        dsimp only [limits.bicone.to_cone_π_app],
        simp [sum_comp, comp_sum, bicone.ι_π, comp_dite, dite_comp],
      end } } }

lemma additive_of_preserves_binary_biproducts [has_binary_biproducts C] [preserves_zero_morphisms F]
  [preserves_binary_biproducts F] : additive F :=
{ map_add' := λ X Y f g, by rw [biprod.add_eq_lift_id_desc, F.map_comp, ← biprod.lift_map_biprod,
    ← biprod.map_biprod_hom_desc, category.assoc, iso.inv_hom_id_assoc, F.map_id,
    biprod.add_eq_lift_id_desc] }

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
@[derive category, nolint has_nonempty_instance]
def AdditiveFunctor :=
full_subcategory (λ (F : C ⥤ D), F.additive)

infixr ` ⥤+ `:26 := AdditiveFunctor

instance : preadditive (C ⥤+ D) :=
preadditive.induced_category _

/-- An additive functor is in particular a functor. -/
@[derive full, derive faithful]
def AdditiveFunctor.forget : (C ⥤+ D) ⥤ (C ⥤ D) :=
full_subcategory_inclusion _

variables {C D}

/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
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

section exact
open category_theory.limits

variables (C : Type u₁) (D : Type u₂) [category.{v₁} C] [category.{v₂} D] [preadditive C]
variables [preadditive D] [has_zero_object C] [has_zero_object D] [has_binary_biproducts C]

section
local attribute [instance] preserves_binary_biproducts_of_preserves_binary_products
local attribute [instance] preserves_binary_biproducts_of_preserves_binary_coproducts

/-- Turn a left exact functor into an additive functor. -/
@[derive full, derive faithful]
def AdditiveFunctor.of_left_exact : (C ⥤ₗ D) ⥤ (C ⥤+ D) :=
full_subcategory.map (λ F h, let hF := classical.choice h in
    by exactI functor.additive_of_preserves_binary_biproducts F)

/-- Turn a right exact functor into an additive functor. -/
@[derive full, derive faithful]
def AdditiveFunctor.of_right_exact : (C ⥤ᵣ D) ⥤ (C ⥤+ D) :=
full_subcategory.map (λ F h, let hF := classical.choice h in
  by exactI functor.additive_of_preserves_binary_biproducts F)

/-- Turn an exact functor into an additive functor. -/
@[derive full, derive faithful]
def AdditiveFunctor.of_exact : (C ⥤ₑ D) ⥤ (C ⥤+ D) :=
full_subcategory.map (λ F h, let hF := classical.choice h.1 in
  by exactI functor.additive_of_preserves_binary_biproducts F)

end

variables {C D}

@[simp] lemma AdditiveFunctor.of_left_exact_obj_fst (F : C ⥤ₗ D) :
  ((AdditiveFunctor.of_left_exact C D).obj F).obj = F.obj := rfl
@[simp] lemma AdditiveFunctor.of_right_exact_obj_fst (F : C ⥤ᵣ D) :
  ((AdditiveFunctor.of_right_exact C D).obj F).obj = F.obj := rfl
@[simp] lemma AdditiveFunctor.of_exact_obj_fst (F : C ⥤ₑ D) :
  ((AdditiveFunctor.of_exact C D).obj F).obj = F.obj := rfl

@[simp] lemma Additive_Functor.of_left_exact_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
  (AdditiveFunctor.of_left_exact C D).map α = α := rfl
@[simp] lemma Additive_Functor.of_right_exact_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
  (AdditiveFunctor.of_right_exact C D).map α = α := rfl
@[simp] lemma Additive_Functor.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
  (AdditiveFunctor.of_exact C D).map α = α := rfl

end exact

end preadditive

end category_theory
