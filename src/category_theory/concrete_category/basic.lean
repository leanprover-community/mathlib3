/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import category_theory.types
import category_theory.epi_mono

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Type*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Type*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`,
see `class has_forget₂`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `bundled_hom` and
`unbundled_hom`, see their documentation for details.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

universes w v v' u

namespace category_theory

/--
A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`.

Note that `concrete_category` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class concrete_category (C : Type u) [category.{v} C] :=
(forget [] : C ⥤ Type w)
[forget_faithful : faithful forget]

attribute [instance] concrete_category.forget_faithful

/-- The forgetful functor from a concrete category to `Type u`. -/
@[reducible] def forget (C : Type v) [category C] [concrete_category.{u} C] : C ⥤ Type u :=
concrete_category.forget C

instance concrete_category.types : concrete_category (Type u) :=
{ forget := 𝟭 _ }

/--
Provide a coercion to `Type u` for a concrete category. This is not marked as an instance
as it could potentially apply to every type, and so is too expensive in typeclass search.

You can use it on particular examples as:
```
instance : has_coe_to_sort X := concrete_category.has_coe_to_sort X
```
-/
def concrete_category.has_coe_to_sort (C : Type v) [category C] [concrete_category C] :
  has_coe_to_sort C (Type u) :=
⟨(concrete_category.forget C).obj⟩

section
local attribute [instance] concrete_category.has_coe_to_sort

variables {C : Type v} [category C] [concrete_category C]

@[simp] lemma forget_obj_eq_coe {X : C} : (forget C).obj X = X := rfl

/-- Usually a bundled hom structure already has a coercion to function
that works with different universes. So we don't use this as a global instance. -/
def concrete_category.has_coe_to_fun {X Y : C} : has_coe_to_fun (X ⟶ Y) (λ f, X → Y) :=
⟨λ f, (forget _).map f⟩

local attribute [instance] concrete_category.has_coe_to_fun

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations.-/
lemma concrete_category.hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x : X, f x = g x) : f = g :=
begin
  apply faithful.map_injective (forget C),
  ext,
  exact w x,
end

@[simp] lemma forget_map_eq_coe {X Y : C} (f : X ⟶ Y) : (forget C).map f = f := rfl

/--
Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
lemma congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
congr_fun (congr_arg (λ k : X ⟶ Y, (k : X → Y)) h) x

lemma coe_id {X : C} : ((𝟙 X) : X → X) = id :=
(forget _).map_id X

lemma coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g : X → Z) = g ∘ f :=
(forget _).map_comp f g

@[simp] lemma id_apply {X : C} (x : X) : ((𝟙 X) : X → X) x = x :=
congr_fun ((forget _).map_id X) x

@[simp] lemma comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
congr_fun ((forget _).map_comp _ _) x

lemma concrete_category.congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
congr_fun (congr_arg (λ f : X ⟶ Y, (f : X → Y)) h) x

lemma concrete_category.congr_arg {X Y : C} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x' :=
congr_arg (f : X → Y) h

/-- In any concrete category, injective morphisms are monomorphisms. -/
lemma concrete_category.mono_of_injective {X Y : C} (f : X ⟶ Y) (i : function.injective f) :
  mono f :=
faithful_reflects_mono (forget C) ((mono_iff_injective f).2 i)

/-- In any concrete category, surjective morphisms are epimorphisms. -/
lemma concrete_category.epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : function.surjective f) :
  epi f :=
faithful_reflects_epi (forget C) ((epi_iff_surjective f).2 s)

@[simp] lemma concrete_category.has_coe_to_fun_Type {X Y : Type u} (f : X ⟶ Y) :
  coe_fn f = f :=
rfl

end

/--
`has_forget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class has_forget₂ (C : Type v) (D : Type v') [category C] [concrete_category.{u} C] [category D]
  [concrete_category.{u} D] :=
(forget₂ : C ⥤ D)
(forget_comp : forget₂ ⋙ (forget D) = forget C . obviously)

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`has_forget₂ C `. -/
@[reducible] def forget₂ (C : Type v) (D : Type v') [category C] [concrete_category C] [category D]
  [concrete_category D] [has_forget₂ C D] : C ⥤ D :=
has_forget₂.forget₂

instance forget_faithful (C : Type v) (D : Type v') [category C] [concrete_category C] [category D]
  [concrete_category D] [has_forget₂ C D] : faithful (forget₂ C D) :=
has_forget₂.forget_comp.faithful_of_comp

instance induced_category.concrete_category {C : Type v} {D : Type v'} [category D]
  [concrete_category D] (f : C → D) :
  concrete_category (induced_category D f) :=
{ forget := induced_functor f ⋙ forget D }

instance induced_category.has_forget₂ {C : Type v} {D : Type v'} [category D] [concrete_category D]
  (f : C → D) :
  has_forget₂ (induced_category D f) D :=
{ forget₂ := induced_functor f,
  forget_comp := rfl }

instance full_subcategory.concrete_category {C : Type v} [category C] [concrete_category C]
  (Z : C → Prop) : concrete_category {X : C // Z X} :=
{ forget := full_subcategory_inclusion Z ⋙ forget C }

instance full_subcategory.has_forget₂ {C : Type v} [category C] [concrete_category C]
  (Z : C → Prop) : has_forget₂ {X : C // Z X} C :=
{ forget₂ := full_subcategory_inclusion Z,
  forget_comp := rfl }

/--
In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def has_forget₂.mk' {C : Type v} {D : Type v'} [category C] [concrete_category C] [category D]
  [concrete_category D] (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
  (map : Π {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, (forget D).map (map f) == (forget C).map f) :
has_forget₂ C D :=
{ forget₂ := faithful.div _ _ _ @h_obj _ @h_map,
  forget_comp := by apply faithful.div_comp }

instance has_forget_to_Type (C : Type v) [category C] [concrete_category C] :
  has_forget₂ C (Type u) :=
{ forget₂ := forget C,
  forget_comp := functor.comp_id _ }

end category_theory
