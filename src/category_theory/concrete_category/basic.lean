/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import category_theory.types category_theory.full_subcategory

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Sort*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Sort*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget
C`, see `class has_forget`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget.mk'`.

In both cases this is done using the `bundled_category` class. Its
default constructor assumes the bundled morphisms approach, and requires

* an injective `to_fun : hom (ia : c α) (ib : c β) → α → β` projection;
* `id` and `comp g f` morphisms that project to `id` and `g ∘ f`.

Note that the argument order agrees with `function.comp`, not
`category_theory.comp`. This way we can directly use
`@monoid_hom.comp` as an argument to `bundled_category.mk`.

For a full concrete subcategory `D = bundled d` of a bundled category
`C = bundled c` we provide `bundled_category.restrict_str`
constructor. This constructor agrees with `induced_category` but also
allows us to automatically prove that the `induced_functor : C ⥤ D` is
a “partially forgetting” functor, i.e., `induced_functor ⋙ forget D =
forget C`.

For unbundled morphisms we provide a convenience constructor
`bundled_category.of_hom_class`. It accepts a morphism class `hom : Π
α β (ia : c α) (ib : c β), (α → β) → Prop` together with proofs of
`hom id` and `hom g → hom f → hom (g ∘ f)`, and creates a
`bundled_category` instance using `subtype hom` as the bundled
morphisms type.


-/

universes v u₁ u₂ u₃

namespace category_theory

/-- A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`. -/
class concrete_category (C : Type u₂) extends category.{v} C :=
(forget : C ⥤ Type u₁)
[forget_faithful : faithful forget]

@[reducible] def forget (C : Type u₂) [concrete_category C] := concrete_category.forget C

attribute [instance] concrete_category.forget_faithful

instance concrete_category.types : concrete_category (Type u₂) :=
{ forget := 𝟭 _ }

/--
`has_forget C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ C` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class has_forget (C : Type u₂) (D : Type u₃) [concrete_category.{v u₁} C] [concrete_category.{v u₁} D] :=
(forget₂ : C ⥤ D)
(forget_comp : forget₂ ⋙ (forget D) = forget C)

@[reducible] def forget₂ (C D : Type u₂) [concrete_category.{v u₁} C] [concrete_category.{v u₁} D]
  [has_forget C D] : C ⥤ D :=
has_forget.forget₂ C D

instance forget_faithful (C D : Type u₂) [concrete_category.{v u₁} C] [concrete_category.{v u₁} D]
  [has_forget C D] : faithful (forget₂ C D) :=
(has_forget.forget_comp C D).faithful_of_comp

instance induced_category.concrete_category {C : Type u₂} {D : Type u₃} [concrete_category D] (f : C → D) :
  concrete_category (induced_category f) :=
{ forget := induced_functor f ⋙ forget D }

instance induced_category.has_forget {C : Type u₂} {D : Type u₃} [concrete_category D] (f : C → D) :
  has_forget (induced_category f) D :=
{ forget₂ := induced_functor f,
  forget_comp := rfl }

/--
In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def has_forget.mk' {C D : Type u₂} [concrete_category.{v u₁} C] [concrete_category.{v u₁} D]
  (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
  (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, (forget D).map (map f) == (forget C).map f) :
has_forget C D :=
{ forget₂ := faithful.div _ _ _ @h_obj _ @h_map,
  forget_comp := by apply faithful.div_comp }

instance (C : Type u₂) [concrete_category.{u₂ u₂} C] : has_forget C (Type u₂) :=
{ forget₂ := forget C,
  forget_comp := functor.comp_id _ }

end category_theory
