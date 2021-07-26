/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.endomorphism
import category_theory.category.Cat
import algebra.category.Mon.basic

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transfering some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `α` with a monoid structure, `single_obj α` is `unit` type with `category` structure
such that `End (single_obj α).star` is the monoid `α`.  This can be extended to a functor `Mon ⥤
Cat`.

If `α` is a group, then `single_obj α` is a groupoid.

An element `x : α` can be reinterpreted as an element of `End (single_obj.star α)` using
`single_obj.to_End`.

## Implementation notes

- `category_struct.comp` on `End (single_obj.star α)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `α`.

- By default, Lean puts instances into `category_theory` namespace instead of
  `category_theory.single_obj`, so we give all names explicitly.
-/

universes u v w

namespace category_theory
/-- Type tag on `unit` used to define single-object categories and groupoids. -/
@[nolint unused_arguments has_inhabited_instance]
def single_obj (α : Type u) : Type := unit

namespace single_obj

variables (α : Type u)

/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
instance category_struct [has_one α] [has_mul α] : category_struct (single_obj α) :=
{ hom := λ _ _, α,
  comp := λ _ _ _ x y, y * x,
  id := λ _, 1 }

/-- Monoid laws become category laws for the single object category. -/
instance category [monoid α] : category (single_obj α) :=
{ comp_id' := λ _ _, one_mul,
  id_comp' := λ _ _, mul_one,
  assoc' := λ _ _ _ _ x y z, (mul_assoc z y x).symm }

lemma id_as_one [monoid α] (x : single_obj α) : 𝟙 x = 1 := rfl

lemma comp_as_mul [monoid α] {x y z : single_obj α} (f : x ⟶ y) (g : y ⟶ z) :
  f ≫ g = g * f := rfl

/--
Groupoid structure on `single_obj α`.

See https://stacks.math.columbia.edu/tag/0019.
-/
instance groupoid [group α] : groupoid (single_obj α) :=
{ inv := λ _ _ x, x⁻¹,
  inv_comp' := λ _ _, mul_right_inv,
  comp_inv' := λ _ _, mul_left_inv }

lemma inv_as_inv [group α] {x y : single_obj α} (f : x ⟶ y) : inv f = f⁻¹ :=
by { ext, rw [comp_as_mul, inv_mul_self, id_as_one] }

/-- The single object in `single_obj α`. -/
protected def star : single_obj α := unit.star

/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def to_End [monoid α] : α ≃* End (single_obj.star α) :=
{ map_mul' := λ x y, rfl,
  .. equiv.refl α }

lemma to_End_def [monoid α] (x : α) : to_End α x = x := rfl

/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor.

See https://stacks.math.columbia.edu/tag/001F --
although we do not characterize when the functor is full or faithful.
-/
def map_hom (α : Type u) (β : Type v) [monoid α] [monoid β] :
  (α →* β) ≃ (single_obj α) ⥤ (single_obj β) :=
{ to_fun := λ f,
  { obj := id,
    map := λ _ _, ⇑f,
    map_id' := λ _, f.map_one,
    map_comp' := λ _ _ _ x y, f.map_mul y x },
  inv_fun := λ f,
    { to_fun := @functor.map _ _ _ _ f (single_obj.star α) (single_obj.star α),
      map_one' := f.map_id _,
      map_mul' := λ x y, f.map_comp y x },
  left_inv := λ ⟨f, h₁, h₂⟩, rfl,
  right_inv := λ f, by cases f; obviously }

lemma map_hom_id (α : Type u) [monoid α] : map_hom α α (monoid_hom.id α) = 𝟭 _ := rfl

lemma map_hom_comp {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α →* β)
  {γ : Type w} [monoid γ] (g : β →* γ) :
  map_hom α γ (g.comp f) = map_hom α β f ⋙ map_hom β γ g :=
rfl

/-- Given a function `f : C → G` from a category to a group, we get a functor
    `C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps] def difference_functor {C G} [category C] [group G] (f : C → G) : C ⥤ single_obj G :=
{ obj := λ _, (),
  map := λ x y _, f y * (f x)⁻¹,
  map_id' := by { intro, rw [single_obj.id_as_one, mul_right_inv] },
  map_comp' := by { intros, rw [single_obj.comp_as_mul, ←mul_assoc,
    mul_left_inj, mul_assoc, inv_mul_self, mul_one] } }

end single_obj

end category_theory

open category_theory

namespace monoid_hom

/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `category_theory.single_obj.map_hom` for an equivalence between these types. -/
@[reducible] def to_functor {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α →* β) :
  (single_obj α) ⥤ (single_obj β) :=
single_obj.map_hom α β f

@[simp] lemma id_to_functor (α : Type u) [monoid α] : (id α).to_functor = 𝟭 _ := rfl
@[simp] lemma comp_to_functor {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α →* β)
  {γ : Type w} [monoid γ] (g : β →* γ) :
  (g.comp f).to_functor = f.to_functor ⋙ g.to_functor :=
rfl

end monoid_hom

namespace units

variables (α : Type u) [monoid α]

/--
The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def to_Aut : units α ≃* Aut (single_obj.star α) :=
(units.map_equiv (single_obj.to_End α)).trans $
  Aut.units_End_equiv_Aut _

@[simp] lemma to_Aut_hom (x : units α) : (to_Aut α x).hom = single_obj.to_End α x := rfl
@[simp] lemma to_Aut_inv (x : units α) :
  (to_Aut α x).inv = single_obj.to_End α (x⁻¹ : units α) :=
rfl
end units

namespace Mon

open category_theory

/-- The fully faithful functor from `Mon` to `Cat`. -/
def to_Cat : Mon ⥤ Cat :=
{ obj := λ x, Cat.of (single_obj x),
  map := λ x y f, single_obj.map_hom x y f }

instance to_Cat_full : full to_Cat :=
{ preimage := λ x y, (single_obj.map_hom x y).inv_fun,
  witness' := λ x y, by apply equiv.right_inv }

instance to_Cat_faithful : faithful to_Cat :=
{ map_injective' := λ x y, by apply equiv.injective }

end Mon
