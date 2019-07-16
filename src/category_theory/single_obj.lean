/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

# Single-object category

Single object category with a given monoid of endomorphisms.  It is defined to faciliate transfering
some definitions and lemmas (e.g., conjugacy etc.) from category theory to monoids and groups.

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
import category_theory.endomorphism category_theory.groupoid category_theory.Cat
import data.equiv.algebra algebra.Mon.basic
import tactic.find

universes u v w

namespace category_theory
/-- Type tag on `unit` used to define single-object categories and groupoids. -/
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

/-- Groupoid structure on `single_obj α` -/
instance groupoid [group α] : groupoid (single_obj α) :=
{ inv := λ _ _ x, x⁻¹,
  inv_comp' := λ _ _, mul_right_inv,
  comp_inv' := λ _ _, mul_left_inv }

protected def star : single_obj α := unit.star

/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def to_End_equiv [monoid α] : End (single_obj.star α) ≃* α := mul_equiv.refl α

/-- Reinterpret an element of a monoid as an element of the endomorphisms monoid of the only object
    in the `single_obj α` category. -/
def to_End {α} [monoid α] (x : α) : End (single_obj.star α) := x

lemma to_End_def [monoid α] (x : α) : to_End x = x := rfl

/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor. -/
def map_hom_equiv {α : Type u} {β : Type v} [monoid α] [monoid β] :
  { f : α → β // is_monoid_hom f } ≃ (single_obj α) ⥤ (single_obj β) :=
{ to_fun := λ f,
  { obj := id,
    map := λ _ _, f.1,
    map_id' := λ _, f.2.map_one,
    map_comp' := λ _ _ _ x y, @is_mul_hom.map_mul _ _ _ _ _ f.2.1 y x },
  inv_fun := λ f, ⟨@functor.map _ _ _ _ f (single_obj.star α) (single_obj.star α),
    { map_mul := λ x y, f.map_comp y x, map_one := f.map_id _ }⟩,
  left_inv := λ ⟨f, hf⟩, rfl,
  right_inv := assume f, by rcases f; obviously }

/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `map_hom_equiv` for an equivalence between these types. -/
def map_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [hf : is_monoid_hom f] :
  (single_obj α) ⥤ (single_obj β) :=
map_hom_equiv.to_fun ⟨f, hf⟩ -- FIXME: doesn't work using `⇑`

lemma map_hom_id {α : Type u} [monoid α] : map_hom (@id α) = 𝟭 _ := rfl

lemma map_hom_comp {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]
  {γ : Type w} [monoid γ] (g : β → γ) [is_monoid_hom g] :
  map_hom f ⋙ map_hom g = map_hom (g ∘ f) :=
rfl

end single_obj

end category_theory

namespace Mon

open category_theory

/-- The fully faithful functor from `Mon` to `Cat`. -/
def to_Cat : Mon ⥤ Cat :=
{ obj := λ x, mk_ob (single_obj x),
  map := λ x y, single_obj.map_hom_equiv.to_fun }

instance to_Cat_full : full to_Cat :=
{ preimage := λ x y, single_obj.map_hom_equiv.inv_fun,
  witness' := λ x y, single_obj.map_hom_equiv.right_inv }

instance to_Cat_faithful : faithful to_Cat :=
{ injectivity' := λ x y, single_obj.map_hom_equiv.injective }

end Mon
