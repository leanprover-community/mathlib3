/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import tactic.equiv_rw

/-!
We construct isomorphisms describing products over certain shapes.

* Products over sigma types:
```
def product_over_sigma_iso {I : Type v} {Z : I → Type v} (f : (Σ i, Z i) → C) :
  ∏ f ≅ ∏ λ i, ∏ (λ z, f ⟨i, z⟩)
```
* Products over two element types as binary products:
```
def product_over_equiv_walking_pair {I : Type v} (e : I ≃ walking_pair) (f : I → C)
  ∏ f ≅ (f (e.symm left)) ⨯ (f (e.symm right))
```
* Products over one element types:
```
def product_over_equiv_punit {I : Type v} (e : I ≃ punit) (f : I → C) :
  ∏ f ≅ f (e.symm punit.star)
```
* Products over `sum` types:
```
def product_over_sum_iso {I J : Type v} (f : I ⊕ J → C) :
  ∏ f ≅ (∏ f ∘ sum.inl) ⨯ (∏ f ∘ sum.inr)
```

### TODO
* Also the coproduct and biproduct versions of these.

* These isomorphisms could be further generalized to limits over disjoint union diagrams.
  (One could even do diagrams of the form `Σ i, Z i`,
  although one would first have to set up the category structure.)
-/

universes v u

open category_theory

namespace category_theory.limits

variables {C : Type u} [category.{v} C]

/--
We can restrict a cone over a sigma type to a cone over one of the fibers.
-/
@[simps]
def fan.restrict_to_fiber {I : Type v} {Z : I → Type v} {f : (Σ i, Z i) → C}
  (c : fan f) (i : I) : fan (λ z, f ⟨i, z⟩) :=
{ X := c.X,
  π := { app := λ z, c.π.app ⟨i, z⟩, }, }

/--
Given a cone over each fiber of a sigma type,
and then a cone over the cone points of those cones,
we can build a cone over the sigma type.
-/
@[simps]
def cone_over_sigma {I : Type v} {Z : I → Type v} (f : (Σ i, Z i) → C)
  (P : Π i, fan (λ z, f ⟨i, z⟩)) (Q : fan (λ i, (P i).X)) :
  fan f :=
{ X := Q.X,
  π :=
  { app := λ p, Q.π.app p.1 ≫ (P p.1).π.app p.2 ≫ eq_to_hom (by { cases p, refl, }),
    naturality' := λ X Y f,
    begin
      cases X with Xi Xz, cases Y with Yi Yz, rcases f with ⟨⟨⟨rfl, rfl⟩⟩⟩,
      simp,
    end, }, }

/--
Given a cone `s` over a sigma type, and limit cones `P i` over each fiber,
we can lift `s` to produce a cone over the limit points `(P i).X`.
-/
@[simps]
def lift_over_fibers {I : Type v} {Z : I → Type v} {f : (Σ i, Z i) → C}
  (P : Π i, fan (λ z, f ⟨i, z⟩))
  (w : Π i, is_limit (P i)) (s : fan f) :
  fan (λ i, (P i).X) :=
{ X := s.X,
  π := { app := λ i, (w i).lift (s.restrict_to_fiber i) }, }

/--
When all of the cones used in `cone_over_sigma f P Q` are limit cones,
the resulting cone is also a limit cone.
-/
def is_limit_cone_over_sigma {I : Type v} {Z : I → Type v} (f : (Σ i, Z i) → C)
  (P : Π i, fan (λ z, f ⟨i, z⟩)) (Q : fan (λ i, (P i).X))
  (w₁ : Π i, is_limit (P i)) (w₂ : is_limit Q) :
  is_limit (cone_over_sigma f P Q) :=
{ lift := λ s, w₂.lift
  { X := s.X,
    π := { app := λ i, (w₁ i).lift (fan.restrict_to_fiber s i), }, },
  uniq' := λ s m w,
  begin
    apply w₂.uniq (lift_over_fibers P w₁ s) m,
    intro i,
    apply (w₁ i).hom_ext,
    intro z,
    simpa using w ⟨i, z⟩,
  end, }

/--
Given any specified choices of the products involved (via `has_*` instances),
the product over a sigma type is isomorphic to
the product over the base of the products over the fibers.
-/
def product_over_sigma_iso {I : Type v} {Z : I → Type v} (f : (Σ i, Z i) → C)
  [has_product f] [∀ i, has_product (λ z, f ⟨i, z⟩)] [has_product (λ i, ∏ (λ z, f ⟨i, z⟩))] :
  ∏ f ≅ ∏ λ i, ∏ (λ z, f ⟨i, z⟩) :=
begin
  transitivity (cone_over_sigma f (λ i, limit.cone (discrete.functor (λ z, f ⟨i, z⟩))) _).X,
  { apply is_limit.cone_point_unique_up_to_iso (limit.is_limit _)
    (is_limit_cone_over_sigma _ _ _ _ _),
    { exact (λ i, limit.is_limit _), },
    { apply limit.is_limit _, assumption, } },
  { simp,
    apply iso.refl, },
end

section
open walking_pair

lemma equiv_walking_pair_aux {I : Type v} (e : I ≃ limits.walking_pair) (f : I → C) (i : I) :
  (limits.pair (f (e.symm left)) (f (e.symm right))).obj (e i) =
    (discrete.functor f).obj i :=
begin
  cases h : e i;
  { simp only [discrete.functor_obj, limits.pair_obj_left, limits.pair_obj_right],
    rw [←h, equiv.symm_apply_apply], }
end

local attribute [simp] equiv_walking_pair_aux

/--
Given an equivalence `I ≃ walking_pair`, we can convert a `binary_fan` to a `fan`.
-/
@[simps]
def fan_of_binary_fan {I : Type v} (e : I ≃ walking_pair) {f : I → C}
  (c : binary_fan (f (e.symm left)) (f (e.symm right))) : fan f :=
{ X := c.X,
  π := { app := λ i, c.π.app (e i) ≫ eq_to_hom (by simp), }, }

/--
Given an equivalence `I ≃ walking_pair`,
we get an equivalence of categories of cones,
allowing us to convert between `fan` and `binary_fan`.
-/
def cone_equivalence_of_equiv_walking_pair {I : Type v} (e : I ≃ walking_pair) (f : I → C) :
  cone (discrete.functor f) ≌ cone (pair (f (e.symm left)) (f (e.symm right))) :=
begin
  apply cones.equivalence_of_reindexing (discrete.equivalence e.symm),
  apply discrete.nat_iso,
  rintro ⟨i|j⟩; simp,
end

/--
If a fan over a type equivalent to `walking_pair` is a limit cone,
then the corresponding binary fan is a limit cone too.
-/
def is_limit_binary_fan_of_is_limit_fan {I : Type v} (e : I ≃ walking_pair) (f : I → C)
  (c : fan f) (h : is_limit c) :
  is_limit ((cone_equivalence_of_equiv_walking_pair e f).functor.obj c) :=
is_limit.of_cone_equiv _ h

/--
If a binary_fan is a limit cone,
then the corresponding fan over a type equivalent to `walking_pair` is a limit cone too.
-/
def is_limit_fan_of_is_limit_binary_fan {I : Type v} (e : I ≃ walking_pair) (f : I → C)
  (c : binary_fan (f (e.symm left)) (f (e.symm right))) (h : is_limit c) :
  is_limit ((cone_equivalence_of_equiv_walking_pair e f).inverse.obj c) :=
is_limit.of_cone_equiv _ h

/--
Given any specified choice of the product,
the product over a type equivalent to `walking_pair`
is just the binary product of the two objects.
-/
-- We could prove this using the above lemmas tranferring `is_limit` terms,
-- but there is also a direct API for comparing chosen limits.
def product_over_equiv_walking_pair {I : Type v} (e : I ≃ walking_pair) (f : I → C)
  [has_product f] [has_binary_product (f (e.symm left)) (f (e.symm right))] :
  ∏ f ≅ (f (e.symm left)) ⨯ (f (e.symm right)) :=
has_limit.ext_of_equivalence (discrete.equivalence e) (discrete.nat_iso (λ i, by simp))

end

/--
Given any specified choice of the product,
the product over a type equivalent to `punit`
is just the object sitting over `punit.star`.
-/
def product_over_equiv_punit {I : Type v} (e : I ≃ punit) (f : I → C) [has_product f] :
  ∏ f ≅ f (e.symm punit.star) :=
{ hom := pi.π f (e.symm punit.star),
  inv := pi.lift (λ i, eq_to_hom (congr_arg f (e.injective (subsingleton.elim _ _)))),
  hom_inv_id' := begin ext j, equiv_rw e at j, cases j, simp, end, }

/--
Given any specified choice of the product,
the product over a `unique` type `I`
is just the object sitting over `default I`.
-/
def product_over_unique {I : Type v} [unique I] (f : I → C) [has_product f] :
  ∏ f ≅ f (default I) :=
product_over_equiv_punit equiv_punit_of_unique f

/--
Given any specified choices of the products involved (using `has_*` typeclasses),
the product over a `sum` type is isomorphic to
the binary product of the products over the two types.
-/
-- We could muck about transferring `is_limit` instances,
-- but it's so easy to just write down the maps,
-- and let automation apply the extensionality lemmas to prove they are inverses.
def product_over_sum_iso {I J : Type v} (f : I ⊕ J → C)
  [has_product f] [has_product (f ∘ sum.inl)] [has_product (f ∘ sum.inr)]
  [has_binary_product (∏ f ∘ sum.inl) (∏ f ∘ sum.inr)] :
  ∏ f ≅ (∏ f ∘ sum.inl) ⨯ (∏ f ∘ sum.inr) :=
{ hom := prod.lift (pi.lift (λ i, pi.π f (sum.inl i))) (pi.lift (λ j, pi.π f (sum.inr j))),
  inv := pi.lift (λ x, sum.cases_on x
    (λ (i : I), limits.prod.fst ≫ limits.pi.π _ i)
    (λ (j : J), limits.prod.snd ≫ limits.pi.π _ j)), }

/--
Given any specified choices of the products involved (using `has_*` typeclasses),
the product over a `sum` type is isomorphic to
the binary product of the products over the two types.

This variant of `product_over_sum_iso` is expressed in terms of two functions,
one out of each of the two types.
-/
def product_over_sum_iso' {I J : Type v} (f : I → C) (g : J → C)
  [has_product f] [has_product g] [has_product (sum.elim f g)] [has_binary_product (∏ f) (∏ g)] :
  ∏ (sum.elim f g) ≅ ∏ f ⨯ ∏ g :=
product_over_sum_iso (sum.elim f g)

end category_theory.limits
