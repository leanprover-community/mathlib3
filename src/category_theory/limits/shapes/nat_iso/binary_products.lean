/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.binary_products

/-!
Constructing binary products from specified objects, and characterisations of the morphisms
out them.
-/

universes v u

open category_theory
open opposite

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

open walking_pair

local attribute [tidy] tactic.case_bash

/--
We characterise `F.cones` objectwise for a functor `F` on the walking pair.
-/
@[simps]
def walking_pair_cones_equiv {Q : C} (F : discrete walking_pair.{v} ⥤ C) :
  F.cones.obj (op Q) ≅ ((Q ⟶ F.obj left) : Type v) × ((Q ⟶ F.obj right) : Type v) :=
{ hom := λ c, (c.app left, c.app right),
  inv := λ f, { app := λ j, walking_pair.cases_on j f.1 f.2 } }

/--
`is_binary_product X Y P` asserts that there is an isomorphism of hom-spaces
`(Q ⟶ P) ≅ (Q ⟶ X) × (Q ⟶ Y)`, natural in `Q`.
-/
structure is_binary_product (X Y P : C) :=
(hom_iso : Π (Q : C), (Q ⟶ P) ≅ (Q ⟶ X) × (Q ⟶ Y))
(naturality₁ : Π (Q : C) (f : Q ⟶ P), ((hom_iso Q).hom f).1 = f ≫ ((hom_iso P).hom (𝟙 P)).1 . obviously)
(naturality₂ : Π (Q : C) (f : Q ⟶ P), ((hom_iso Q).hom f).2 = f ≫ ((hom_iso P).hom (𝟙 P)).2 . obviously)

namespace is_binary_product

/--
If `P` is a binary product indexed by a functor `F`,
then `F.cones` is representable by `P`.
-/
def nat_iso
  {P : C} {F : discrete walking_pair.{v} ⥤ C}
  (I : is_binary_product.{v} (F.obj left) (F.obj right) P) :
    yoneda.obj P ≅ F.cones :=
begin
  -- Is there a cheaper way to do this? I feel like we're reproving some part of Yoneda.
  have n₁' : Π (Q Q' : C) (f : Q ⟶ Q') (g : Q' ⟶ P), ((I.hom_iso Q).hom (f ≫ g)).1 = f ≫ ((I.hom_iso Q').hom g).1 :=
    λ Q Q' f g, by rw [I.naturality₁, category.assoc, ←I.naturality₁],
  have n₂' : Π (Q Q' : C) (f : Q ⟶ Q') (g : Q' ⟶ P), ((I.hom_iso Q).hom (f ≫ g)).2 = f ≫ ((I.hom_iso Q').hom g).2 :=
    λ Q Q' f g, by rw [I.naturality₂, category.assoc, ←I.naturality₂],
  exact nat_iso.of_components (λ Q, ((I.hom_iso (unop Q)) ≪≫ (walking_pair_cones_equiv F).symm)) (by tidy)
end.

/--
If `P` represents `(pair X Y).cones`, then `P` is a binary product of `X` and `Y`.
-/
def of_nat_iso (X Y P : C) (i : yoneda.obj P ≅ (pair X Y).cones) : is_binary_product.{v} X Y P :=
{ hom_iso := λ Q, i.app (op Q) ≪≫ (walking_pair_cones_equiv (pair X Y)),
  naturality₁ := λ Q f, by simp [yoneda.naturality_id f i.hom],
  naturality₂ := λ Q f, by simp [yoneda.naturality_id f i.hom], }

section
variables {X Y P : C} (I : is_binary_product.{v} X Y P)

/-- The `cone` associated to a binary product. -/
def cone : cone (pair X Y) :=
is_limit.of_nat_iso.limit_cone (nat_iso I)

@[simp] lemma nat_iso_hom_app :
  ((@nat_iso _ _ _ (pair X Y) I).hom.app (op P) (𝟙 P)) = (cone I).π :=
begin
  dsimp [nat_iso], ext j,
  cases j; { simp, refl, },
end

/-- The witness that the `cone` associated to a binary product is a limit cone. -/
def to_is_limit : is_limit (cone I) :=
is_limit.of_nat_iso (nat_iso I)
end

/--
Construct an `is_binary_product` from a generic `is_limit`.
-/
def of_is_limit {X Y : C} {c : limits.cone (pair X Y)} (h : limits.is_limit c) :
  is_binary_product.{v} X Y c.X :=
of_nat_iso X Y c.X (is_limit.nat_iso h)

/-- A binary product is unique up to canonical isomorphism. -/
def unique {X Y : C} : unique_up_to_canonical_iso.{v} (λ P, is_binary_product.{v} X Y P) :=
(is_limit.uniqueness (pair X Y)).transport
  cones.forget (λ P e, e.cone) (λ P e, e.to_is_limit) (λ P e, rfl)

end is_binary_product

namespace has_binary_products

/--
Show that `C` has binary products by
providing a function `prod : C → C → C`,
and for all `X Y : C`, and all other objects `Q : C`,
providing an isomorphism `(Q ⟶ prod X Y) ≅ (Q ⟶ X) × (Q ⟶ Y)`
which is natural in `Q`.
-/
def mk' (prod : C → C → C) (I : Π X Y, is_binary_product.{v} X Y (prod X Y)) :
  has_binary_products.{v} C :=
{ has_limits_of_shape :=
  has_limits_of_shape.of_nat_iso (λ F,
    ⟨_, is_binary_product.nat_iso (I (F.obj left) (F.obj right))⟩) }

-- We verify that this construction allows us to easily build binary products in `Type`.
example : has_binary_products.{v} (Type v) :=
mk' (λ X Y, X × Y) (λ X Y,
  { hom_iso := (λ Q,
    { hom := λ f, (λ q, (f q).1, λ q, (f q).2),
      inv := λ p q, (p.1 q, p.2 q) }) })

/--
If a category has specified binary products,
we can construct `is_binary_product.{v} X Y (X ⨯ Y)` for each `X` and `Y`.
-/
def prod_is_binary_product [has_binary_products.{v} C] (X Y : C) : is_binary_product.{v} X Y (X ⨯ Y) :=
-- An alternative proof here could just be:
-- is_binary_product.of_is_limit (limit.is_limit _)
{ hom_iso := λ Q,
  { hom := λ f, (f ≫ prod.fst, f ≫ prod.snd),
    inv := λ p, prod.lift p.1 p.2, } }

end has_binary_products

-- TODO give alternative proofs about the braiding, to see how usable this is?


end category_theory.limits
