-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.products

universes u v

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive two : Type v
| left | right

def two.map {C : Type u} (X Y : C) : two → C
| two.left := X
| two.right := Y

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

variables {C} {X Y : C}

def prod.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : fan (two.map X Y) :=
{ X := P,
  π :=
  { app := λ j, begin cases j, exact π₁, exact π₂ end }}
def sum.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : cofan (two.map X Y) :=
{ X := P,
  ι :=
  { app := λ j, begin cases j, exact ι₁, exact ι₂ end }}

-- FIXME can we use `def` here? with a `class` attribute?

variables (C)

class has_binary_products extends has_products_of_shape.{u v} two.{v} C
class has_binary_coproducts extends has_coproducts_of_shape.{u v} two.{v} C

variables {C}

class has_binary_product (X Y : C) extends has_product.{u v} (two.map X Y)
class has_binary_coproduct (X Y : C) extends has_coproduct.{u v} (two.map X Y)

instance has_binary_product_of_has_binary_products (X Y : C) [i : has_binary_products.{u v} C] :
  has_binary_product.{u v} X Y :=
{ fan := has_products_of_shape.fan (two.map X Y),
  is_product := has_products_of_shape.is_product (two.map X Y) }
instance has_binary_coproduct_of_has_binary_coproducts (X Y : C) [i : has_binary_coproducts.{u v} C] :
  has_binary_coproduct.{u v} X Y :=
{ cofan := has_coproducts_of_shape.cofan (two.map X Y),
  is_coproduct := has_coproducts_of_shape.is_coproduct (two.map X Y) }

-- These are defs because they do not necessarily give the nicest constructions.
def has_binary_products_of_has_products [i : has_products_of_shape.{u v} two C] :
  has_binary_products.{u v} C := { .. i }
def has_binary_product_of_has_product (X Y : C) [i : has_product.{u v} (two.map X Y)] :
  has_binary_product.{u v} X Y := { .. i }
def has_binary_coproducts_of_has_coproducts [i : has_coproducts_of_shape.{u v} two C] :
  has_binary_coproducts.{u v} C := { .. i }
def has_binary_coproduct_of_has_coproduct (X Y : C) [i : has_coproduct.{u v} (two.map X Y)] :
  has_binary_coproduct.{u v} X Y := { .. i }

variables (X Y)

section prod
variable [has_binary_product.{u v} X Y]

def prod.span : fan (two.map X Y) := has_product.fan.{u v} (two.map X Y)
protected def prod : C := (prod.span.{u v} X Y).X
def prod.fst : limits.prod X Y ⟶ X :=
(prod.span.{u v} X Y).π.app two.left
def prod.snd : limits.prod X Y ⟶ Y :=
(prod.span.{u v} X Y).π.app two.right

variables {X Y}

def prod.lift {P : C} (fst : P ⟶ X) (snd : P ⟶ Y) : P ⟶ limits.prod X Y :=
limit.lift.{u v} _ (prod.mk.{u v} fst snd)

@[simp] lemma prod.lift_fst {P : C} (fst : P ⟶ X) (snd : P ⟶ Y) : prod.lift fst snd ≫ prod.fst _ _ = fst :=
limit.lift_π (prod.mk.{u v} fst snd) two.left
@[simp] lemma prod.lift_snd {P : C} (fst : P ⟶ X) (snd : P ⟶ Y) : prod.lift fst snd ≫ prod.snd _ _ = snd :=
limit.lift_π (prod.mk.{u v} fst snd) two.right

def prod.map
  {U V : C} [has_binary_product.{u v} U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  (limits.prod X Y) ⟶ (limits.prod U V) :=
pi.lift (λ b, two.cases_on b (prod.fst X Y ≫ fst) (prod.snd X Y ≫ snd))

@[simp] lemma pi.map_fst
  {U V : C} [has_binary_product.{u v} U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  prod.map fst snd ≫ prod.fst U V = prod.fst X Y ≫ fst :=
by erw is_limit.fac; refl
@[simp] lemma pi.map_snd
  {U V : C} [has_binary_product.{u v} U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  prod.map fst snd ≫ prod.snd U V = prod.snd X Y ≫ snd :=
by erw is_limit.fac; refl


@[extensionality] lemma prod.hom_ext
  {P : C} {g h : P ⟶ limits.prod.{u v} X Y}
  (w_fst : g ≫ prod.fst X Y = h ≫ prod.fst X Y)
  (w_snd : g ≫ prod.snd X Y = h ≫ prod.snd X Y) : g = h :=
limit.hom_ext (λ j, two.cases_on j w_fst w_snd)

end prod

section sum
variable [has_binary_coproduct.{u v} X Y]

def sum.cospan : cofan (two.map X Y) := has_coproduct.cofan.{u v} (two.map X Y)
protected def sum : C := (sum.cospan.{u v} X Y).X
def sum.inl : X ⟶ limits.sum X Y :=
(sum.cospan.{u v} X Y).ι.app two.left
def sum.inr : Y ⟶ limits.sum X Y :=
(sum.cospan.{u v} X Y).ι.app two.right

variables {X Y}

def sum.desc {P : C} (left : X ⟶ P) (right : Y ⟶ P) : limits.sum X Y ⟶ P :=
colimit.desc.{u v} _ (sum.mk.{u v} left right)

end sum

-- TODO many things

-- pullbacks from binary_products and equalizers
-- finite products from binary_products and terminal objects

end category_theory.limits
