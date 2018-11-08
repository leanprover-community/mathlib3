-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.products

universes u v

open category_theory

namespace category_theory.limits

inductive two : Type v
| left | right

def two.map {C : Type u} (X Y : C) : two → C
| two.left := X
| two.right := Y

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

-- FIXME can we use `def` here? with a `class` attribute?

class has_binary_products extends has_products_of_shape.{u v} two.{v} C
class has_binary_coproducts extends has_coproducts_of_shape.{u v} two.{v} C

variables {C}

class has_binary_product (X Y : C) extends has_product.{u v} (two.map X Y)
class has_binary_coproduct (X Y : C) extends has_coproduct.{u v} (two.map X Y)

def has_binary_products_of_has_products [i : has_products_of_shape.{u v} two C] :
  has_binary_products.{u v} C := { .. i }
def has_binary_product_of_has_product (X Y : C) [i : has_product.{u v} (two.map X Y)] :
  has_binary_product.{u v} X Y := { .. i }
def has_binary_coproducts_of_has_coproducts [i : has_coproducts_of_shape.{u v} two C] :
  has_binary_coproducts.{u v} C := { .. i }
def has_binary_coproduct_of_has_coproduct (X Y : C) [i : has_coproduct.{u v} (two.map X Y)] :
  has_binary_coproduct.{u v} X Y := { .. i }

variables (X Y : C)

section prod
variable [has_binary_product.{u v} X Y]

def prod.span : fan (two.map X Y) := has_product.fan.{u v} (two.map X Y)
protected def prod : C := (prod.span.{u v} X Y).X
def prod.fst : limits.prod X Y ⟶ X :=
(prod.span.{u v} X Y).π.app two.left
def prod.snd : limits.prod X Y ⟶ Y :=
(prod.span.{u v} X Y).π.app two.right
end prod

section sum
variable [has_binary_coproduct.{u v} X Y]

def sum.cospan : cofan (two.map X Y) := has_coproduct.cofan.{u v} (two.map X Y)
protected def sum : C := (sum.cospan.{u v} X Y).X
def sum.inl : X ⟶ limits.sum X Y :=
(sum.cospan.{u v} X Y).ι.app two.left
def sum.inr : Y ⟶ limits.sum X Y :=
(sum.cospan.{u v} X Y).ι.app two.right
end sum

-- TODO many things

-- pullbacks from binary_products and equalizers
-- finite products from binary_products and terminal objects

end category_theory.limits
