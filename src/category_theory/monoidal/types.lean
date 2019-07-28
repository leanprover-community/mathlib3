-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Michael Jendrusch, Scott Morrison
import category_theory.types
import category_theory.monoidal.category

open category_theory
open tactic

universes u v

namespace category_theory.monoidal

instance types : monoidal_category.{u+1} (Type u) :=
{ tensor_obj := λ X Y, X × Y,
  tensor_hom := λ _ _ _ _ f g, prod.map f g,
  tensor_unit := punit,
  left_unitor := λ X, (equiv.punit_prod X).to_iso,
  right_unitor := λ X, (equiv.prod_punit X).to_iso,
  associator := λ X Y Z, (equiv.prod_assoc X Y Z).to_iso,
  ..category_theory.types.{u+1} }

-- TODO Once we add braided/symmetric categories, include the braiding.
-- TODO More generally, define the symmetric monoidal structure on any category with products.

end category_theory.monoidal
