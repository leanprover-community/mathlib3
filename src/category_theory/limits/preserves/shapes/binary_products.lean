/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves.basic
import category_theory.limits.creates

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `prod_comparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/

noncomputable theory

universes v u₁ u₂

namespace category_theory

open category limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace functor

abbreviation preserves_binary_product (X Y : C) := preserves_limit (pair X Y) G
abbreviation reflects_binary_product (X Y : C) := reflects_limit (pair X Y) G
abbreviation creates_binary_product (X Y : C) := creates_limit (pair X Y) G
abbreviation preserves_binary_products := preserves_limits_of_shape (discrete walking_pair) G
abbreviation reflects_binary_products := reflects_limits_of_shape (discrete walking_pair) G
abbreviation creates_binary_products := creates_limits_of_shape (discrete walking_pair) G
abbreviation preserves_binary_coproduct (X Y : C) := preserves_colimit (pair X Y) G
abbreviation reflects_binary_coproduct (X Y : C) := reflects_colimit (pair X Y) G
abbreviation creates_binary_coproduct (X Y : C) := creates_colimit (pair X Y) G
abbreviation preserves_binary_coproducts := preserves_colimits_of_shape (discrete walking_pair) G
abbreviation reflects_binary_coproducts := reflects_colimits_of_shape (discrete walking_pair) G
abbreviation creates_binary_coproducts := creates_colimits_of_shape (discrete walking_pair) G

end functor

-- TODO: make reflects/creates versions and dualise this
def preserves_binary_products_of_preserves_binary_product
  [∀ X Y, G.preserves_binary_product X Y] :
  G.preserves_binary_products :=
{ preserves_limit := λ K, preserves_limit_of_iso_diagram G (diagram_iso_pair K).symm }

example [G.preserves_binary_products] (X Y : C) : G.preserves_binary_product X Y := infer_instance

namespace limits

section
variables {P X Y Z : C} (f : P ⟶ X) (g : P ⟶ Y)

/--
The map of a binary fan is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `binary_fan.mk` with `functor.map_cone`.
-/
def is_limit_map_cone_binary_fan_equiv :
  is_limit (G.map_cone (binary_fan.mk f g)) ≃ is_limit (binary_fan.mk (G.map f) (G.map g)) :=
(is_limit.postcompose_hom_equiv (diagram_iso_pair _) _).symm.trans
  (is_limit.equiv_iso_limit (cones.ext (iso.refl _) (by { rintro (_ | _), tidy })))

/-- The property of preserving products expressed in terms of binary fans. -/
def map_is_limit_of_preserves_of_is_limit [G.preserves_binary_product X Y]
  (l : is_limit (binary_fan.mk f g)) :
  is_limit (binary_fan.mk (G.map f) (G.map g)) :=
is_limit_map_cone_binary_fan_equiv G f g (preserves_limit.preserves l)

/-- The property of reflecting products expressed in terms of binary fans. -/
def is_limit_of_reflects_of_map_is_limit [G.reflects_binary_product X Y]
  (l : is_limit (binary_fan.mk (G.map f) (G.map g))) :
  is_limit (binary_fan.mk f g) :=
reflects_limit.reflects ((is_limit_map_cone_binary_fan_equiv G f g).symm l)

variables (X Y) [has_binary_product X Y]

/--
If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
def is_limit_of_has_binary_product_of_preserves_binary_product
  [G.preserves_binary_product X Y] :
  is_limit (binary_fan.mk (G.map (limits.prod.fst : X ⨯ Y ⟶ X)) (G.map (limits.prod.snd))) :=
map_is_limit_of_preserves_of_is_limit G _ _ (prod_is_prod X Y)

variables [has_binary_product (G.obj X) (G.obj Y)]

/--
If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def preserves_binary_product.of_iso_prod_comparison [i : is_iso (prod_comparison G X Y)] :
  G.preserves_binary_product X Y :=
begin
  apply preserves_limit_of_preserves_limit_cone (prod_is_prod X Y),
  apply (is_limit_map_cone_binary_fan_equiv _ _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (pair (G.obj X) (G.obj Y))),
  apply i,
end

variables [G.preserves_binary_product X Y]
/--
If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def preserves_binary_product.iso :
  G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_binary_product_of_preserves_binary_product G X Y)
  (limit.is_limit _)

@[simp]
lemma preserves_binary_product.iso_hom :
  (preserves_binary_product.iso G X Y).hom = prod_comparison G X Y :=
rfl

instance : is_iso (prod_comparison G X Y) :=
begin
  rw ← preserves_binary_product.iso_hom,
  apply_instance
end

end

section
variables {P X Y Z : C} (f : X ⟶ P) (g : Y ⟶ P)

/--
The map of a binary cofan is a colimit iff
the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `binary_cofan.mk` with `functor.map_cocone`.
-/
def is_colimit_map_cocone_binary_cofan_equiv :
  is_colimit (G.map_cocone (binary_cofan.mk f g)) ≃
    is_colimit (binary_cofan.mk (G.map f) (G.map g)) :=
(is_colimit.precompose_hom_equiv (diagram_iso_pair _).symm _).symm.trans
  (is_colimit.equiv_iso_colimit (cocones.ext (iso.refl _) (by { rintro (_ | _), tidy, })))

/-- The property of preserving coproducts expressed in terms of binary cofans. -/
def map_is_colimit_of_preserves_of_is_colimit [G.preserves_binary_coproduct X Y]
  (l : is_colimit (binary_cofan.mk f g)) :
  is_colimit (binary_cofan.mk (G.map f) (G.map g)) :=
is_colimit_map_cocone_binary_cofan_equiv G f g (preserves_colimit.preserves l)

/-- The property of reflecting coproducts expressed in terms of binary cofans. -/
def is_colimit_of_reflects_of_map_is_colimit [G.reflects_binary_coproduct X Y]
  (l : is_colimit (binary_cofan.mk (G.map f) (G.map g))) :
  is_colimit (binary_cofan.mk f g) :=
reflects_colimit.reflects ((is_colimit_map_cocone_binary_cofan_equiv G f g).symm l)

variables (X Y) [has_binary_coproduct X Y]

/--
If `G` preserves binary coproducts and `C` has them, then the binary cofan constructed of the mapped
morphisms of the binary product cocone is a colimit.
-/
def is_colimit_of_has_binary_coproduct_of_preserves_binary_coproduct
  [G.preserves_binary_coproduct X Y] :
  is_colimit (binary_cofan.mk (G.map (coprod.inl : X ⟶ X ⨿ Y)) (G.map (coprod.inr))) :=
map_is_colimit_of_preserves_of_is_colimit G _ _ (coprod_is_coprod X Y)

variables [has_binary_coproduct (G.obj X) (G.obj Y)]

/--
If the coproduct comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def preserves_binary_coproduct.of_iso_coprod_comparison [i : is_iso (coprod_comparison G X Y)] :
  G.preserves_binary_coproduct X Y :=
begin
  apply preserves_colimit_of_preserves_colimit_cocone (coprod_is_coprod X Y),
  apply (is_colimit_map_cocone_binary_cofan_equiv _ _ _).symm _,
  apply is_colimit.of_point_iso (colimit.is_colimit (pair (G.obj X) (G.obj Y))),
  apply i,
end

variables [G.preserves_binary_coproduct X Y]
/--
If `G` preserves the coproduct of `(X,Y)`, then the coproduct comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def preserves_binary_coproduct.iso :
  G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y) :=
is_colimit.cocone_point_unique_up_to_iso
  (colimit.is_colimit _)
  (is_colimit_of_has_binary_coproduct_of_preserves_binary_coproduct G X Y)

@[simp]
lemma preserves_binary_coproduct.iso_hom :
  (preserves_binary_coproduct.iso G X Y).hom = coprod_comparison G X Y :=
rfl

instance : is_iso (coprod_comparison G X Y) :=
begin
  rw ← preserves_binary_coproduct.iso_hom,
  apply_instance
end

end

end limits
end category_theory
