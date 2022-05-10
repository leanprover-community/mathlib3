/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.biproducts
import category_theory.limits.preserves.shapes.zero

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `preserves_biproduct` and `preserves_binary_biproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images,
* show that in a preadditive category, a functor preserves a biproduct if and only if it preserves
  the corresponding product if and only if it preserves the corresponding coproduct.

-/

universes v u u₂

noncomputable theory

open category_theory
open category_theory.limits

namespace category_theory

variables {C : Type u} [category.{v} C] {D : Type u₂} [category.{v} D]

section has_zero_morphisms
variables [has_zero_morphisms C] [has_zero_morphisms D]

namespace functor

section map
variables (F : C ⥤ D) [preserves_zero_morphisms F]

section bicone
variables {J : Type v} [decidable_eq J]

/-- The image of a bicone under a functor. -/
@[simps]
def map_bicone {f : J → C} (b : bicone f) : bicone (F.obj ∘ f) :=
{ X := F.obj b.X,
  π := λ j, F.map (b.π j),
  ι := λ j, F.map (b.ι j),
  ι_π := λ j j',
  begin
    rw ← F.map_comp,
    split_ifs,
    { subst h,
      simp only [bicone_ι_π_self, category_theory.functor.map_id, eq_to_hom_refl] },
    { rw [bicone_ι_π_ne _ h, F.map_zero] }
  end }

end bicone

/-- The image of a binary bicone under a functor. -/
@[simps]
def map_binary_bicone {X Y : C} (b : binary_bicone X Y) : binary_bicone (F.obj X) (F.obj Y) :=
{ X := F.obj b.X,
  fst := F.map b.fst,
  snd := F.map b.snd,
  inl := F.map b.inl,
  inr := F.map b.inr,
  inl_fst' := by rw [← F.map_comp, b.inl_fst, F.map_id],
  inl_snd' := by rw [← F.map_comp, b.inl_snd, F.map_zero],
  inr_fst' := by rw [← F.map_comp, b.inr_fst, F.map_zero],
  inr_snd' := by rw [← F.map_comp, b.inr_snd, F.map_id] }

end map

end functor

open category_theory.functor

namespace limits

section bicone
variables {J : Type v} [decidable_eq J]

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
class preserves_biproduct (f : J → C) (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {b : bicone f}, b.is_bilimit → (F.map_bicone b).is_bilimit)

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
def is_bilimit_of_preserves {f : J → C} (F : C ⥤ D) [preserves_zero_morphisms F]
  [preserves_biproduct f F] {b : bicone f} (hb : b.is_bilimit) : (F.map_bicone b).is_bilimit :=
preserves_biproduct.preserves hb

variables (J)

/-- A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f` for every
    `f : J → C`. -/
class preserves_biproducts_of_shape (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {f : J → C}, preserves_biproduct f F)

attribute [instance, priority 100] preserves_biproducts_of_shape.preserves

end bicone

/-- A functor `F` preserves finite biproducts if it preserves biproducts of shape `J` whenever
    `J` is a fintype. -/
class preserves_finite_biproducts (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {J : Type v} [decidable_eq J] [fintype J], preserves_biproducts_of_shape J F)

attribute [instance, priority 100] preserves_finite_biproducts.preserves

/-- A functor `F` preserves biproducts if it preserves biproducts of any (small) shape `J`. -/
class preserves_biproducts (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {J : Type v} [decidable_eq J], preserves_biproducts_of_shape J F)

attribute [instance, priority 100] preserves_biproducts.preserves

@[priority 100]
instance preserves_finite_biproducts_of_preserves_biproducts (F : C ⥤ D)
  [preserves_zero_morphisms F] [preserves_biproducts F] : preserves_finite_biproducts F :=
{ preserves := λ J _ _, infer_instance }

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
class preserves_binary_biproduct (X Y : C) (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {b : binary_bicone X Y}, b.is_bilimit → (F.map_binary_bicone b).is_bilimit)

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
def is_binary_bilimit_of_preserves {X Y : C} (F : C ⥤ D) [preserves_zero_morphisms F]
  [preserves_binary_biproduct X Y F] {b : binary_bicone X Y} (hb : b.is_bilimit) :
  (F.map_binary_bicone b).is_bilimit :=
preserves_binary_biproduct.preserves hb

/-- A functor `F` preserves binary biproducts if it preserves the binary biproduct of `X` and `Y`
    for all `X` and `Y`. -/
class preserves_binary_biproducts (F : C ⥤ D) [preserves_zero_morphisms F] :=
(preserves : Π {X Y : C}, preserves_binary_biproduct X Y F . tactic.apply_instance)

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preserves_binary_biproduct_of_preserves_biproduct (F : C ⥤ D) [preserves_zero_morphisms F]
  (X Y : C) [preserves_biproduct (pair X Y).obj F] : preserves_binary_biproduct X Y F :=
{ preserves := λ b hb,
  { is_limit := is_limit.of_iso_limit
      ((is_limit.postcompose_hom_equiv (by exact diagram_iso_pair _) _).symm
        ((is_bilimit_of_preserves F (b.to_bicone_is_bilimit.symm hb)).is_limit)) $
      cones.ext (iso.refl _) (λ j, by { cases j, tidy }),
    is_colimit := is_colimit.of_iso_colimit
      ((is_colimit.precompose_inv_equiv (by exact diagram_iso_pair _ ) _).symm
        ((is_bilimit_of_preserves F (b.to_bicone_is_bilimit.symm hb)).is_colimit)) $
      cocones.ext (iso.refl _) (λ j, by { cases j, tidy }) } }

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preserves_binary_biproducts_of_preserves_biproducts (F : C ⥤ D)
  [preserves_zero_morphisms F] [preserves_biproducts_of_shape (discrete walking_pair.{v}) F] :
  preserves_binary_biproducts F :=
{ preserves := λ X Y, preserves_binary_biproduct_of_preserves_biproduct F X Y }

attribute [instance, priority 100] preserves_binary_biproducts.preserves

end limits

open category_theory.limits

namespace functor

section bicone
variables {J : Type v} [decidable_eq J] (F : C ⥤ D) [preserves_zero_morphisms F] (f : J → C)
  [has_biproduct f] [preserves_biproduct f F]

instance has_biproduct_of_preserves : has_biproduct (F.obj ∘ f) :=
has_biproduct.mk
{ bicone := F.map_bicone (biproduct.bicone f),
  is_bilimit := preserves_biproduct.preserves (biproduct.is_bilimit _) }

/-- If `F` preserves a biproduct, we get a definitionally nice isomorphism
    `F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`. -/
@[simp]
def map_biproduct : F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f) :=
biproduct.unique_up_to_iso _ (preserves_biproduct.preserves (biproduct.is_bilimit _))

lemma map_biproduct_hom : (map_biproduct F f).hom = biproduct.lift (λ j, F.map (biproduct.π f j)) :=
rfl

lemma map_biproduct_inv : (map_biproduct F f).inv = biproduct.desc (λ j, F.map (biproduct.ι f j)) :=
rfl

end bicone

variables (F : C ⥤ D) [preserves_zero_morphisms F] (X Y : C) [has_binary_biproduct X Y]
  [preserves_binary_biproduct X Y F]

instance has_binary_biproduct_of_preserves : has_binary_biproduct (F.obj X) (F.obj Y) :=
has_binary_biproduct.mk
{ bicone := F.map_binary_bicone (binary_biproduct.bicone X Y),
  is_bilimit := preserves_binary_biproduct.preserves (binary_biproduct.is_bilimit _ _) }

/-- If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
    `F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`. -/
@[simp]
def map_biprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
biprod.unique_up_to_iso _ _
  (preserves_binary_biproduct.preserves (binary_biproduct.is_bilimit _ _))

lemma map_biprod_hom : (map_biprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
rfl

lemma map_biprod_inv : (map_biprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
rfl

end functor

namespace limits
variables (F : C ⥤ D) [preserves_zero_morphisms F]

section bicone
variables {J : Type v} [decidable_eq J] (f : J → C) [has_biproduct f] [preserves_biproduct f F]
  {W : C}

lemma biproduct.map_lift_map_biprod (g : Π j, W ⟶ f j) :
  F.map (biproduct.lift g) ≫ (F.map_biproduct f).hom = biproduct.lift (λ j, F.map (g j)) :=
by { ext, simp [← F.map_comp] }

lemma biproduct.map_biproduct_inv_map_desc (g : Π j, f j ⟶ W) :
  (F.map_biproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc (λ j, F.map (g j)) :=
by { ext, simp [← F.map_comp] }

lemma biproduct.map_biproduct_hom_desc (g : Π j, f j ⟶ W) :
  (F.map_biproduct f).hom ≫ biproduct.desc (λ j, F.map (g j)) = F.map (biproduct.desc g) :=
by rw [← biproduct.map_biproduct_inv_map_desc, iso.hom_inv_id_assoc]

end bicone

section binary_bicone
variables (X Y : C) [has_binary_biproduct X Y] [preserves_binary_biproduct X Y F] {W : C}

lemma biprod.map_lift_map_biprod (f : W ⟶ X) (g : W ⟶ Y) :
  F.map (biprod.lift f g) ≫ (F.map_biprod X Y).hom = biprod.lift (F.map f) (F.map g) :=
by ext; simp [← F.map_comp]

lemma biprod.lift_map_biprod (f : W ⟶ X) (g : W ⟶ Y) :
  biprod.lift (F.map f) (F.map g) ≫ (F.map_biprod X Y).inv = F.map (biprod.lift f g) :=
by rw [← biprod.map_lift_map_biprod, category.assoc, iso.hom_inv_id, category.comp_id]

lemma biprod.map_biprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
  (F.map_biprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) :=
by ext; simp [← F.map_comp]

lemma biprod.map_biprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
 (F.map_biprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) :=
by rw [← biprod.map_biprod_inv_map_desc, iso.hom_inv_id_assoc]

end binary_bicone

end limits

end has_zero_morphisms

open category_theory.functor

section preadditive
variables [preadditive C] [preadditive D] (F : C ⥤ D) [preserves_zero_morphisms F]

namespace limits

section fintype
variables {J : Type v} [decidable_eq J] [fintype J]

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite products. -/
def preserves_product_of_preserves_biproduct {f : J → C} [preserves_biproduct f F] :
  preserves_limit (discrete.functor f) F :=
{ preserves := λ c hc, is_limit.of_iso_limit
  ((is_limit.postcompose_inv_equiv (discrete.comp_nat_iso_discrete _ _) _).symm
    (is_bilimit_of_preserves F (bicone_is_bilimit_of_limit_cone_of_is_limit hc)).is_limit) $
  cones.ext (iso.refl _) (by tidy) }

section
local attribute [instance] preserves_product_of_preserves_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite products. -/
def preserves_products_of_shape_of_preserves_biproducts_of_shape
  [preserves_biproducts_of_shape J F] : preserves_limits_of_shape (discrete J) F :=
{ preserves_limit := λ f, preserves_limit_of_iso_diagram _ discrete.nat_iso_functor.symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
    preserves finite biproducts. -/
def preserves_biproduct_of_preserves_product {f : J → C} [preserves_limit (discrete.functor f) F] :
  preserves_biproduct f F :=
{ preserves := λ b hb, is_bilimit_of_is_limit _ $
    is_limit.of_iso_limit ((is_limit.postcompose_hom_equiv (discrete.comp_nat_iso_discrete _ _)
      (F.map_cone b.to_cone)).symm (is_limit_of_preserves F hb.is_limit)) $
      cones.ext (iso.refl _) (by tidy) }

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
    preserves finite biproducts. -/
def preserves_biproducts_of_shape_of_preserves_products_of_shape
  [preserves_limits_of_shape (discrete J) F] : preserves_biproducts_of_shape J F :=
{ preserves := λ f, preserves_biproduct_of_preserves_product F }

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite coproducts. -/
def preserves_coproduct_of_preserves_biproduct {f : J → C} [preserves_biproduct f F] :
  preserves_colimit (discrete.functor f) F :=
{ preserves := λ c hc, is_colimit.of_iso_colimit
    ((is_colimit.precompose_hom_equiv (discrete.comp_nat_iso_discrete _ _) _).symm
      (is_bilimit_of_preserves F
        (bicone_is_bilimit_of_colimit_cocone_of_is_colimit hc)).is_colimit) $
    cocones.ext (iso.refl _) (by tidy) }

section
local attribute [instance] preserves_coproduct_of_preserves_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite coproducts. -/
def preserves_coproducts_of_shape_of_preserves_biproducts_of_shape
  [preserves_biproducts_of_shape J F] : preserves_colimits_of_shape (discrete J) F :=
{ preserves_colimit := λ f, preserves_colimit_of_iso_diagram _ discrete.nat_iso_functor.symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
    preserves finite biproducts. -/
def preserves_biproduct_of_preserves_coproduct {f : J → C}
  [preserves_colimit (discrete.functor f) F] : preserves_biproduct f F :=
{ preserves := λ b hb, is_bilimit_of_is_colimit _ $
    is_colimit.of_iso_colimit ((is_colimit.precompose_inv_equiv (discrete.comp_nat_iso_discrete _ _)
      (F.map_cocone b.to_cocone)).symm (is_colimit_of_preserves F hb.is_colimit)) $
      cocones.ext (iso.refl _) (by tidy) }

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
    preserves finite biproducts. -/
def preserves_biproducts_of_shape_of_preserves_coproducts_of_shape
  [preserves_colimits_of_shape (discrete J) F] : preserves_biproducts_of_shape J F :=
{ preserves := λ f, preserves_biproduct_of_preserves_coproduct F }

end fintype

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary products. -/
def preserves_binary_product_of_preserves_binary_biproduct {X Y : C}
  [preserves_binary_biproduct X Y F] : preserves_limit (pair X Y) F :=
{ preserves := λ c hc, is_limit.of_iso_limit
    ((is_limit.postcompose_inv_equiv (by exact diagram_iso_pair _) _).symm
      (is_binary_bilimit_of_preserves F
        (binary_bicone_is_bilimit_of_limit_cone_of_is_limit hc)).is_limit) $
    cones.ext (iso.refl _) (λ j, by { cases j, tidy }) }

section
local attribute [instance] preserves_binary_product_of_preserves_binary_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary products. -/
def preserves_binary_products_of_preserves_binary_biproducts
  [preserves_binary_biproducts F] : preserves_limits_of_shape (discrete walking_pair.{v}) F :=
{ preserves_limit := λ K, preserves_limit_of_iso_diagram _ (diagram_iso_pair _).symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
    preserves binary biproducts. -/
def preserves_binary_biproduct_of_preserves_binary_product {X Y : C}
  [preserves_limit (pair X Y) F] : preserves_binary_biproduct X Y F :=
{ preserves := λ b hb, is_binary_bilimit_of_is_limit _ $
    is_limit.of_iso_limit ((is_limit.postcompose_hom_equiv (by exact diagram_iso_pair _)
      (F.map_cone b.to_cone)).symm (is_limit_of_preserves F hb.is_limit)) $
        cones.ext (iso.refl _) (λ j, by { cases j, tidy }) }

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
    preserves binary biproducts. -/
def preserves_binary_biproducts_of_preserves_binary_products
  [preserves_limits_of_shape (discrete walking_pair.{v}) F] : preserves_binary_biproducts F :=
{ preserves := λ X Y, preserves_binary_biproduct_of_preserves_binary_product F }

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary coproducts. -/
def preserves_binary_coproduct_of_preserves_binary_biproduct {X Y : C}
  [preserves_binary_biproduct X Y F] : preserves_colimit (pair X Y) F :=
{ preserves := λ c hc, is_colimit.of_iso_colimit
    ((is_colimit.precompose_hom_equiv (by exact diagram_iso_pair _) _).symm
      (is_binary_bilimit_of_preserves F
        (binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit hc)).is_colimit) $
      cocones.ext (iso.refl _) (λ j, by { cases j, tidy }) }

section
local attribute [instance] preserves_binary_coproduct_of_preserves_binary_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary coproducts. -/
def preserves_binary_coproducts_of_preserves_binary_biproducts
  [preserves_binary_biproducts F] : preserves_colimits_of_shape (discrete walking_pair.{v}) F :=
{ preserves_colimit := λ K, preserves_colimit_of_iso_diagram _ (diagram_iso_pair _).symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
    preserves binary biproducts. -/
def preserves_binary_biproduct_of_preserves_binary_coproduct {X Y : C}
  [preserves_colimit (pair X Y) F] : preserves_binary_biproduct X Y F :=
{ preserves := λ b hb, is_binary_bilimit_of_is_colimit _ $
    is_colimit.of_iso_colimit ((is_colimit.precompose_inv_equiv (by exact diagram_iso_pair _)
      (F.map_cocone b.to_cocone)).symm (is_colimit_of_preserves F hb.is_colimit)) $
        cocones.ext (iso.refl _) (λ j, by { cases j, tidy }) }

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
    preserves binary biproducts. -/
def preserves_binary_biproducts_of_preserves_binary_coproducts
  [preserves_colimits_of_shape (discrete walking_pair.{v}) F] : preserves_binary_biproducts F :=
{ preserves := λ X Y, preserves_binary_biproduct_of_preserves_binary_coproduct F }

end limits

end preadditive

end category_theory
