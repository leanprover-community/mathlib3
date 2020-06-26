/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.epi_mono
import category_theory.limits.shapes.binary_products
import category_theory.preadditive

/-!
# Biproducts and binary biproducts

We introduce the notion of biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

We model these here using a `bicone`, with a cone point `X`,
and natural transformations `π` from the constant functor with value `X` to `F`
and `ι` in the other direction.

We implement `has_bilimit` as a `bicone`, equipped with the evidence
`is_limit bicone.to_cone` and `is_colimit bicone.to_cocone`.

In practice, of course, we are only interested in the special case of bilimits
over `discrete J` for `[fintype J] [decidable_eq J]`,
which corresponds to finite biproducts.

TODO: We should provide a constructor that takes `has_limit F`, `has_colimit F`, and
and iso `limit F ≅ colimit F`, and produces `has_bilimit F`.

TODO: perhaps it makes sense to unify the treatment of zero objects with this a bit.

In addition to biproducts and binary biproducts, we define the notion of preadditive binary
biproduct, which is a preadditive version of binary biproducts. We show that a preadditive binary
biproduct is a binary biproduct and construct preadditive binary biproducts both from binary
products and from binary coproducts.

TODO: the preadditive version of finite biproducts

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.
-/

universes v u

open category_theory
open category_theory.functor

namespace category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]

/--
A `c : bicone F` is:
* an object `c.X` and
* a natural transformation `c.π : c.X ⟶ F` from the constant `c.X` functor to `F`.
* a natural transformation `c.ι : F ⟶ c.X` from `F` to the constant `c.X` functor.
-/
@[nolint has_inhabited_instance]
structure bicone {J : Type v} [small_category J] (F : J ⥤ C) :=
(X : C)
(π : (const J).obj X ⟶ F)
(ι : F ⟶ (const J).obj X)

variables {F : J ⥤ C}

namespace bicone
/-- Extract the cone from a bicone. -/
@[simps]
def to_cone (B : bicone F) : cone F :=
{ .. B }
/-- Extract the cocone from a bicone. -/
@[simps]
def to_cocone (B : bicone F) : cocone F :=
{ .. B }
end bicone

/--
`has_bilimit F` represents a particular chosen bicone which is
simultaneously a limit and a colimit of the diagram `F`.

(This is only interesting when the source category is discrete.)
-/
class has_bilimit (F : J ⥤ C) :=
(bicone : bicone F)
(is_limit : is_limit bicone.to_cone)
(is_colimit : is_colimit bicone.to_cocone)

@[priority 100]
instance has_limit_of_has_bilimit [has_bilimit F] : has_limit F :=
{ cone := has_bilimit.bicone.to_cone,
  is_limit := has_bilimit.is_limit, }

@[priority 100]
instance has_colimit_of_has_bilimit [has_bilimit F] : has_colimit F :=
{ cocone := has_bilimit.bicone.to_cocone,
  is_colimit := has_bilimit.is_colimit, }

variables (J C)

/--
`C` has bilimits of shape `J` if we have chosen
a particular limit and a particular colimit, with the same cone points,
of every functor `F : J ⥤ C`.

(This is only interesting if `J` is discrete.)
-/
class has_bilimits_of_shape :=
(has_bilimit : Π F : J ⥤ C, has_bilimit F)

attribute [instance, priority 100] has_bilimits_of_shape.has_bilimit

@[priority 100]
instance [has_bilimits_of_shape J C] : has_limits_of_shape J C :=
{ has_limit := λ F, by apply_instance }
@[priority 100]
instance [has_bilimits_of_shape J C] : has_colimits_of_shape J C :=
{ has_colimit := λ F, by apply_instance }

/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type with decidable equality. -/
class has_finite_biproducts :=
(has_bilimits_of_shape : Π (J : Type v) [fintype J] [decidable_eq J],
  has_bilimits_of_shape.{v} (discrete J) C)

attribute [instance] has_finite_biproducts.has_bilimits_of_shape

/--
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproduct_iso {J : Type v} (F : J → C) [has_bilimit (discrete.functor F)] :
  limits.pi_obj F ≅ limits.sigma_obj F :=
eq_to_iso rfl

end category_theory.limits

namespace category_theory.limits
variables {J : Type v}
variables {C : Type u} [category.{v} C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbreviation biproduct (f : J → C) [has_bilimit (discrete.functor f)] :=
limit (discrete.functor f)

notation `⨁ ` f:20 := biproduct f

/-- The projection onto a summand of a biproduct. -/
abbreviation biproduct.π (f : J → C) [has_bilimit (discrete.functor f)] (b : J) : ⨁ f ⟶ f b :=
limit.π (discrete.functor f) b
/-- The inclusion into a summand of a biproduct. -/
abbreviation biproduct.ι (f : J → C) [has_bilimit (discrete.functor f)] (b : J) : f b ⟶ ⨁ f :=
colimit.ι (discrete.functor f) b

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbreviation biproduct.lift
  {f : J → C} [has_bilimit (discrete.functor f)] {P : C} (p : Π b, P ⟶ f b) : P ⟶ ⨁ f :=
limit.lift _ (fan.mk p)
/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbreviation biproduct.desc
  {f : J → C} [has_bilimit (discrete.functor f)] {P : C} (p : Π b, f b ⟶ P) : ⨁ f ⟶ P :=
colimit.desc _ (cofan.mk p)

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map betweeen the biproducts. -/
abbreviation biproduct.map [fintype J] [decidable_eq J] {f g : J → C} [has_finite_biproducts.{v} C]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
(@lim (discrete J) _ C _ _).map (discrete.nat_trans p)

instance biproduct.ι_mono [decidable_eq J] (f : J → C) [has_bilimit (discrete.functor f)]
  (b : J) : split_mono (biproduct.ι f b) :=
{ retraction := biproduct.desc $
    λ b', if h : b' = b then eq_to_hom (congr_arg f h) else biproduct.ι f b' ≫ biproduct.π f b }

instance biproduct.π_epi [decidable_eq J] (f : J → C) [has_bilimit (discrete.functor f)]
  (b : J) : split_epi (biproduct.π f b) :=
{ section_ := biproduct.lift $
    λ b', if h : b = b' then eq_to_hom (congr_arg f h) else biproduct.ι f b ≫ biproduct.π f b' }

variables {C}

/--
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`.
-/
@[nolint has_inhabited_instance]
structure binary_bicone (P Q : C) :=
(X : C)
(π₁ : X ⟶ P)
(π₂ : X ⟶ Q)
(ι₁ : P ⟶ X)
(ι₂ : Q ⟶ X)

namespace binary_bicone
variables {P Q : C}

/-- Extract the cone from a binary bicone. -/
@[simp]
def to_cone (c : binary_bicone.{v} P Q) : cone (pair P Q) :=
binary_fan.mk c.π₁ c.π₂
/-- Extract the cocone from a binary bicone. -/
@[simp]
def to_cocone (c : binary_bicone.{v} P Q) : cocone (pair P Q) :=
binary_cofan.mk c.ι₁ c.ι₂

end binary_bicone

/--
`has_binary_biproduct P Q` represents a particular chosen bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class has_binary_biproduct (P Q : C) :=
(bicone : binary_bicone.{v} P Q)
(is_limit : is_limit bicone.to_cone)
(is_colimit : is_colimit bicone.to_cocone)

section
variable (C)

/--
`has_binary_biproducts C` represents a particular chosen bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class has_binary_biproducts :=
(has_binary_biproduct : Π (P Q : C), has_binary_biproduct.{v} P Q)

attribute [instance, priority 100] has_binary_biproducts.has_binary_biproduct

end

variables {P Q : C}

instance has_binary_biproduct.has_limit_pair [has_binary_biproduct.{v} P Q] :
  has_limit (pair P Q) :=
{ cone := has_binary_biproduct.bicone.to_cone,
  is_limit := has_binary_biproduct.is_limit.{v}, }

instance has_binary_biproduct.has_colimit_pair [has_binary_biproduct.{v} P Q] :
  has_colimit (pair P Q) :=
{ cocone := has_binary_biproduct.bicone.to_cocone,
  is_colimit := has_binary_biproduct.is_colimit.{v}, }

@[priority 100]
instance has_limits_of_shape_walking_pair [has_binary_biproducts.{v} C] :
  has_limits_of_shape.{v} (discrete walking_pair) C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_pair F).symm }
@[priority 100]
instance has_colimits_of_shape_walking_pair [has_binary_biproducts.{v} C] :
  has_colimits_of_shape.{v} (discrete walking_pair) C :=
{ has_colimit := λ F, has_colimit_of_iso (diagram_iso_pair F) }

@[priority 100]
instance has_binary_products_of_has_binary_biproducts [has_binary_biproducts.{v} C] :
  has_binary_products.{v} C :=
⟨by apply_instance⟩

@[priority 100]
instance has_binary_coproducts_of_has_binary_biproducts [has_binary_biproducts.{v} C] :
  has_binary_coproducts.{v} C :=
⟨by apply_instance⟩

/--
The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprod_iso (X Y : C) [has_binary_biproduct.{v} X Y]  :
  limits.prod X Y ≅ limits.coprod X Y :=
eq_to_iso rfl

/-- The chosen biproduct of a pair of objects. -/
abbreviation biprod (X Y : C) [has_binary_biproduct.{v} X Y] := limit (pair X Y)

notation X ` ⊞ `:20 Y:20 := biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbreviation biprod.fst {X Y : C} [has_binary_biproduct.{v} X Y] : X ⊞ Y ⟶ X :=
limit.π (pair X Y) walking_pair.left
/-- The projection onto the second summand of a binary biproduct. -/
abbreviation biprod.snd {X Y : C} [has_binary_biproduct.{v} X Y] : X ⊞ Y ⟶ Y :=
limit.π (pair X Y) walking_pair.right
/-- The inclusion into the first summand of a binary biproduct. -/
abbreviation biprod.inl {X Y : C} [has_binary_biproduct.{v} X Y] : X ⟶ X ⊞ Y :=
colimit.ι (pair X Y) walking_pair.left
/-- The inclusion into the second summand of a binary biproduct. -/
abbreviation biprod.inr {X Y : C} [has_binary_biproduct.{v} X Y] : Y ⟶ X ⊞ Y :=
colimit.ι (pair X Y) walking_pair.right

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbreviation biprod.lift {W X Y : C} [has_binary_biproduct.{v} X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  W ⟶ X ⊞ Y :=
limit.lift _ (binary_fan.mk f g)
/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbreviation biprod.desc {W X Y : C} [has_binary_biproduct.{v} X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  X ⊞ Y ⟶ W :=
colimit.desc _ (binary_cofan.mk f g)

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbreviation biprod.map {W X Y Z : C} [has_binary_biproducts.{v} C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
(@lim (discrete walking_pair) _ C _ _).map (@map_pair _ _ (pair W X) (pair Y Z) f g)

instance biprod.inl_mono {X Y : C} [has_binary_biproduct.{v} X Y] :
  split_mono (biprod.inl : X ⟶ X ⊞ Y) :=
{ retraction := biprod.desc (𝟙 X) (biprod.inr ≫ biprod.fst) }

instance biprod.inr_mono {X Y : C} [has_binary_biproduct.{v} X Y] :
  split_mono (biprod.inr : Y ⟶ X ⊞ Y) :=
{ retraction := biprod.desc (biprod.inl ≫ biprod.snd) (𝟙 Y)}

instance biprod.fst_epi {X Y : C} [has_binary_biproduct.{v} X Y] :
  split_epi (biprod.fst : X ⊞ Y ⟶ X) :=
{ section_ := biprod.lift (𝟙 X) (biprod.inl ≫ biprod.snd) }

instance biprod.snd_epi {X Y : C} [has_binary_biproduct.{v} X Y] :
  split_epi (biprod.snd : X ⊞ Y ⟶ Y) :=
{ section_ := biprod.lift (biprod.inr ≫ biprod.fst) (𝟙 Y) }

@[ext] lemma biprod.hom_ext {X Y Z : C} [has_binary_biproduct.{v} X Y] (f g : Z ⟶ X ⊞ Y)
  (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
binary_fan.is_limit.hom_ext has_binary_biproduct.is_limit h₀ h₁

@[ext] lemma biprod.hom_ext' {X Y Z : C} [has_binary_biproduct.{v} X Y] (f g : X ⊞ Y ⟶ Z)
  (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
binary_cofan.is_colimit.hom_ext has_binary_biproduct.is_colimit h₀ h₁

-- TODO:
-- If someone is interested, they could provide the constructions:
--   has_binary_biproducts ↔ has_finite_biproducts

section preadditive
variables [preadditive.{v} C]

open category_theory.preadditive

/-- A preadditive binary biproduct is a bicone on two objects `X` and `Y` satisfying a set of five
    axioms expressing the properties of a biproduct in additive terms. The notion of preadditive
    binary biproduct is strictly stronger than the notion of binary biproduct (but it in any
    preadditive category, the existence of a binary biproduct implies the existence of a
    preadditive binary biproduct: a biproduct is, in particular, a product, and every product gives
    rise to a preadditive binary biproduct, see `has_preadditive_binary_biproduct.of_has_limit_pair`). -/
class has_preadditive_binary_biproduct (X Y : C) :=
(bicone : binary_bicone.{v} X Y)
(ι₁_π₁' : bicone.ι₁ ≫ bicone.π₁ = 𝟙 X . obviously)
(ι₂_π₂' : bicone.ι₂ ≫ bicone.π₂ = 𝟙 Y . obviously)
(ι₂_π₁' : bicone.ι₂ ≫ bicone.π₁ = 0 . obviously)
(ι₁_π₂' : bicone.ι₁ ≫ bicone.π₂ = 0 . obviously)
(total' : bicone.π₁ ≫ bicone.ι₁ + bicone.π₂ ≫ bicone.ι₂ = 𝟙 bicone.X . obviously)

restate_axiom has_preadditive_binary_biproduct.ι₁_π₁'
restate_axiom has_preadditive_binary_biproduct.ι₂_π₂'
restate_axiom has_preadditive_binary_biproduct.ι₂_π₁'
restate_axiom has_preadditive_binary_biproduct.ι₁_π₂'
restate_axiom has_preadditive_binary_biproduct.total'
attribute [simp, reassoc] has_preadditive_binary_biproduct.ι₁_π₁
  has_preadditive_binary_biproduct.ι₂_π₂ has_preadditive_binary_biproduct.ι₂_π₁
  has_preadditive_binary_biproduct.ι₁_π₂
attribute [simp] has_preadditive_binary_biproduct.total

section
local attribute [tidy] tactic.case_bash

/-- A preadditive binary biproduct is a binary biproduct. -/
@[priority 100]
instance (X Y : C) [has_preadditive_binary_biproduct.{v} X Y] : has_binary_biproduct.{v} X Y :=
{ bicone := has_preadditive_binary_biproduct.bicone,
  is_limit :=
  { lift := λ s, binary_fan.fst s ≫ has_preadditive_binary_biproduct.bicone.ι₁ +
      binary_fan.snd s ≫ has_preadditive_binary_biproduct.bicone.ι₂,
    uniq' := λ s m h, by erw [←category.comp_id m, ←has_preadditive_binary_biproduct.total,
      comp_add, reassoc_of (h walking_pair.left), reassoc_of (h walking_pair.right)] },
  is_colimit :=
  { desc := λ s, has_preadditive_binary_biproduct.bicone.π₁ ≫ binary_cofan.inl s +
      has_preadditive_binary_biproduct.bicone.π₂ ≫ binary_cofan.inr s,
    uniq' := λ s m h, by erw [←category.id_comp m, ←has_preadditive_binary_biproduct.total,
      add_comp, category.assoc, category.assoc, h walking_pair.left, h walking_pair.right] } }

end

section
variables (X Y : C) [has_preadditive_binary_biproduct.{v} X Y]

@[simp, reassoc] lemma biprod.inl_fst : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.fst = 𝟙 X :=
has_preadditive_binary_biproduct.ι₁_π₁
@[simp, reassoc] lemma biprod.inr_snd : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.snd = 𝟙 Y :=
has_preadditive_binary_biproduct.ι₂_π₂
@[simp, reassoc] lemma biprod.inr_fst : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.fst = 0 :=
has_preadditive_binary_biproduct.ι₂_π₁
@[simp, reassoc] lemma biprod.inl_snd : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.snd = 0 :=
has_preadditive_binary_biproduct.ι₁_π₂
@[simp] lemma biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
has_preadditive_binary_biproduct.total

lemma biprod.inl_add_inr {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  f ≫ biprod.inl + g ≫ biprod.inr = biprod.lift f g := rfl

lemma biprod.fst_add_snd {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biprod.fst ≫ f + biprod.snd ≫ g = biprod.desc f g := rfl

@[simp, reassoc] lemma biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
  biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i :=
by simp [←biprod.inl_add_inr, ←biprod.fst_add_snd]

end

section has_limit_pair

/-- In a preadditive category, if the product of `X` and `Y` exists, then the preadditive binary
    biproduct of `X` and `Y` exists. -/
def has_preadditive_binary_biproduct.of_has_limit_pair (X Y : C) [has_limit.{v} (pair X Y)] :
  has_preadditive_binary_biproduct.{v} X Y :=
{ bicone :=
  { X := X ⨯ Y,
    π₁ := category_theory.limits.prod.fst,
    π₂ := category_theory.limits.prod.snd,
    ι₁ := prod.lift (𝟙 X) 0,
    ι₂ := prod.lift 0 (𝟙 Y) } }

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the preadditive binary
    biproduct of `X` and `Y` exists. -/
def has_preadditive_binary_biproduct.of_has_colimit_pair (X Y : C) [has_colimit.{v} (pair X Y)] :
  has_preadditive_binary_biproduct.{v} X Y :=
{ bicone :=
  { X := X ⨿ Y,
    π₁ := coprod.desc (𝟙 X) 0,
    π₂ := coprod.desc 0 (𝟙 Y),
    ι₁ := category_theory.limits.coprod.inl,
    ι₂ := category_theory.limits.coprod.inr } }

end has_limit_pair

section
variable (C)

/-- A preadditive category `has_preadditive_binary_biproducts` if the preadditive binary biproduct
    exists for every pair of objects. -/
class has_preadditive_binary_biproducts :=
(has_preadditive_binary_biproduct : Π (X Y : C), has_preadditive_binary_biproduct.{v} X Y)

attribute [instance, priority 100] has_preadditive_binary_biproducts.has_preadditive_binary_biproduct

@[priority 100]
instance [has_preadditive_binary_biproducts.{v} C] : has_binary_biproducts.{v} C :=
⟨λ X Y, by apply_instance⟩

/-- If a preadditive category has all binary products, then it has all preadditive binary
    biproducts. -/
-- This particularly dangerous as an instance,
-- as we can deduce `has_binary_products` from `has_preadditive_binary_biproducts`.
def has_preadditive_binary_biproducts_of_has_binary_products [has_binary_products.{v} C] :
  has_preadditive_binary_biproducts.{v} C :=
⟨λ X Y, has_preadditive_binary_biproduct.of_has_limit_pair X Y⟩

/-- If a preadditive category has all binary coproducts, then it has all preadditive binary
    biproducts. -/
-- This particularly dangerous as an instance,
-- as we can deduce `has_binary_products` from `has_preadditive_binary_biproducts`.
def has_preadditive_binary_biproducts_of_has_binary_coproducts [has_binary_coproducts.{v} C] :
  has_preadditive_binary_biproducts.{v} C :=
⟨λ X Y, has_preadditive_binary_biproduct.of_has_colimit_pair X Y⟩

end

end preadditive

end category_theory.limits
