/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.epi_mono
import category_theory.limits.shapes.binary_products
import category_theory.preadditive
import algebra.big_operators

/-!
# Biproducts and binary biproducts

We introduce the notion of biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

We treat first the case of a general category with zero morphisms,
and subsequently the case of a preadditive category.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit cocone.

In a preadditive category,
* any `binary_biproduct` satisfies `total : fst ≫ inl + snd ≫ inr = 𝟙 X`
* any `binary_product` is a `binary_biproduct`
* any `binary_coproduct` is a `binary_biproduct`

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

In a preadditive category,
* any `biproduct` satisfies `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
* any `product` is a `biproduct`
* any `coproduct` is a `biproduct`

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.
-/

universes v u

open category_theory
open category_theory.functor

namespace category_theory.limits

variables {J : Type v} [decidable_eq J]
variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

/--
A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
@[nolint has_inhabited_instance]
structure bicone (F : J → C) :=
(X : C)
(π : Π j, X ⟶ F j)
(ι : Π j, F j ⟶ X)
(ι_π : ∀ j j', ι j ≫ π j' = if h : j = j' then eq_to_hom (congr_arg F h) else 0)

@[simp] lemma bicone_ι_π_self {F : J → C} (B : bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) :=
by simpa using B.ι_π j j

@[simp] lemma bicone_ι_π_ne {F : J → C} (B : bicone F) {j j' : J} (h : j ≠ j') :
  B.ι j ≫ B.π j' = 0 :=
by simpa [h] using B.ι_π j j'

variables {F : J → C}

namespace bicone
/-- Extract the cone from a bicone. -/
@[simps]
def to_cone (B : bicone F) : cone (discrete.functor F) :=
{ X := B.X,
  π := { app := λ j, B.π j }, }
/-- Extract the cocone from a bicone. -/
@[simps]
def to_cocone (B : bicone F) : cocone (discrete.functor F) :=
{ X := B.X,
  ι := { app := λ j, B.ι j }, }
end bicone

/--
`has_biproduct F` represents a particular chosen bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class has_biproduct (F : J → C) :=
(bicone : bicone F)
(is_limit : is_limit bicone.to_cone)
(is_colimit : is_colimit bicone.to_cocone)

@[priority 100]
instance has_product_of_has_biproduct [has_biproduct F] : has_limit (discrete.functor F) :=
{ cone := has_biproduct.bicone.to_cone,
  is_limit := has_biproduct.is_limit, }

@[priority 100]
instance has_coproduct_of_has_biproduct [has_biproduct F] : has_colimit (discrete.functor F) :=
{ cocone := has_biproduct.bicone.to_cocone,
  is_colimit := has_biproduct.is_colimit, }

variables (J C)

/--
`C` has biproducts of shape `J` if we have chosen
a particular limit and a particular colimit, with the same cone points,
of every function `F : J → C`.
-/
class has_biproducts_of_shape :=
(has_biproduct : Π F : J → C, has_biproduct F)

attribute [instance, priority 100] has_biproducts_of_shape.has_biproduct

/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type with decidable equality. -/
class has_finite_biproducts :=
(has_biproducts_of_shape : Π (J : Type v) [fintype J] [decidable_eq J],
  has_biproducts_of_shape J C)

attribute [instance, priority 100] has_finite_biproducts.has_biproducts_of_shape

variables {J C}

/--
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproduct_iso (F : J → C) [has_biproduct F] :
  limits.pi_obj F ≅ limits.sigma_obj F :=
eq_to_iso rfl

end category_theory.limits

namespace category_theory.limits
variables {J : Type v} [decidable_eq J]
variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbreviation biproduct (f : J → C) [has_biproduct f] : C :=
limit (discrete.functor f)

notation `⨁ ` f:20 := biproduct f

/-- The chosen bicone over a family of elements. -/
abbreviation biproduct.bicone (f : J → C) [has_biproduct f] : bicone f :=
has_biproduct.bicone

/-- The cone coming from the chosen bicone is a limit cone. -/
abbreviation biproduct.is_limit (f : J → C) [has_biproduct f] :
  is_limit (biproduct.bicone f).to_cone :=
has_biproduct.is_limit

/-- The cocone coming from the chosen bicone is a colimit cocone. -/
abbreviation biproduct.is_colimit (f : J → C) [has_biproduct f] :
  is_colimit (biproduct.bicone f).to_cocone :=
has_biproduct.is_colimit

/-- The projection onto a summand of a biproduct. -/
abbreviation biproduct.π (f : J → C) [has_biproduct f] (b : J) : ⨁ f ⟶ f b :=
limit.π (discrete.functor f) b
/-- The inclusion into a summand of a biproduct. -/
abbreviation biproduct.ι (f : J → C) [has_biproduct f] (b : J) : f b ⟶ ⨁ f :=
colimit.ι (discrete.functor f) b

@[reassoc]
lemma biproduct.ι_π (f : J → C) [has_biproduct f] (j j' : J) :
  biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eq_to_hom (congr_arg f h) else 0 :=
has_biproduct.bicone.ι_π j j'

@[simp,reassoc]
lemma biproduct.ι_π_self (f : J → C) [has_biproduct f] (j : J) :
  biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ :=
by simp [biproduct.ι_π]

@[simp,reassoc]
lemma biproduct.ι_π_ne (f : J → C) [has_biproduct f] {j j' : J} (h : j ≠ j') :
  biproduct.ι f j ≫ biproduct.π f j' = 0 :=
by simp [biproduct.ι_π, h]

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbreviation biproduct.lift
  {f : J → C} [has_biproduct f] {P : C} (p : Π b, P ⟶ f b) : P ⟶ ⨁ f :=
limit.lift _ (fan.mk p)
/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbreviation biproduct.desc
  {f : J → C} [has_biproduct f] {P : C} (p : Π b, f b ⟶ P) : ⨁ f ⟶ P :=
colimit.desc _ (cofan.mk p)

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbreviation biproduct.map [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
lim_map (discrete.nat_trans p)

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbreviation biproduct.map' [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
@colim_map _ _ _ _ (discrete.functor f) (discrete.functor g) _ _ (discrete.nat_trans p)

@[ext] lemma biproduct.hom_ext {f : J → C} [has_biproduct f]
  {Z : C} (g h : Z ⟶ ⨁ f)
  (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
limit.hom_ext w

@[ext] lemma biproduct.hom_ext' {f : J → C} [has_biproduct f]
  {Z : C} (g h : ⨁ f ⟶ Z)
  (w : ∀ j, biproduct.ι f j ≫ g =  biproduct.ι f j ≫ h) : g = h :=
colimit.hom_ext w

lemma biproduct.map_eq_map' [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π b, f b ⟶ g b) : biproduct.map p = biproduct.map' p :=
begin
  ext j j',
  simp only [discrete.nat_trans_app, limits.ι_colim_map, limits.lim_map_π, category.assoc],
  rw [biproduct.ι_π_assoc, biproduct.ι_π],
  split_ifs,
  { subst h, rw [eq_to_hom_refl, category.id_comp], erw category.comp_id, },
  { simp, },
end

instance biproduct.ι_mono (f : J → C) [has_biproduct f]
  (b : J) : split_mono (biproduct.ι f b) :=
{ retraction := biproduct.desc $
    λ b', if h : b' = b then eq_to_hom (congr_arg f h) else biproduct.ι f b' ≫ biproduct.π f b }

instance biproduct.π_epi (f : J → C) [has_biproduct f]
  (b : J) : split_epi (biproduct.π f b) :=
{ section_ := biproduct.lift $
    λ b', if h : b = b' then eq_to_hom (congr_arg f h) else biproduct.ι f b ≫ biproduct.π f b' }

-- Because `biproduct.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[simp]
lemma biproduct.inl_map [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π j, f j ⟶ g j) (j : J) :
  biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j :=
begin
  rw biproduct.map_eq_map',
  simp,
end

variables {C}

/--
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
@[nolint has_inhabited_instance]
structure binary_bicone (P Q : C) :=
(X : C)
(fst : X ⟶ P)
(snd : X ⟶ Q)
(inl : P ⟶ X)
(inr : Q ⟶ X)
(inl_fst' : inl ≫ fst = 𝟙 P . obviously)
(inl_snd' : inl ≫ snd = 0 . obviously)
(inr_fst' : inr ≫ fst = 0 . obviously)
(inr_snd' : inr ≫ snd = 𝟙 Q . obviously)

restate_axiom binary_bicone.inl_fst'
restate_axiom binary_bicone.inl_snd'
restate_axiom binary_bicone.inr_fst'
restate_axiom binary_bicone.inr_snd'
attribute [simp, reassoc] binary_bicone.inl_fst binary_bicone.inl_snd
  binary_bicone.inr_fst binary_bicone.inr_snd

namespace binary_bicone
variables {P Q : C}

/-- Extract the cone from a binary bicone. -/
def to_cone (c : binary_bicone P Q) : cone (pair P Q) :=
binary_fan.mk c.fst c.snd

@[simp]
lemma to_cone_X (c : binary_bicone P Q) :
  c.to_cone.X = c.X := rfl

@[simp]
lemma to_cone_π_app_left (c : binary_bicone P Q) :
  c.to_cone.π.app (walking_pair.left) = c.fst := rfl
@[simp]
lemma to_cone_π_app_right (c : binary_bicone P Q) :
  c.to_cone.π.app (walking_pair.right) = c.snd := rfl

/-- Extract the cocone from a binary bicone. -/
def to_cocone (c : binary_bicone P Q) : cocone (pair P Q) :=
binary_cofan.mk c.inl c.inr

@[simp]
lemma to_cocone_X (c : binary_bicone P Q) :
  c.to_cocone.X = c.X := rfl

@[simp]
lemma to_cocone_ι_app_left (c : binary_bicone P Q) :
  c.to_cocone.ι.app (walking_pair.left) = c.inl := rfl
@[simp]
lemma to_cocone_ι_app_right (c : binary_bicone P Q) :
  c.to_cocone.ι.app (walking_pair.right) = c.inr := rfl

end binary_bicone

namespace bicone

/-- Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simps]
def to_binary_bicone {X Y : C} (b : bicone (pair X Y).obj) : binary_bicone X Y :=
{ X := b.X,
  fst := b.π walking_pair.left,
  snd := b.π walking_pair.right,
  inl := b.ι walking_pair.left,
  inr := b.ι walking_pair.right,
  inl_fst' := by { simp [bicone.ι_π], refl, },
  inr_fst' := by simp [bicone.ι_π],
  inl_snd' := by simp [bicone.ι_π],
  inr_snd' := by { simp [bicone.ι_π], refl, }, }

/--
If the cone obtained from a bicone over `pair X Y` is a limit cone,
so is the cone obtained by converting that bicone to a binary_bicone, then to a cone.
-/
def to_binary_bicone_is_limit {X Y : C} {b : bicone (pair X Y).obj}
  (c : is_limit (b.to_cone)) :
  is_limit (b.to_binary_bicone.to_cone) :=
{ lift := λ s, c.lift s,
   fac' := λ s j, by { cases j; erw c.fac, },
   uniq' := λ s m w,
   begin
     apply c.uniq s,
     rintro (⟨⟩|⟨⟩),
     exact w walking_pair.left,
     exact w walking_pair.right,
   end, }

/--
If the cocone obtained from a bicone over `pair X Y` is a colimit cocone,
so is the cocone obtained by converting that bicone to a binary_bicone, then to a cocone.
-/
def to_binary_bicone_is_colimit {X Y : C} {b : bicone (pair X Y).obj}
  (c : is_colimit (b.to_cocone)) :
  is_colimit (b.to_binary_bicone.to_cocone) :=
{ desc := λ s, c.desc s,
   fac' := λ s j, by { cases j; erw c.fac, },
   uniq' := λ s m w,
   begin
     apply c.uniq s,
     rintro (⟨⟩|⟨⟩),
     exact w walking_pair.left,
     exact w walking_pair.right,
   end, }

end bicone

/--
`has_binary_biproduct P Q` represents a particular chosen bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class has_binary_biproduct (P Q : C) :=
(bicone : binary_bicone P Q)
(is_limit : is_limit bicone.to_cone)
(is_colimit : is_colimit bicone.to_cocone)

section
variable (C)

/--
`has_binary_biproducts C` represents a particular chosen bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class has_binary_biproducts :=
(has_binary_biproduct : Π (P Q : C), has_binary_biproduct P Q)

attribute [instance, priority 100] has_binary_biproducts.has_binary_biproduct

/--
A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
def has_binary_biproducts_of_finite_biproducts [has_finite_biproducts C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ P Q,
  { bicone := (biproduct.bicone (pair P Q).obj).to_binary_bicone,
    is_limit := bicone.to_binary_bicone_is_limit (biproduct.is_limit _),
    is_colimit := bicone.to_binary_bicone_is_colimit (biproduct.is_colimit _) } }

end

variables {P Q : C}

instance has_binary_biproduct.has_limit_pair [has_binary_biproduct P Q] :
  has_limit (pair P Q) :=
{ cone := has_binary_biproduct.bicone.to_cone,
  is_limit := has_binary_biproduct.is_limit, }

instance has_binary_biproduct.has_colimit_pair [has_binary_biproduct P Q] :
  has_colimit (pair P Q) :=
{ cocone := has_binary_biproduct.bicone.to_cocone,
  is_colimit := has_binary_biproduct.is_colimit, }

@[priority 100]
instance has_limits_of_shape_walking_pair [has_binary_biproducts C] :
  has_limits_of_shape (discrete walking_pair) C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_pair F).symm }
@[priority 100]
instance has_colimits_of_shape_walking_pair [has_binary_biproducts C] :
  has_colimits_of_shape (discrete walking_pair) C :=
{ has_colimit := λ F, has_colimit_of_iso (diagram_iso_pair F) }

@[priority 100]
instance has_binary_products_of_has_binary_biproducts [has_binary_biproducts C] :
  has_binary_products C :=
⟨by apply_instance⟩

@[priority 100]
instance has_binary_coproducts_of_has_binary_biproducts [has_binary_biproducts C] :
  has_binary_coproducts C :=
⟨by apply_instance⟩

/--
The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprod_iso (X Y : C) [has_binary_biproduct X Y]  :
  limits.prod X Y ≅ limits.coprod X Y :=
eq_to_iso rfl

/-- The chosen biproduct of a pair of objects. -/
abbreviation biprod (X Y : C) [has_binary_biproduct X Y] := limit (pair X Y)

notation X ` ⊞ `:20 Y:20 := biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbreviation biprod.fst {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ X :=
limit.π (pair X Y) walking_pair.left
/-- The projection onto the second summand of a binary biproduct. -/
abbreviation biprod.snd {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ Y :=
limit.π (pair X Y) walking_pair.right
/-- The inclusion into the first summand of a binary biproduct. -/
abbreviation biprod.inl {X Y : C} [has_binary_biproduct X Y] : X ⟶ X ⊞ Y :=
colimit.ι (pair X Y) walking_pair.left
/-- The inclusion into the second summand of a binary biproduct. -/
abbreviation biprod.inr {X Y : C} [has_binary_biproduct X Y] : Y ⟶ X ⊞ Y :=
colimit.ι (pair X Y) walking_pair.right

@[simp,reassoc]
lemma biprod.inl_fst {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
has_binary_biproduct.bicone.inl_fst
@[simp,reassoc]
lemma biprod.inl_snd {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
has_binary_biproduct.bicone.inl_snd
@[simp,reassoc]
lemma biprod.inr_fst {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
has_binary_biproduct.bicone.inr_fst
@[simp,reassoc]
lemma biprod.inr_snd {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
has_binary_biproduct.bicone.inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbreviation biprod.lift {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  W ⟶ X ⊞ Y :=
limit.lift _ (binary_fan.mk f g)
/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbreviation biprod.desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  X ⊞ Y ⟶ W :=
colimit.desc _ (binary_cofan.mk f g)

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbreviation biprod.map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
lim_map (@map_pair _ _ (pair W X) (pair Y Z) f g)

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.map_iso {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ≅ Y) (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z :=
{ hom := biprod.map f.hom g.hom,
  inv := biprod.map f.inv g.inv, }

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbreviation biprod.map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
colim_map (@map_pair _ _ (pair W X) (pair Y Z) f g)

@[ext] lemma biprod.hom_ext {X Y Z : C} [has_binary_biproduct X Y] (f g : Z ⟶ X ⊞ Y)
  (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
binary_fan.is_limit.hom_ext has_binary_biproduct.is_limit h₀ h₁

@[ext] lemma biprod.hom_ext' {X Y Z : C} [has_binary_biproduct X Y] (f g : X ⊞ Y ⟶ Z)
  (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
binary_cofan.is_colimit.hom_ext has_binary_biproduct.is_colimit h₀ h₁

lemma biprod.map_eq_map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g :=
begin
  ext,
  { simp only [map_pair_left, ι_colim_map, lim_map_π, biprod.inl_fst_assoc, category.assoc],
    erw [biprod.inl_fst, category.comp_id], },
  { simp only [map_pair_left, ι_colim_map, lim_map_π, has_zero_morphisms.zero_comp,
      biprod.inl_snd_assoc, category.assoc],
    erw [biprod.inl_snd], simp, },
  { simp only [map_pair_right, biprod.inr_fst_assoc, ι_colim_map, lim_map_π,
      has_zero_morphisms.zero_comp, category.assoc],
    erw [biprod.inr_fst], simp, },
  { simp only [map_pair_right, ι_colim_map, lim_map_π, biprod.inr_snd_assoc, category.assoc],
    erw [biprod.inr_snd, category.comp_id], },
end

instance biprod.inl_mono {X Y : C} [has_binary_biproduct X Y] :
  split_mono (biprod.inl : X ⟶ X ⊞ Y) :=
{ retraction := biprod.desc (𝟙 X) (biprod.inr ≫ biprod.fst) }

instance biprod.inr_mono {X Y : C} [has_binary_biproduct X Y] :
  split_mono (biprod.inr : Y ⟶ X ⊞ Y) :=
{ retraction := biprod.desc (biprod.inl ≫ biprod.snd) (𝟙 Y)}

instance biprod.fst_epi {X Y : C} [has_binary_biproduct X Y] :
  split_epi (biprod.fst : X ⊞ Y ⟶ X) :=
{ section_ := biprod.lift (𝟙 X) (biprod.inl ≫ biprod.snd) }

instance biprod.snd_epi {X Y : C} [has_binary_biproduct X Y] :
  split_epi (biprod.snd : X ⊞ Y ⟶ Y) :=
{ section_ := biprod.lift (biprod.inr ≫ biprod.fst) (𝟙 Y) }

@[simp,reassoc]
lemma biprod.map_fst {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
by simp

@[simp,reassoc]
lemma biprod.map_snd {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
by simp

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[simp,reassoc]
lemma biprod.inl_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.inl ≫ biprod.map f g = f ≫ biprod.inl :=
begin
  rw biprod.map_eq_map',
  simp,
end

@[simp,reassoc]
lemma biprod.inr_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.inr ≫ biprod.map f g = g ≫ biprod.inr :=
begin
  rw biprod.map_eq_map',
  simp,
end

section
variables [has_binary_biproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps] def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P :=
{ hom := biprod.lift biprod.snd biprod.fst,
  inv := biprod.lift biprod.snd biprod.fst }

/--
An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P :=
{ hom := biprod.desc biprod.inr biprod.inl,
  inv := biprod.desc biprod.inr biprod.inl }

lemma biprod.braiding'_eq_braiding {P Q : C} :
  biprod.braiding' P Q = biprod.braiding P Q :=
by tidy

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc] lemma biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
  biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f :=
by tidy

@[reassoc] lemma biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
  (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f :=
by tidy

@[simp, reassoc] lemma biprod.symmetry' (P Q : C) :
  biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
@[reassoc] lemma biprod.symmetry (P Q : C) :
  (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ :=
by simp

end

-- TODO:
-- If someone is interested, they could provide the constructions:
--   has_binary_biproducts ↔ has_finite_biproducts

end category_theory.limits

namespace category_theory.limits

section preadditive
variables {C : Type u} [category.{v} C] [preadditive C]
variables {J : Type v} [fintype J] [decidable_eq J]

open category_theory.preadditive
open_locale big_operators

/--
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def has_biproduct_of_total {f : J → C} (b : bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X) :
  has_biproduct f :=
{ bicone := b,
  is_limit :=
  { lift := λ s, ∑ j, s.π.app j ≫ b.ι j,
    uniq' := λ s m h,
    begin
      erw [←category.comp_id m, ←total, comp_sum],
      apply finset.sum_congr rfl,
      intros j m,
      erw [reassoc_of (h j)],
    end,
    fac' := λ s j,
    begin
      simp only [sum_comp, category.assoc, bicone.to_cone_π_app, b.ι_π, comp_dite],
      dsimp, simp,
    end },
  is_colimit :=
  { desc := λ s, ∑ j, b.π j ≫ s.ι.app j,
    uniq' := λ s m h,
    begin
      erw [←category.id_comp m, ←total, sum_comp],
            apply finset.sum_congr rfl,
      intros j m,
      erw [category.assoc, h],
    end,
    fac' := λ s j,
    begin
      simp only [comp_sum, ←category.assoc, bicone.to_cocone_ι_app, b.ι_π, dite_comp],
      dsimp, simp,
    end } }

/-- In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
def has_biproduct.of_has_product (f : J → C) [has_product f] :
  has_biproduct f :=
has_biproduct_of_total
{ X := pi_obj f,
  π := limits.pi.π f,
  ι := λ j, pi.lift (λ j', if h : j = j' then eq_to_hom (congr_arg f h) else 0),
  ι_π := λ j j', by simp, }
(by { ext, simp [sum_comp, comp_dite] })

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
def has_biproduct.of_has_coproduct (f : J → C) [has_coproduct f] :
  has_biproduct f :=
has_biproduct_of_total
{ X := sigma_obj f,
  π := λ j, sigma.desc (λ j', if h : j' = j then eq_to_hom (congr_arg f h) else 0),
  ι := limits.sigma.ι f,
  ι_π := λ j j', by simp, }
begin
  ext,
  simp only [comp_sum, limits.cofan.mk_π_app, limits.colimit.ι_desc_assoc, eq_self_iff_true,
    limits.colimit.ι_desc, category.comp_id],
  dsimp,
  simp only [dite_comp, finset.sum_dite_eq, finset.mem_univ, if_true, category.id_comp,
    eq_to_hom_refl, limits.has_zero_morphisms.zero_comp],
end

section
variables {f : J → C} [has_biproduct f]

/--
In any preadditive category, any biproduct satsifies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp] lemma biproduct.total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
begin
  ext j j',
  simp [comp_sum, sum_comp, biproduct.ι_π, comp_dite, dite_comp],
end

lemma biproduct.lift_eq {T : C} {g : Π j, T ⟶ f j} :
  biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j :=
begin
  ext j,
  simp [sum_comp, biproduct.ι_π, comp_dite],
end

lemma biproduct.desc_eq {T : C} {g : Π j, f j ⟶ T} :
  biproduct.desc g = ∑ j, biproduct.π f j ≫ g j :=
begin
  ext j,
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp],
end

@[simp, reassoc] lemma biproduct.lift_desc {T U : C} {g : Π j, T ⟶ f j} {h : Π j, f j ⟶ U} :
  biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j :=
by simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc,
  comp_dite, dite_comp]

lemma biproduct.map_eq [has_finite_biproducts C] {f g : J → C} {h : Π j, f j ⟶ g j} :
  biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j :=
begin
  ext,
  simp [biproduct.ι_π, biproduct.ι_π_assoc, comp_sum, sum_comp, comp_dite, dite_comp],
end

end

/--
In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def has_binary_biproduct_of_total {X Y : C} (b : binary_bicone X Y)
  (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X) :
  has_binary_biproduct X Y :=
{ bicone := b,
  is_limit :=
  { lift := λ s, binary_fan.fst s ≫ b.inl +
      binary_fan.snd s ≫ b.inr,
    uniq' := λ s m h, by erw [←category.comp_id m, ←total,
      comp_add, reassoc_of (h walking_pair.left), reassoc_of (h walking_pair.right)],
    fac' := λ s j, by cases j; simp, },
  is_colimit :=
  { desc := λ s, b.fst ≫ binary_cofan.inl s +
      b.snd ≫ binary_cofan.inr s,
    uniq' := λ s m h, by erw [←category.id_comp m, ←total,
      add_comp, category.assoc, category.assoc, h walking_pair.left, h walking_pair.right],
    fac' := λ s j, by cases j; simp, } }

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
def has_binary_biproduct.of_has_binary_product (X Y : C) [has_binary_product X Y] :
  has_binary_biproduct X Y :=
has_binary_biproduct_of_total
{ X := X ⨯ Y,
  fst := category_theory.limits.prod.fst,
  snd := category_theory.limits.prod.snd,
  inl := prod.lift (𝟙 X) 0,
  inr := prod.lift 0 (𝟙 Y) }
begin
  ext; simp [add_comp],
end

/-- In a preadditive category, if all binary products exist,
    then the all binary biproducts exist. -/
def has_binary_biproducts.of_has_binary_products [has_binary_products C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ X Y, has_binary_biproduct.of_has_binary_product X Y, }

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
def has_binary_biproduct.of_has_binary_coproduct (X Y : C) [has_binary_coproduct X Y] :
  has_binary_biproduct X Y :=
has_binary_biproduct_of_total
{ X := X ⨿ Y,
  fst := coprod.desc (𝟙 X) 0,
  snd := coprod.desc 0 (𝟙 Y),
  inl := category_theory.limits.coprod.inl,
  inr := category_theory.limits.coprod.inr }
begin
  ext; simp [add_comp],
end

/-- In a preadditive category, if all binary coproducts exist,
    then the all binary biproducts exist. -/
def has_binary_biproducts.of_has_binary_coproducts [has_binary_coproducts C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ X Y, has_binary_biproduct.of_has_binary_coproduct X Y, }

section
variables {X Y : C} [has_binary_biproduct X Y]

/--
In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp] lemma biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
begin
  ext; simp [add_comp],
end

lemma biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr :=
begin
  ext; simp [add_comp],
end

lemma biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g :=
begin
  ext; simp [add_comp],
end

@[simp, reassoc] lemma biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
  biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i :=
by simp [biprod.lift_eq, biprod.desc_eq]


lemma biprod.map_eq [has_binary_biproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
  biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr :=
by apply biprod.hom_ext; apply biprod.hom_ext'; simp

end

end preadditive

end category_theory.limits
