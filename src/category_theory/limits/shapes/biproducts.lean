/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jakob von Raumer
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.kernels

/-!
# Biproducts and binary biproducts

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`category_theory.preadditive.biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation
Prior to #14046, `has_finite_biproducts` required a `decidable_eq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib), and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/

noncomputable theory

universes w w' v u

open category_theory
open category_theory.functor
open_locale classical

namespace category_theory

namespace limits

variables {J : Type w}
variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

/--
A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
@[nolint has_nonempty_instance]
structure bicone (F : J → C) :=
(X : C)
(π : Π j, X ⟶ F j)
(ι : Π j, F j ⟶ X)
(ι_π : ∀ j j', ι j ≫ π j' = if h : j = j' then eq_to_hom (congr_arg F h) else 0 . obviously)

@[simp, reassoc] lemma bicone_ι_π_self {F : J → C} (B : bicone F) (j : J) :
  B.ι j ≫ B.π j = 𝟙 (F j) :=
by simpa using B.ι_π j j

@[simp, reassoc] lemma bicone_ι_π_ne {F : J → C} (B : bicone F) {j j' : J} (h : j ≠ j') :
  B.ι j ≫ B.π j' = 0 :=
by simpa [h] using B.ι_π j j'

variables {F : J → C}

namespace bicone

local attribute [tidy] tactic.discrete_cases

/-- Extract the cone from a bicone. -/
def to_cone (B : bicone F) : cone (discrete.functor F) :=
{ X := B.X,
  π := { app := λ j, B.π j.as }, }

@[simp] lemma to_cone_X (B : bicone F) : B.to_cone.X = B.X := rfl

@[simp] lemma to_cone_π_app (B : bicone F) (j : discrete J) : B.to_cone.π.app j = B.π j.as := rfl

lemma to_cone_π_app_mk (B : bicone F) (j : J) : B.to_cone.π.app ⟨j⟩ = B.π j := rfl

/-- Extract the cocone from a bicone. -/
def to_cocone (B : bicone F) : cocone (discrete.functor F) :=
{ X := B.X,
  ι := { app := λ j, B.ι j.as }, }

@[simp] lemma to_cocone_X (B : bicone F) : B.to_cocone.X = B.X := rfl

@[simp] lemma to_cocone_ι_app (B : bicone F) (j : discrete J) : B.to_cocone.ι.app j = B.ι j.as :=
rfl

lemma to_cocone_ι_app_mk (B : bicone F) (j : J) : B.to_cocone.ι.app ⟨j⟩ = B.ι j := rfl

/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
def of_limit_cone {f : J → C} {t : cone (discrete.functor f)} (ht : is_limit t) :
  bicone f :=
{ X := t.X,
  π := λ j, t.π.app ⟨j⟩,
  ι := λ j, ht.lift (fan.mk _ (λ j', if h : j = j' then eq_to_hom (congr_arg f h) else 0)),
  ι_π := λ j j', by simp }

lemma ι_of_is_limit {f : J → C} {t : bicone f} (ht : is_limit t.to_cone) (j : J) :
  t.ι j = ht.lift (fan.mk _ (λ j', if h : j = j' then eq_to_hom (congr_arg f h) else 0)) :=
ht.hom_ext (λ j', by { rw ht.fac, discrete_cases, simp [t.ι_π] })

/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
def of_colimit_cocone {f : J → C} {t : cocone (discrete.functor f)} (ht : is_colimit t) :
  bicone f :=
{ X := t.X,
  π := λ j, ht.desc (cofan.mk _ (λ j', if h : j' = j then eq_to_hom (congr_arg f h) else 0)),
  ι := λ j, t.ι.app ⟨j⟩,
  ι_π := λ j j', by simp }

lemma π_of_is_colimit {f : J → C} {t : bicone f} (ht : is_colimit t.to_cocone) (j : J) :
  t.π j = ht.desc (cofan.mk _ (λ j', if h : j' = j then eq_to_hom (congr_arg f h) else 0)) :=
ht.hom_ext (λ j', by { rw ht.fac, discrete_cases, simp [t.ι_π] })

/-- Structure witnessing that a bicone is both a limit cone and a colimit cocone. -/
@[nolint has_nonempty_instance]
structure is_bilimit {F : J → C} (B : bicone F) :=
(is_limit : is_limit B.to_cone)
(is_colimit : is_colimit B.to_cocone)

local attribute [ext] bicone.is_bilimit

instance subsingleton_is_bilimit {f : J → C} {c : bicone f} : subsingleton c.is_bilimit :=
⟨λ h h', bicone.is_bilimit.ext _ _ (subsingleton.elim _ _) (subsingleton.elim _ _)⟩

section whisker
variables {K : Type w'}

/-- Whisker a bicone with an equivalence between the indexing types. -/
@[simps]
def whisker {f : J → C} (c : bicone f) (g : K ≃ J) : bicone (f ∘ g) :=
{ X := c.X,
  π := λ k, c.π (g k),
  ι := λ k, c.ι (g k),
  ι_π := λ k k',
  begin
    simp only [c.ι_π],
    split_ifs with h h' h'; simp [equiv.apply_eq_iff_eq g] at h h'; tauto
  end }

local attribute [tidy] tactic.discrete_cases

/-- Taking the cone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cone and postcomposing with a suitable isomorphism. -/
def whisker_to_cone {f : J → C} (c : bicone f) (g : K ≃ J) :
  (c.whisker g).to_cone ≅ (cones.postcompose (discrete.functor_comp f g).inv).obj
    (c.to_cone.whisker (discrete.functor (discrete.mk ∘ g))) :=
cones.ext (iso.refl _) (by tidy)

/-- Taking the cocone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cocone and precomposing with a suitable isomorphism. -/
def whisker_to_cocone {f : J → C} (c : bicone f) (g : K ≃ J) :
  (c.whisker g).to_cocone ≅ (cocones.precompose (discrete.functor_comp f g).hom).obj
    (c.to_cocone.whisker (discrete.functor (discrete.mk ∘ g))) :=
cocones.ext (iso.refl _) (by tidy)

/-- Whiskering a bicone with an equivalence between types preserves being a bilimit bicone. -/
def whisker_is_bilimit_iff {f : J → C} (c : bicone f) (g : K ≃ J) :
  (c.whisker g).is_bilimit ≃ c.is_bilimit :=
begin
  refine equiv_of_subsingleton_of_subsingleton (λ hc, ⟨_, _⟩) (λ hc, ⟨_, _⟩),
  { let := is_limit.of_iso_limit hc.is_limit (bicone.whisker_to_cone c g),
    let := (is_limit.postcompose_hom_equiv (discrete.functor_comp f g).symm _) this,
    exact is_limit.of_whisker_equivalence (discrete.equivalence g) this },
  { let := is_colimit.of_iso_colimit hc.is_colimit (bicone.whisker_to_cocone c g),
    let := (is_colimit.precompose_hom_equiv (discrete.functor_comp f g) _) this,
    exact is_colimit.of_whisker_equivalence (discrete.equivalence g) this },
  { apply is_limit.of_iso_limit _ (bicone.whisker_to_cone c g).symm,
    apply (is_limit.postcompose_hom_equiv (discrete.functor_comp f g).symm _).symm _,
    exact is_limit.whisker_equivalence hc.is_limit (discrete.equivalence g) },
  { apply is_colimit.of_iso_colimit _ (bicone.whisker_to_cocone c g).symm,
    apply (is_colimit.precompose_hom_equiv (discrete.functor_comp f g) _).symm _,
    exact is_colimit.whisker_equivalence hc.is_colimit (discrete.equivalence g) }
end

end whisker

end bicone

/--
A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_nonempty_instance]
structure limit_bicone (F : J → C) :=
(bicone : bicone F)
(is_bilimit : bicone.is_bilimit)

/--
`has_biproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class has_biproduct (F : J → C) : Prop :=
mk' :: (exists_biproduct : nonempty (limit_bicone F))

lemma has_biproduct.mk {F : J → C} (d : limit_bicone F) : has_biproduct F :=
⟨nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `biproduct_data F` from `has_biproduct F`. -/
def get_biproduct_data (F : J → C) [has_biproduct F] : limit_bicone F :=
classical.choice has_biproduct.exists_biproduct

/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
def biproduct.bicone (F : J → C) [has_biproduct F] : bicone F :=
(get_biproduct_data F).bicone

/-- `biproduct.bicone F` is a bilimit bicone. -/
def biproduct.is_bilimit (F : J → C) [has_biproduct F] : (biproduct.bicone F).is_bilimit :=
(get_biproduct_data F).is_bilimit

/-- `biproduct.bicone F` is a limit cone. -/
def biproduct.is_limit (F : J → C) [has_biproduct F] : is_limit (biproduct.bicone F).to_cone :=
(get_biproduct_data F).is_bilimit.is_limit

/-- `biproduct.bicone F` is a colimit cocone. -/
def biproduct.is_colimit (F : J → C) [has_biproduct F] :
  is_colimit (biproduct.bicone F).to_cocone :=
(get_biproduct_data F).is_bilimit.is_colimit

@[priority 100]
instance has_product_of_has_biproduct [has_biproduct F] : has_product F :=
has_limit.mk { cone := (biproduct.bicone F).to_cone,
  is_limit := biproduct.is_limit F, }

@[priority 100]
instance has_coproduct_of_has_biproduct [has_biproduct F] : has_coproduct F :=
has_colimit.mk { cocone := (biproduct.bicone F).to_cocone,
  is_colimit := biproduct.is_colimit F, }

variables (J C)

/--
`C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class has_biproducts_of_shape : Prop :=
(has_biproduct : ∀ F : J → C, has_biproduct F)

attribute [instance, priority 100] has_biproducts_of_shape.has_biproduct

/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type. -/
class has_finite_biproducts : Prop :=
(out [] : ∀ n, has_biproducts_of_shape (fin n) C)

variables {J}

lemma has_biproducts_of_shape_of_equiv {K : Type w'} [has_biproducts_of_shape K C] (e : J ≃ K) :
  has_biproducts_of_shape J C :=
⟨λ F, let ⟨⟨h⟩⟩ := has_biproducts_of_shape.has_biproduct (F ∘ e.symm), ⟨c, hc⟩ := h
  in has_biproduct.mk $ by simpa only [(∘), e.symm_apply_apply]
    using limit_bicone.mk (c.whisker e) ((c.whisker_is_bilimit_iff _).2 hc)⟩

@[priority 100] instance has_biproducts_of_shape_finite [has_finite_biproducts C] [finite J] :
  has_biproducts_of_shape J C :=
begin
  rcases finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩,
  haveI := has_finite_biproducts.out C n,
  exact has_biproducts_of_shape_of_equiv C e
end

@[priority 100]
instance has_finite_products_of_has_finite_biproducts [has_finite_biproducts C] :
  has_finite_products C :=
{ out := λ n, ⟨λ F, has_limit_of_iso discrete.nat_iso_functor.symm⟩ }

@[priority 100]
instance has_finite_coproducts_of_has_finite_biproducts [has_finite_biproducts C] :
  has_finite_coproducts C :=
{ out := λ n, ⟨λ F, has_colimit_of_iso discrete.nat_iso_functor⟩ }

variables {J C}

/--
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproduct_iso (F : J → C) [has_biproduct F] :
  limits.pi_obj F ≅ limits.sigma_obj F :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (biproduct.is_limit F)).trans $
  is_colimit.cocone_point_unique_up_to_iso (biproduct.is_colimit F) (colimit.is_colimit _)

end limits

namespace limits
variables {J : Type w}
variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbreviation biproduct (f : J → C) [has_biproduct f] : C :=
(biproduct.bicone f).X

notation `⨁ ` f:20 := biproduct f

/-- The projection onto a summand of a biproduct. -/
abbreviation biproduct.π (f : J → C) [has_biproduct f] (b : J) : ⨁ f ⟶ f b :=
(biproduct.bicone f).π b

@[simp]
lemma biproduct.bicone_π (f : J → C) [has_biproduct f] (b : J) :
  (biproduct.bicone f).π b = biproduct.π f b := rfl

/-- The inclusion into a summand of a biproduct. -/
abbreviation biproduct.ι (f : J → C) [has_biproduct f] (b : J) : f b ⟶ ⨁ f :=
(biproduct.bicone f).ι b

@[simp]
lemma biproduct.bicone_ι (f : J → C) [has_biproduct f] (b : J) :
  (biproduct.bicone f).ι b = biproduct.ι f b := rfl

/-- Note that as this lemma has a `if` in the statement, we include a `decidable_eq` argument.
This means you may not be able to `simp` using this lemma unless you `open_locale classical`. -/
@[reassoc]
lemma biproduct.ι_π [decidable_eq J] (f : J → C) [has_biproduct f] (j j' : J) :
  biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eq_to_hom (congr_arg f h) else 0 :=
by convert (biproduct.bicone f).ι_π j j'

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
(biproduct.is_limit f).lift (fan.mk P p)
/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbreviation biproduct.desc
  {f : J → C} [has_biproduct f] {P : C} (p : Π b, f b ⟶ P) : ⨁ f ⟶ P :=
(biproduct.is_colimit f).desc (cofan.mk P p)

@[simp, reassoc]
lemma biproduct.lift_π {f : J → C} [has_biproduct f] {P : C} (p : Π b, P ⟶ f b) (j : J) :
  biproduct.lift p ≫ biproduct.π f j = p j :=
(biproduct.is_limit f).fac _ ⟨j⟩

@[simp, reassoc]
lemma biproduct.ι_desc {f : J → C} [has_biproduct f] {P : C} (p : Π b, f b ⟶ P) (j : J) :
  biproduct.ι f j ≫ biproduct.desc p = p j :=
(biproduct.is_colimit f).fac _ ⟨j⟩

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbreviation biproduct.map {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
is_limit.map (biproduct.bicone f).to_cone (biproduct.is_limit g)
  (discrete.nat_trans (λ j, p j.as))

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbreviation biproduct.map' {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
is_colimit.map (biproduct.is_colimit f) (biproduct.bicone g).to_cocone
  (discrete.nat_trans (λ j, p j.as))

@[ext] lemma biproduct.hom_ext {f : J → C} [has_biproduct f]
  {Z : C} (g h : Z ⟶ ⨁ f)
  (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
(biproduct.is_limit f).hom_ext (λ j, w j.as)

@[ext] lemma biproduct.hom_ext' {f : J → C} [has_biproduct f]
  {Z : C} (g h : ⨁ f ⟶ Z)
  (w : ∀ j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
(biproduct.is_colimit f).hom_ext (λ j, w j.as)

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biproduct.iso_product (f : J → C) [has_biproduct f] : ⨁ f ≅ ∏ f :=
is_limit.cone_point_unique_up_to_iso (biproduct.is_limit f) (limit.is_limit _)

@[simp] lemma biproduct.iso_product_hom {f : J → C} [has_biproduct f] :
  (biproduct.iso_product f).hom = pi.lift (biproduct.π f) :=
limit.hom_ext $ λ j, by simp [biproduct.iso_product]

@[simp] lemma biproduct.iso_product_inv {f : J → C} [has_biproduct f] :
  (biproduct.iso_product f).inv = biproduct.lift (pi.π f) :=
biproduct.hom_ext _ _ $ λ j, by simp [iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biproduct.iso_coproduct (f : J → C) [has_biproduct f] : ⨁ f ≅ ∐ f :=
is_colimit.cocone_point_unique_up_to_iso (biproduct.is_colimit f) (colimit.is_colimit _)

@[simp] lemma biproduct.iso_coproduct_inv {f : J → C} [has_biproduct f] :
  (biproduct.iso_coproduct f).inv = sigma.desc (biproduct.ι f) :=
colimit.hom_ext $ λ j, by simp [biproduct.iso_coproduct]

@[simp] lemma biproduct.iso_coproduct_hom {f : J → C} [has_biproduct f] :
  (biproduct.iso_coproduct f).hom = biproduct.desc (sigma.ι f) :=
biproduct.hom_ext' _ _ $ λ j, by simp [← iso.eq_comp_inv]

lemma biproduct.map_eq_map' {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π b, f b ⟶ g b) : biproduct.map p = biproduct.map' p :=
begin
  ext j j',
  simp only [discrete.nat_trans_app, limits.is_colimit.ι_map, limits.is_limit.map_π, category.assoc,
    ←bicone.to_cone_π_app_mk, ←biproduct.bicone_π, ←bicone.to_cocone_ι_app_mk, ←biproduct.bicone_ι],
  simp only [biproduct.bicone_ι, biproduct.bicone_π, bicone.to_cocone_ι_app, bicone.to_cone_π_app],
  dsimp,
  rw [biproduct.ι_π_assoc, biproduct.ι_π],
  split_ifs,
  { subst h, rw [eq_to_hom_refl, category.id_comp], erw category.comp_id, },
  { simp, },
end

@[simp, reassoc]
lemma biproduct.map_π {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π j, f j ⟶ g j) (j : J) :
  biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
limits.is_limit.map_π _ _ _ (discrete.mk j)

@[simp, reassoc]
lemma biproduct.ι_map {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π j, f j ⟶ g j) (j : J) :
  biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j :=
begin
  rw biproduct.map_eq_map',
  convert limits.is_colimit.ι_map _ _ _ (discrete.mk j); refl
end

@[simp, reassoc]
lemma biproduct.map_desc {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π j, f j ⟶ g j) {P : C} (k : Π j, g j ⟶ P) :
  biproduct.map p ≫ biproduct.desc k = biproduct.desc (λ j, p j ≫ k j) :=
by { ext, simp, }

@[simp, reassoc]
lemma biproduct.lift_map {f g : J → C} [has_biproduct f] [has_biproduct g]
  {P : C} (k : Π j, P ⟶ f j) (p : Π j, f j ⟶ g j)  :
  biproduct.lift k ≫ biproduct.map p = biproduct.lift (λ j, k j ≫ p j) :=
by { ext, simp, }

/-- Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
def biproduct.map_iso {f g : J → C} [has_biproduct f] [has_biproduct g]
  (p : Π b, f b ≅ g b) : ⨁ f ≅ ⨁ g :=
{ hom := biproduct.map (λ b, (p b).hom),
  inv := biproduct.map (λ b, (p b).inv), }

section π_kernel

section
variables (f : J → C) [has_biproduct f]
variables (p : J → Prop) [has_biproduct (subtype.restrict p f)]

/-- The canonical morphism from the biproduct over a restricted index type to the biproduct of
the full index type. -/
def biproduct.from_subtype : ⨁ subtype.restrict p f ⟶ ⨁ f :=
biproduct.desc $ λ j, biproduct.ι _ _

/-- The canonical morphism from a biproduct to the biproduct over a restriction of its index
type. -/
def biproduct.to_subtype : ⨁ f ⟶ ⨁ subtype.restrict p f :=
biproduct.lift $ λ j, biproduct.π _ _

@[simp, reassoc]
lemma biproduct.from_subtype_π [decidable_pred p] (j : J) :
  biproduct.from_subtype f p ≫ biproduct.π f j =
    if h : p j then biproduct.π (subtype.restrict p f) ⟨j, h⟩ else 0 :=
begin
  ext i,
  rw [biproduct.from_subtype, biproduct.ι_desc_assoc, biproduct.ι_π],
  by_cases h : p j,
  { rw [dif_pos h, biproduct.ι_π],
    split_ifs with h₁ h₂ h₂,
    exacts [rfl, false.elim (h₂ (subtype.ext h₁)),
      false.elim (h₁ (congr_arg subtype.val h₂)), rfl] },
  { rw [dif_neg h, dif_neg (show (i : J) ≠ j, from λ h₂, h (h₂ ▸ i.2)), comp_zero] }
end

lemma biproduct.from_subtype_eq_lift [decidable_pred p] : biproduct.from_subtype f p =
    biproduct.lift (λ j, if h : p j then biproduct.π (subtype.restrict p f) ⟨j, h⟩ else 0) :=
biproduct.hom_ext _ _ (by simp)

@[simp, reassoc]
lemma biproduct.from_subtype_π_subtype (j : subtype p) :
  biproduct.from_subtype f p ≫ biproduct.π f j = biproduct.π (subtype.restrict p f) j :=
begin
  ext i,
  rw [biproduct.from_subtype, biproduct.ι_desc_assoc, biproduct.ι_π, biproduct.ι_π],
  split_ifs with h₁ h₂ h₂,
  exacts [rfl, false.elim (h₂ (subtype.ext h₁)), false.elim (h₁ (congr_arg subtype.val h₂)), rfl]
end

@[simp, reassoc]
lemma biproduct.to_subtype_π (j : subtype p) :
  biproduct.to_subtype f p ≫ biproduct.π (subtype.restrict p f) j = biproduct.π f j :=
biproduct.lift_π _ _

@[simp, reassoc]
lemma biproduct.ι_to_subtype [decidable_pred p] (j : J) :
  biproduct.ι f j ≫ biproduct.to_subtype f p =
    if h : p j then biproduct.ι (subtype.restrict p f) ⟨j, h⟩ else 0 :=
begin
  ext i,
  rw [biproduct.to_subtype, category.assoc, biproduct.lift_π, biproduct.ι_π],
  by_cases h : p j,
  { rw [dif_pos h, biproduct.ι_π],
    split_ifs with h₁ h₂ h₂,
    exacts [rfl, false.elim (h₂ (subtype.ext h₁)),
      false.elim (h₁ (congr_arg subtype.val h₂)), rfl] },
  { rw [dif_neg h, dif_neg (show j ≠ i, from λ h₂, h (h₂.symm ▸ i.2)), zero_comp] }
end

lemma biproduct.to_subtype_eq_desc [decidable_pred p] : biproduct.to_subtype f p =
  biproduct.desc (λ j, if h : p j then biproduct.ι (subtype.restrict p f) ⟨j, h⟩ else 0) :=
biproduct.hom_ext' _ _ (by simp)

@[simp, reassoc]
lemma biproduct.ι_to_subtype_subtype (j : subtype p) :
  biproduct.ι f j ≫ biproduct.to_subtype f p = biproduct.ι (subtype.restrict p f) j :=
begin
  ext i,
  rw [biproduct.to_subtype, category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π],
  split_ifs with h₁ h₂ h₂,
  exacts [rfl, false.elim (h₂ (subtype.ext h₁)), false.elim (h₁ (congr_arg subtype.val h₂)), rfl]
end

@[simp, reassoc]
lemma biproduct.ι_from_subtype (j : subtype p) :
  biproduct.ι (subtype.restrict p f) j ≫ biproduct.from_subtype f p = biproduct.ι f j :=
biproduct.ι_desc _ _

@[simp, reassoc]
lemma biproduct.from_subtype_to_subtype :
  biproduct.from_subtype f p ≫ biproduct.to_subtype f p = 𝟙 (⨁ subtype.restrict p f) :=
begin
  refine biproduct.hom_ext _ _ (λ j, _),
  rw [category.assoc, biproduct.to_subtype_π, biproduct.from_subtype_π_subtype, category.id_comp]
end

@[simp, reassoc]
lemma biproduct.to_subtype_from_subtype [decidable_pred p] :
  biproduct.to_subtype f p ≫ biproduct.from_subtype f p =
    biproduct.map (λ j, if p j then 𝟙 (f j) else 0) :=
begin
  ext1 i,
  by_cases h : p i,
  { simp [h], congr },
  { simp [h] }
end

end

section
variables (f : J → C) (i : J) [has_biproduct f] [has_biproduct (subtype.restrict (λ j, j ≠ i) f)]

/-- The kernel of `biproduct.π f i` is the inclusion from the biproduct which omits `i`
from the index set `J` into the biproduct over `J`. -/
def biproduct.is_limit_from_subtype : is_limit
  (kernel_fork.of_ι (biproduct.from_subtype f (λ j, j ≠ i))
    (by simp) : kernel_fork (biproduct.π f i)) :=
fork.is_limit.mk' _ $ λ s,
⟨s.ι ≫ biproduct.to_subtype _ _,
 begin
   ext j,
   rw [kernel_fork.ι_of_ι, category.assoc, category.assoc,
     biproduct.to_subtype_from_subtype_assoc, biproduct.map_π],
   rcases em (i = j) with (rfl|h),
   { rw [if_neg (not_not.2 rfl), comp_zero, comp_zero, kernel_fork.condition] },
   { rw [if_pos (ne.symm h), category.comp_id], }
 end,
 begin
   intros m hm,
   rw [← hm, kernel_fork.ι_of_ι, category.assoc, biproduct.from_subtype_to_subtype],
   exact (category.comp_id _).symm
 end⟩

instance : has_kernel (biproduct.π f i) :=
has_limit.mk ⟨_, biproduct.is_limit_from_subtype f i⟩

/-- The kernel of `biproduct.π f i` is `⨁ subtype.restrict {i}ᶜ f`. -/
@[simps]
def kernel_biproduct_π_iso : kernel (biproduct.π f i) ≅ ⨁ subtype.restrict (λ j, j ≠ i) f :=
limit.iso_limit_cone ⟨_, biproduct.is_limit_from_subtype f i⟩

/-- The cokernel of `biproduct.ι f i` is the projection from the biproduct over the index set `J`
onto the biproduct omitting `i`. -/
def biproduct.is_colimit_to_subtype : is_colimit
  (cokernel_cofork.of_π (biproduct.to_subtype f (λ j, j ≠ i))
    (by simp) : cokernel_cofork (biproduct.ι f i)) :=
cofork.is_colimit.mk' _ $ λ s,
⟨biproduct.from_subtype _ _ ≫ s.π,
 begin
   ext j,
   rw [cokernel_cofork.π_of_π, biproduct.to_subtype_from_subtype_assoc,
     biproduct.ι_map_assoc],
   rcases em (i = j) with (rfl|h),
   { rw [if_neg (not_not.2 rfl), zero_comp, cokernel_cofork.condition] },
   { rw [if_pos (ne.symm h), category.id_comp], }
 end,
 begin
   intros m hm,
   rw [← hm, cokernel_cofork.π_of_π, ← category.assoc, biproduct.from_subtype_to_subtype],
   exact (category.id_comp _).symm
 end⟩

instance : has_cokernel (biproduct.ι f i) :=
has_colimit.mk ⟨_, biproduct.is_colimit_to_subtype f i⟩

/-- The cokernel of `biproduct.ι f i` is `⨁ subtype.restrict {i}ᶜ f`. -/
@[simps]
def cokernel_biproduct_ι_iso : cokernel (biproduct.ι f i) ≅ ⨁ subtype.restrict (λ j, j ≠ i) f :=
colimit.iso_colimit_cocone ⟨_, biproduct.is_colimit_to_subtype f i⟩

end

section
open_locale classical

-- Per #15067, we only allow indexing in `Type 0` here.
variables {K : Type} [fintype K] [has_finite_biproducts C] (f : K → C)

/-- The limit cone exhibiting `⨁ subtype.restrict pᶜ f` as the kernel of
`biproduct.to_subtype f p` -/
@[simps]
def kernel_fork_biproduct_to_subtype (p : set K) :
  limit_cone (parallel_pair (biproduct.to_subtype f p) 0) :=
{ cone := kernel_fork.of_ι (biproduct.from_subtype f pᶜ) begin
    ext j k,
    simp only [biproduct.ι_from_subtype_assoc, biproduct.ι_to_subtype, comp_zero, zero_comp],
    erw [dif_neg j.2],
    simp only [zero_comp],
  end,
  is_limit := kernel_fork.is_limit.of_ι _ _ (λ W g h, g ≫ biproduct.to_subtype f pᶜ)
    begin
      intros W' g' w,
      ext j,
      simp only [category.assoc, biproduct.to_subtype_from_subtype, pi.compl_apply,
        biproduct.map_π],
      split_ifs,
      { simp, },
      { replace w := w =≫ biproduct.π _ ⟨j, not_not.mp h⟩, simpa using w.symm, },
    end
    (by tidy), }

instance (p : set K) : has_kernel (biproduct.to_subtype f p) :=
has_limit.mk (kernel_fork_biproduct_to_subtype f p)

/-- The kernel of `biproduct.to_subtype f p` is `⨁ subtype.restrict pᶜ f`. -/
@[simps]
def kernel_biproduct_to_subtype_iso (p : set K) :
  kernel (biproduct.to_subtype f p) ≅ ⨁ subtype.restrict pᶜ f :=
limit.iso_limit_cone (kernel_fork_biproduct_to_subtype f p)

/-- The colimit cocone exhibiting `⨁ subtype.restrict pᶜ f` as the cokernel of
`biproduct.from_subtype f p` -/
@[simps]
def cokernel_cofork_biproduct_from_subtype (p : set K) :
  colimit_cocone (parallel_pair (biproduct.from_subtype f p) 0) :=
{ cocone := cokernel_cofork.of_π (biproduct.to_subtype f pᶜ) begin
    ext j k,
    simp only [pi.compl_apply, biproduct.ι_from_subtype_assoc, biproduct.ι_to_subtype,
      comp_zero, zero_comp],
    rw [dif_neg],
    simp only [zero_comp],
    exact not_not.mpr j.2,
  end,
  is_colimit := cokernel_cofork.is_colimit.of_π _ _ (λ W g h, biproduct.from_subtype f pᶜ ≫ g)
    begin
      intros W' g' w,
      ext j,
      simp only [biproduct.to_subtype_from_subtype_assoc, pi.compl_apply, biproduct.ι_map_assoc],
      split_ifs,
      { simp, },
      { replace w := biproduct.ι _ (⟨j, not_not.mp h⟩ : p) ≫= w, simpa using w.symm, },
    end
    (by tidy), }

instance (p : set K) : has_cokernel (biproduct.from_subtype f p) :=
has_colimit.mk (cokernel_cofork_biproduct_from_subtype f p)

/-- The cokernel of `biproduct.from_subtype f p` is `⨁ subtype.restrict pᶜ f`. -/
@[simps]
def cokernel_biproduct_from_subtype_iso (p : set K) :
  cokernel (biproduct.from_subtype f p) ≅ ⨁ subtype.restrict pᶜ f :=
colimit.iso_colimit_cocone (cokernel_cofork_biproduct_from_subtype f p)

end

end π_kernel

end limits

namespace limits

section finite_biproducts

variables {J : Type} [fintype J] {K : Type} [fintype K]
  {C : Type u} [category.{v} C] [has_zero_morphisms C] [has_finite_biproducts C]
  {f : J → C} {g : K → C}

/--
Convert a (dependently typed) matrix to a morphism of biproducts.
-/
def biproduct.matrix (m : Π j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
biproduct.desc (λ j, biproduct.lift (λ k, m j k))

@[simp, reassoc]
lemma biproduct.matrix_π (m : Π j k, f j ⟶ g k) (k : K) :
  biproduct.matrix m ≫ biproduct.π g k = biproduct.desc (λ j, m j k) :=
by { ext, simp [biproduct.matrix], }

@[simp, reassoc]
lemma biproduct.ι_matrix (m : Π j k, f j ⟶ g k) (j : J) :
  biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift (λ k, m j k) :=
by { ext, simp [biproduct.matrix], }

/--
Extract the matrix components from a morphism of biproducts.
-/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp] lemma biproduct.matrix_components (m : Π j k, f j ⟶ g k) (j : J) (k : K) :
  biproduct.components (biproduct.matrix m) j k = m j k :=
by simp [biproduct.components]

@[simp] lemma biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) :
  biproduct.matrix (λ j k, biproduct.components m j k) = m :=
by { ext, simp [biproduct.components], }

/-- Morphisms between direct sums are matrices. -/
@[simps]
def biproduct.matrix_equiv : (⨁ f ⟶ ⨁ g) ≃ (Π j k, f j ⟶ g k) :=
{ to_fun := biproduct.components,
  inv_fun := biproduct.matrix,
  left_inv := biproduct.components_matrix,
  right_inv := λ m, by { ext, apply biproduct.matrix_components } }

end finite_biproducts

variables {J : Type w} {C : Type u} [category.{v} C] [has_zero_morphisms C]

instance biproduct.ι_mono (f : J → C) [has_biproduct f] (b : J) :
  is_split_mono (biproduct.ι f b) := is_split_mono.mk'
{ retraction := biproduct.desc $ pi.single b _ }

instance biproduct.π_epi (f : J → C) [has_biproduct f] (b : J) :
  is_split_epi (biproduct.π f b) := is_split_epi.mk'
{ section_ := biproduct.lift $ pi.single b _ }

/-- Auxiliary lemma for `biproduct.unique_up_to_iso`. -/
lemma biproduct.cone_point_unique_up_to_iso_hom (f : J → C) [has_biproduct f] {b : bicone f}
  (hb : b.is_bilimit) :
  (hb.is_limit.cone_point_unique_up_to_iso (biproduct.is_limit _)).hom = biproduct.lift b.π :=
rfl

/-- Auxiliary lemma for `biproduct.unique_up_to_iso`. -/
lemma biproduct.cone_point_unique_up_to_iso_inv (f : J → C) [has_biproduct f] {b : bicone f}
  (hb : b.is_bilimit) :
  (hb.is_limit.cone_point_unique_up_to_iso (biproduct.is_limit _)).inv = biproduct.desc b.ι :=
begin
  refine biproduct.hom_ext' _ _ (λ j, hb.is_limit.hom_ext (λ j', _)),
  discrete_cases,
  rw [category.assoc, is_limit.cone_point_unique_up_to_iso_inv_comp, bicone.to_cone_π_app,
    biproduct.bicone_π, biproduct.ι_desc, biproduct.ι_π, b.to_cone_π_app, b.ι_π]
end

/-- Biproducts are unique up to isomorphism. This already follows because bilimits are limits,
    but in the case of biproducts we can give an isomorphism with particularly nice definitional
    properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are inverses of each
    other. -/
@[simps]
def biproduct.unique_up_to_iso (f : J → C) [has_biproduct f] {b : bicone f} (hb : b.is_bilimit) :
  b.X ≅ ⨁ f :=
{ hom := biproduct.lift b.π,
  inv := biproduct.desc b.ι,
  hom_inv_id' := by rw [← biproduct.cone_point_unique_up_to_iso_hom f hb,
    ← biproduct.cone_point_unique_up_to_iso_inv f hb, iso.hom_inv_id],
  inv_hom_id' := by rw [← biproduct.cone_point_unique_up_to_iso_hom f hb,
    ← biproduct.cone_point_unique_up_to_iso_inv f hb, iso.inv_hom_id] }

variables (C)

/-- A category with finite biproducts has a zero object. -/
@[priority 100] -- see Note [lower instance priority]
instance has_zero_object_of_has_finite_biproducts [has_finite_biproducts C] : has_zero_object C :=
by { refine ⟨⟨biproduct empty.elim, λ X, ⟨⟨⟨0⟩, _⟩⟩, λ X, ⟨⟨⟨0⟩, _⟩⟩⟩⟩, tidy, }

section
variables {C} [unique J] (f : J → C)

/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
def limit_bicone_of_unique : limit_bicone f :=
{ bicone :=
  { X := f default,
    π := λ j, eq_to_hom (by congr),
    ι := λ j, eq_to_hom (by congr), },
  is_bilimit :=
  { is_limit := (limit_cone_of_unique f).is_limit,
    is_colimit := (colimit_cocone_of_unique f).is_colimit, }, }

@[priority 100] instance has_biproduct_unique : has_biproduct f :=
has_biproduct.mk (limit_bicone_of_unique f)

/-- A biproduct over a index type with exactly one term is just the object over that term. -/
@[simps]
def biproduct_unique_iso : ⨁ f ≅ f default :=
(biproduct.unique_up_to_iso _ (limit_bicone_of_unique f).is_bilimit).symm

end

variables {C}

/--
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
@[nolint has_nonempty_instance]
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
  c.to_cone.π.app ⟨walking_pair.left⟩ = c.fst := rfl
@[simp]
lemma to_cone_π_app_right (c : binary_bicone P Q) :
  c.to_cone.π.app ⟨walking_pair.right⟩ = c.snd := rfl
@[simp]
lemma binary_fan_fst_to_cone (c : binary_bicone P Q) : binary_fan.fst c.to_cone = c.fst := rfl
@[simp]
lemma binary_fan_snd_to_cone (c : binary_bicone P Q) : binary_fan.snd c.to_cone = c.snd := rfl

/-- Extract the cocone from a binary bicone. -/
def to_cocone (c : binary_bicone P Q) : cocone (pair P Q) :=
binary_cofan.mk c.inl c.inr

@[simp]
lemma to_cocone_X (c : binary_bicone P Q) :
  c.to_cocone.X = c.X := rfl

@[simp]
lemma to_cocone_ι_app_left (c : binary_bicone P Q) :
  c.to_cocone.ι.app ⟨walking_pair.left⟩ = c.inl := rfl
@[simp]
lemma to_cocone_ι_app_right (c : binary_bicone P Q) :
  c.to_cocone.ι.app ⟨walking_pair.right⟩ = c.inr := rfl
@[simp]
lemma binary_cofan_inl_to_cocone (c : binary_bicone P Q) : binary_cofan.inl c.to_cocone = c.inl :=
rfl
@[simp]
lemma binary_cofan_inr_to_cocone (c : binary_bicone P Q) : binary_cofan.inr c.to_cocone = c.inr :=
rfl

instance (c : binary_bicone P Q) : is_split_mono c.inl :=
is_split_mono.mk' { retraction := c.fst, id' := c.inl_fst }

instance (c : binary_bicone P Q) : is_split_mono c.inr :=
is_split_mono.mk'  { retraction := c.snd, id' := c.inr_snd }

instance (c : binary_bicone P Q) : is_split_epi c.fst :=
is_split_epi.mk' { section_ := c.inl, id' := c.inl_fst }

instance (c : binary_bicone P Q) : is_split_epi c.snd :=
is_split_epi.mk' { section_ := c.inr, id' := c.inr_snd }

/-- Convert a `binary_bicone` into a `bicone` over a pair. -/
@[simps]
def to_bicone {X Y : C} (b : binary_bicone X Y) : bicone (pair_function X Y) :=
{ X := b.X,
  π := λ j, walking_pair.cases_on j b.fst b.snd,
  ι := λ j, walking_pair.cases_on j b.inl b.inr,
  ι_π := λ j j', by { rcases j with ⟨⟩; rcases j' with ⟨⟩, tidy } }

/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
def to_bicone_is_limit {X Y : C} (b : binary_bicone X Y) :
  is_limit (b.to_bicone.to_cone) ≃ is_limit (b.to_cone) :=
is_limit.equiv_iso_limit $ cones.ext (iso.refl _) (λ j, by { cases j, tidy })

/-- A binary bicone is a colimit cocone if and only if the corresponding bicone is a colimit
    cocone. -/
def to_bicone_is_colimit {X Y : C} (b : binary_bicone X Y) :
  is_colimit (b.to_bicone.to_cocone) ≃ is_colimit (b.to_cocone) :=
is_colimit.equiv_iso_colimit $ cocones.ext (iso.refl _) (λ j, by { cases j, tidy })

end binary_bicone

namespace bicone

/-- Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simps]
def to_binary_bicone {X Y : C} (b : bicone (pair_function X Y)) : binary_bicone X Y :=
{ X := b.X,
  fst := b.π walking_pair.left,
  snd := b.π walking_pair.right,
  inl := b.ι walking_pair.left,
  inr := b.ι walking_pair.right,
  inl_fst' := by { simp [bicone.ι_π], refl, },
  inr_fst' := by simp [bicone.ι_π],
  inl_snd' := by simp [bicone.ι_π],
  inr_snd' := by { simp [bicone.ι_π], refl, }, }

/-- A bicone over a pair is a limit cone if and only if the corresponding binary bicone is a limit
    cone.  -/
def to_binary_bicone_is_limit {X Y : C} (b : bicone (pair_function X Y)) :
  is_limit (b.to_binary_bicone.to_cone) ≃ is_limit (b.to_cone) :=
is_limit.equiv_iso_limit $ cones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩; tidy })

/-- A bicone over a pair is a colimit cocone if and only if the corresponding binary bicone is a
    colimit cocone. -/
def to_binary_bicone_is_colimit {X Y : C} (b : bicone (pair_function X Y)) :
  is_colimit (b.to_binary_bicone.to_cocone) ≃ is_colimit (b.to_cocone) :=
is_colimit.equiv_iso_colimit $ cocones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩; tidy })

end bicone

/-- Structure witnessing that a binary bicone is a limit cone and a limit cocone. -/
@[nolint has_nonempty_instance]
structure binary_bicone.is_bilimit {P Q : C} (b : binary_bicone P Q) :=
(is_limit : is_limit b.to_cone)
(is_colimit : is_colimit b.to_cocone)

/-- A binary bicone is a bilimit bicone if and only if the corresponding bicone is a bilimit. -/
def binary_bicone.to_bicone_is_bilimit {X Y : C} (b : binary_bicone X Y) :
  b.to_bicone.is_bilimit ≃ b.is_bilimit :=
{ to_fun := λ h, ⟨b.to_bicone_is_limit h.is_limit, b.to_bicone_is_colimit h.is_colimit⟩,
  inv_fun := λ h, ⟨b.to_bicone_is_limit.symm h.is_limit, b.to_bicone_is_colimit.symm h.is_colimit⟩,
  left_inv := λ ⟨h, h'⟩, by { dsimp only, simp },
  right_inv := λ ⟨h, h'⟩, by { dsimp only, simp } }

/-- A bicone over a pair is a bilimit bicone if and only if the corresponding binary bicone is a
    bilimit. -/
def bicone.to_binary_bicone_is_bilimit {X Y : C} (b : bicone (pair_function X Y)) :
  b.to_binary_bicone.is_bilimit ≃ b.is_bilimit :=
{ to_fun := λ h, ⟨b.to_binary_bicone_is_limit h.is_limit,
    b.to_binary_bicone_is_colimit h.is_colimit⟩,
  inv_fun := λ h, ⟨b.to_binary_bicone_is_limit.symm h.is_limit,
    b.to_binary_bicone_is_colimit.symm h.is_colimit⟩,
  left_inv := λ ⟨h, h'⟩, by { dsimp only, simp },
  right_inv := λ ⟨h, h'⟩, by { dsimp only, simp } }

/--
A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_nonempty_instance]
structure binary_biproduct_data (P Q : C) :=
(bicone : binary_bicone P Q)
(is_bilimit : bicone.is_bilimit)

/--
`has_binary_biproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class has_binary_biproduct (P Q : C) : Prop :=
mk' :: (exists_binary_biproduct : nonempty (binary_biproduct_data P Q))

lemma has_binary_biproduct.mk {P Q : C} (d : binary_biproduct_data P Q) :
  has_binary_biproduct P Q :=
⟨nonempty.intro d⟩

/--
Use the axiom of choice to extract explicit `binary_biproduct_data F` from `has_binary_biproduct F`.
-/
def get_binary_biproduct_data (P Q : C) [has_binary_biproduct P Q] : binary_biproduct_data P Q :=
classical.choice has_binary_biproduct.exists_binary_biproduct

/-- A bicone for `P Q ` which is both a limit cone and a colimit cocone. -/
def binary_biproduct.bicone (P Q : C) [has_binary_biproduct P Q] : binary_bicone P Q :=
(get_binary_biproduct_data P Q).bicone

/-- `binary_biproduct.bicone P Q` is a limit bicone. -/
def binary_biproduct.is_bilimit (P Q : C) [has_binary_biproduct P Q] :
  (binary_biproduct.bicone P Q).is_bilimit :=
(get_binary_biproduct_data P Q).is_bilimit

/-- `binary_biproduct.bicone P Q` is a limit cone. -/
def binary_biproduct.is_limit (P Q : C) [has_binary_biproduct P Q] :
  is_limit (binary_biproduct.bicone P Q).to_cone :=
(get_binary_biproduct_data P Q).is_bilimit.is_limit

/-- `binary_biproduct.bicone P Q` is a colimit cocone. -/
def binary_biproduct.is_colimit (P Q : C) [has_binary_biproduct P Q] :
  is_colimit (binary_biproduct.bicone P Q).to_cocone :=
(get_binary_biproduct_data P Q).is_bilimit.is_colimit

section
variable (C)

/--
`has_binary_biproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class has_binary_biproducts : Prop :=
(has_binary_biproduct : Π (P Q : C), has_binary_biproduct P Q)

attribute [instance, priority 100] has_binary_biproducts.has_binary_biproduct

/--
A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
lemma has_binary_biproducts_of_finite_biproducts [has_finite_biproducts C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ P Q, has_binary_biproduct.mk
  { bicone := (biproduct.bicone (pair_function P Q)).to_binary_bicone,
    is_bilimit := (bicone.to_binary_bicone_is_bilimit _).symm (biproduct.is_bilimit _) } }

end

variables {P Q : C}

instance has_binary_biproduct.has_limit_pair [has_binary_biproduct P Q] :
  has_limit (pair P Q) :=
has_limit.mk ⟨_, binary_biproduct.is_limit P Q⟩

instance has_binary_biproduct.has_colimit_pair [has_binary_biproduct P Q] :
  has_colimit (pair P Q) :=
has_colimit.mk ⟨_, binary_biproduct.is_colimit P Q⟩

@[priority 100]
instance has_binary_products_of_has_binary_biproducts [has_binary_biproducts C] :
  has_binary_products C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_pair F).symm }
@[priority 100]
instance has_binary_coproducts_of_has_binary_biproducts [has_binary_biproducts C] :
  has_binary_coproducts C :=
{ has_colimit := λ F, has_colimit_of_iso (diagram_iso_pair F) }

/--
The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprod_iso (X Y : C) [has_binary_biproduct X Y]  :
  limits.prod X Y ≅ limits.coprod X Y :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (binary_biproduct.is_limit X Y)).trans $
  is_colimit.cocone_point_unique_up_to_iso (binary_biproduct.is_colimit X Y) (colimit.is_colimit _)

/-- An arbitrary choice of biproduct of a pair of objects. -/
abbreviation biprod (X Y : C) [has_binary_biproduct X Y] := (binary_biproduct.bicone X Y).X

notation X ` ⊞ `:20 Y:20 := biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbreviation biprod.fst {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ X :=
(binary_biproduct.bicone X Y).fst
/-- The projection onto the second summand of a binary biproduct. -/
abbreviation biprod.snd {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ Y :=
(binary_biproduct.bicone X Y).snd
/-- The inclusion into the first summand of a binary biproduct. -/
abbreviation biprod.inl {X Y : C} [has_binary_biproduct X Y] : X ⟶ X ⊞ Y :=
(binary_biproduct.bicone X Y).inl
/-- The inclusion into the second summand of a binary biproduct. -/
abbreviation biprod.inr {X Y : C} [has_binary_biproduct X Y] : Y ⟶ X ⊞ Y :=
(binary_biproduct.bicone X Y).inr

section
variables {X Y : C} [has_binary_biproduct X Y]

@[simp] lemma binary_biproduct.bicone_fst : (binary_biproduct.bicone X Y).fst = biprod.fst := rfl
@[simp] lemma binary_biproduct.bicone_snd : (binary_biproduct.bicone X Y).snd = biprod.snd := rfl
@[simp] lemma binary_biproduct.bicone_inl : (binary_biproduct.bicone X Y).inl = biprod.inl := rfl
@[simp] lemma binary_biproduct.bicone_inr : (binary_biproduct.bicone X Y).inr = biprod.inr := rfl

end

@[simp,reassoc]
lemma biprod.inl_fst {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
(binary_biproduct.bicone X Y).inl_fst
@[simp,reassoc]
lemma biprod.inl_snd {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
(binary_biproduct.bicone X Y).inl_snd
@[simp,reassoc]
lemma biprod.inr_fst {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
(binary_biproduct.bicone X Y).inr_fst
@[simp,reassoc]
lemma biprod.inr_snd {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
(binary_biproduct.bicone X Y).inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbreviation biprod.lift {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  W ⟶ X ⊞ Y :=
(binary_biproduct.is_limit X Y).lift (binary_fan.mk f g)
/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbreviation biprod.desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  X ⊞ Y ⟶ W :=
(binary_biproduct.is_colimit X Y).desc (binary_cofan.mk f g)

@[simp, reassoc]
lemma biprod.lift_fst {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  biprod.lift f g ≫ biprod.fst = f :=
(binary_biproduct.is_limit X Y).fac _ ⟨walking_pair.left⟩

@[simp, reassoc]
lemma biprod.lift_snd {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  biprod.lift f g ≫ biprod.snd = g :=
(binary_biproduct.is_limit X Y).fac _ ⟨walking_pair.right⟩

@[simp, reassoc]
lemma biprod.inl_desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  biprod.inl ≫ biprod.desc f g = f :=
(binary_biproduct.is_colimit X Y).fac _ ⟨walking_pair.left⟩

@[simp, reassoc]
lemma biprod.inr_desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  biprod.inr ≫ biprod.desc f g = g :=
(binary_biproduct.is_colimit X Y).fac _ ⟨walking_pair.right⟩

instance biprod.mono_lift_of_mono_left {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X)
  (g : W ⟶ Y) [mono f] : mono (biprod.lift f g) :=
mono_of_mono_fac $ biprod.lift_fst _ _

instance biprod.mono_lift_of_mono_right {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X)
  (g : W ⟶ Y) [mono g] : mono (biprod.lift f g) :=
mono_of_mono_fac $ biprod.lift_snd _ _

instance biprod.epi_desc_of_epi_left {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  [epi f] : epi (biprod.desc f g) :=
epi_of_epi_fac $ biprod.inl_desc _ _

instance biprod.epi_desc_of_epi_right {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  [epi g] : epi (biprod.desc f g) :=
epi_of_epi_fac $ biprod.inr_desc _ _

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbreviation biprod.map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
is_limit.map (binary_biproduct.bicone W X).to_cone (binary_biproduct.is_limit Y Z)
  (@map_pair _ _ (pair W X) (pair Y Z) f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbreviation biprod.map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
is_colimit.map (binary_biproduct.is_colimit W X) (binary_biproduct.bicone Y Z).to_cocone
  (@map_pair _ _ (pair W X) (pair Y Z) f g)

@[ext] lemma biprod.hom_ext {X Y Z : C} [has_binary_biproduct X Y] (f g : Z ⟶ X ⊞ Y)
  (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
binary_fan.is_limit.hom_ext (binary_biproduct.is_limit X Y) h₀ h₁

@[ext] lemma biprod.hom_ext' {X Y Z : C} [has_binary_biproduct X Y] (f g : X ⊞ Y ⟶ Z)
  (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
binary_cofan.is_colimit.hom_ext (binary_biproduct.is_colimit X Y) h₀ h₁

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biprod.iso_prod (X Y : C) [has_binary_biproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
is_limit.cone_point_unique_up_to_iso (binary_biproduct.is_limit X Y) (limit.is_limit _)

@[simp] lemma biprod.iso_prod_hom {X Y : C} [has_binary_biproduct X Y] :
  (biprod.iso_prod X Y).hom = prod.lift biprod.fst biprod.snd :=
by ext; simp [biprod.iso_prod]

@[simp] lemma biprod.iso_prod_inv {X Y : C} [has_binary_biproduct X Y] :
  (biprod.iso_prod X Y).inv = biprod.lift prod.fst prod.snd :=
by apply biprod.hom_ext; simp [iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biprod.iso_coprod (X Y : C) [has_binary_biproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
is_colimit.cocone_point_unique_up_to_iso (binary_biproduct.is_colimit X Y) (colimit.is_colimit _)

@[simp] lemma biprod.iso_coprod_inv {X Y : C} [has_binary_biproduct X Y] :
  (biprod.iso_coprod X Y).inv = coprod.desc biprod.inl biprod.inr :=
by ext; simp [biprod.iso_coprod]; refl

@[simp] lemma biprod_iso_coprod_hom {X Y : C} [has_binary_biproduct X Y] :
  (biprod.iso_coprod X Y).hom = biprod.desc coprod.inl coprod.inr :=
by apply biprod.hom_ext'; simp [← iso.eq_comp_inv]

lemma biprod.map_eq_map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g :=
begin
  ext,
  { simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, biprod.inl_fst_assoc,
    category.assoc, ←binary_bicone.to_cone_π_app_left, ←binary_biproduct.bicone_fst,
    ←binary_bicone.to_cocone_ι_app_left, ←binary_biproduct.bicone_inl],
    simp },
  { simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, zero_comp,
      biprod.inl_snd_assoc, category.assoc,
      ←binary_bicone.to_cone_π_app_right, ←binary_biproduct.bicone_snd,
      ←binary_bicone.to_cocone_ι_app_left, ←binary_biproduct.bicone_inl],
    simp },
  { simp only [map_pair_right, biprod.inr_fst_assoc, is_colimit.ι_map, is_limit.map_π,
      zero_comp, category.assoc,
      ←binary_bicone.to_cone_π_app_left, ←binary_biproduct.bicone_fst,
      ←binary_bicone.to_cocone_ι_app_right, ←binary_biproduct.bicone_inr],
    simp },
  { simp only [map_pair_right, is_colimit.ι_map, is_limit.map_π, biprod.inr_snd_assoc,
      category.assoc, ←binary_bicone.to_cone_π_app_right, ←binary_biproduct.bicone_snd,
      ←binary_bicone.to_cocone_ι_app_right, ←binary_biproduct.bicone_inr],
    simp }
end

instance biprod.inl_mono {X Y : C} [has_binary_biproduct X Y] :
  is_split_mono (biprod.inl : X ⟶ X ⊞ Y) :=
is_split_mono.mk' { retraction := biprod.fst }

instance biprod.inr_mono {X Y : C} [has_binary_biproduct X Y] :
  is_split_mono (biprod.inr : Y ⟶ X ⊞ Y) :=
is_split_mono.mk' { retraction := biprod.snd }

instance biprod.fst_epi {X Y : C} [has_binary_biproduct X Y] :
  is_split_epi (biprod.fst : X ⊞ Y ⟶ X) :=
is_split_epi.mk' { section_ := biprod.inl }

instance biprod.snd_epi {X Y : C} [has_binary_biproduct X Y] :
  is_split_epi (biprod.snd : X ⊞ Y ⟶ Y) :=
is_split_epi.mk' { section_ := biprod.inr }

@[simp,reassoc]
lemma biprod.map_fst {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
is_limit.map_π _ _ _ (⟨walking_pair.left⟩ : discrete walking_pair)

@[simp,reassoc]
lemma biprod.map_snd {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
is_limit.map_π _ _ _ (⟨walking_pair.right⟩ : discrete walking_pair)

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[simp,reassoc]
lemma biprod.inl_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.inl ≫ biprod.map f g = f ≫ biprod.inl :=
begin
  rw biprod.map_eq_map',
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ ⟨walking_pair.left⟩
end

@[simp,reassoc]
lemma biprod.inr_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.inr ≫ biprod.map f g = g ≫ biprod.inr :=
begin
  rw biprod.map_eq_map',
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ ⟨walking_pair.right⟩
end

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.map_iso {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ≅ Y) (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z :=
{ hom := biprod.map f.hom g.hom,
  inv := biprod.map f.inv g.inv }

/-- Auxiliary lemma for `biprod.unique_up_to_iso`. -/
lemma biprod.cone_point_unique_up_to_iso_hom (X Y : C) [has_binary_biproduct X Y]
  {b : binary_bicone X Y} (hb : b.is_bilimit) :
  (hb.is_limit.cone_point_unique_up_to_iso (binary_biproduct.is_limit _ _)).hom
    = biprod.lift b.fst b.snd :=
rfl

/-- Auxiliary lemma for `biprod.unique_up_to_iso`. -/
lemma biprod.cone_point_unique_up_to_iso_inv (X Y : C) [has_binary_biproduct X Y]
  {b : binary_bicone X Y} (hb : b.is_bilimit) :
  (hb.is_limit.cone_point_unique_up_to_iso (binary_biproduct.is_limit _ _)).inv
    = biprod.desc b.inl b.inr :=
begin
  refine biprod.hom_ext' _ _ (hb.is_limit.hom_ext (λ j, _)) (hb.is_limit.hom_ext (λ j, _)),
  all_goals { simp only [category.assoc, is_limit.cone_point_unique_up_to_iso_inv_comp],
    rcases j with ⟨⟨⟩⟩ },
  all_goals { simp }
end

/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
    limits, but in the case of biproducts we can give an isomorphism with particularly nice
    definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
    are inverses of each other. -/
@[simps]
def biprod.unique_up_to_iso (X Y : C) [has_binary_biproduct X Y] {b : binary_bicone X Y}
  (hb : b.is_bilimit) : b.X ≅ X ⊞ Y :=
{ hom := biprod.lift b.fst b.snd,
  inv := biprod.desc b.inl b.inr,
  hom_inv_id' := by rw [← biprod.cone_point_unique_up_to_iso_hom X Y hb,
    ← biprod.cone_point_unique_up_to_iso_inv X Y hb, iso.hom_inv_id],
  inv_hom_id' := by rw [← biprod.cone_point_unique_up_to_iso_hom X Y hb,
    ← biprod.cone_point_unique_up_to_iso_inv X Y hb, iso.inv_hom_id] }

-- There are three further variations,
-- about `is_iso biprod.inr`, `is_iso biprod.fst` and `is_iso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
lemma biprod.is_iso_inl_iff_id_eq_fst_comp_inl (X Y : C) [has_binary_biproduct X Y] :
  is_iso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl :=
begin
  split,
  { introI h,
    have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 biprod.inl_fst,
    rw [is_iso.inv_hom_id_assoc, category.comp_id] at this,
    rw [this, is_iso.inv_hom_id], },
  { intro h, exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩, },
end

section biprod_kernel

section binary_bicone

variables {X Y : C} (c : binary_bicone X Y)

/-- A kernel fork for the kernel of `binary_bicone.fst`. It consists of the morphism
`binary_bicone.inr`. -/
def binary_bicone.fst_kernel_fork : kernel_fork c.fst := kernel_fork.of_ι c.inr c.inr_fst

@[simp] lemma binary_bicone.fst_kernel_fork_ι : (binary_bicone.fst_kernel_fork c).ι = c.inr := rfl

/-- A kernel fork for the kernel of `binary_bicone.snd`. It consists of the morphism
`binary_bicone.inl`. -/
def binary_bicone.snd_kernel_fork : kernel_fork c.snd := kernel_fork.of_ι c.inl c.inl_snd

@[simp] lemma binary_bicone.snd_kernel_fork_ι : (binary_bicone.snd_kernel_fork c).ι = c.inl := rfl

/-- A cokernel cofork for the cokernel of `binary_bicone.inl`. It consists of the morphism
`binary_bicone.snd`. -/
def binary_bicone.inl_cokernel_cofork : cokernel_cofork c.inl :=
cokernel_cofork.of_π c.snd c.inl_snd

@[simp] lemma binary_bicone.inl_cokernel_cofork_π :
  (binary_bicone.inl_cokernel_cofork c).π = c.snd := rfl

/-- A cokernel cofork for the cokernel of `binary_bicone.inr`. It consists of the morphism
`binary_bicone.fst`. -/
def binary_bicone.inr_cokernel_cofork : cokernel_cofork c.inr :=
cokernel_cofork.of_π c.fst c.inr_fst

@[simp] lemma binary_bicone.inr_cokernel_cofork_π :
  (binary_bicone.inr_cokernel_cofork c).π = c.fst := rfl

variables {c}

/-- The fork defined in `binary_bicone.fst_kernel_fork` is indeed a kernel. -/
def binary_bicone.is_limit_fst_kernel_fork (i : is_limit c.to_cone) :
  is_limit c.fst_kernel_fork :=
fork.is_limit.mk' _ $ λ s,
⟨s.ι ≫ c.snd, by apply binary_fan.is_limit.hom_ext i; simp, λ m hm, by simp [← hm]⟩

/-- The fork defined in `binary_bicone.snd_kernel_fork` is indeed a kernel. -/
def binary_bicone.is_limit_snd_kernel_fork (i : is_limit c.to_cone) :
  is_limit c.snd_kernel_fork :=
fork.is_limit.mk' _ $ λ s,
⟨s.ι ≫ c.fst, by apply binary_fan.is_limit.hom_ext i; simp, λ m hm, by simp [← hm]⟩

/-- The cofork defined in `binary_bicone.inl_cokernel_cofork` is indeed a cokernel. -/
def binary_bicone.is_colimit_inl_cokernel_cofork (i : is_colimit c.to_cocone) :
  is_colimit c.inl_cokernel_cofork :=
cofork.is_colimit.mk' _ $ λ s, ⟨c.inr ≫ s.π, by apply binary_cofan.is_colimit.hom_ext i; simp,
  λ m hm, by simp [← hm]⟩

/-- The cofork defined in `binary_bicone.inr_cokernel_cofork` is indeed a cokernel. -/
def binary_bicone.is_colimit_inr_cokernel_cofork (i : is_colimit c.to_cocone) :
  is_colimit c.inr_cokernel_cofork :=
cofork.is_colimit.mk' _ $ λ s, ⟨c.inl ≫ s.π, by apply binary_cofan.is_colimit.hom_ext i; simp,
  λ m hm, by simp [← hm]⟩

end binary_bicone

section has_binary_biproduct

variables (X Y : C) [has_binary_biproduct X Y]

/-- A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`. -/
def biprod.fst_kernel_fork : kernel_fork (biprod.fst : X ⊞ Y ⟶ X) :=
binary_bicone.fst_kernel_fork _

@[simp]
lemma biprod.fst_kernel_fork_ι : fork.ι (biprod.fst_kernel_fork X Y) = biprod.inr :=
rfl

/-- The fork `biprod.fst_kernel_fork` is indeed a limit.  -/
def biprod.is_kernel_fst_kernel_fork : is_limit (biprod.fst_kernel_fork X Y) :=
binary_bicone.is_limit_fst_kernel_fork (binary_biproduct.is_limit _ _)

/-- A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`. -/
def biprod.snd_kernel_fork : kernel_fork (biprod.snd : X ⊞ Y ⟶ Y) :=
binary_bicone.snd_kernel_fork _

@[simp]
lemma biprod.snd_kernel_fork_ι : fork.ι (biprod.snd_kernel_fork X Y) = biprod.inl :=
rfl

/-- The fork `biprod.snd_kernel_fork` is indeed a limit.  -/
def biprod.is_kernel_snd_kernel_fork : is_limit (biprod.snd_kernel_fork X Y) :=
binary_bicone.is_limit_snd_kernel_fork (binary_biproduct.is_limit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`. -/
def biprod.inl_cokernel_cofork : cokernel_cofork (biprod.inl : X ⟶ X ⊞ Y) :=
binary_bicone.inl_cokernel_cofork _

@[simp]
lemma biprod.inl_cokernel_cofork_π : cofork.π (biprod.inl_cokernel_cofork X Y) = biprod.snd :=
rfl

/-- The cofork `biprod.inl_cokernel_fork` is indeed a colimit.  -/
def biprod.is_cokernel_inl_cokernel_fork : is_colimit (biprod.inl_cokernel_cofork X Y) :=
binary_bicone.is_colimit_inl_cokernel_cofork (binary_biproduct.is_colimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`. -/
def biprod.inr_cokernel_cofork : cokernel_cofork (biprod.inr : Y ⟶ X ⊞ Y) :=
binary_bicone.inr_cokernel_cofork _

@[simp]
lemma biprod.inr_cokernel_cofork_π : cofork.π (biprod.inr_cokernel_cofork X Y) = biprod.fst :=
rfl

/-- The cofork `biprod.inr_cokernel_fork` is indeed a colimit.  -/
def biprod.is_cokernel_inr_cokernel_fork : is_colimit (biprod.inr_cokernel_cofork X Y) :=
binary_bicone.is_colimit_inr_cokernel_cofork (binary_biproduct.is_colimit _ _)

end has_binary_biproduct

variables {X Y : C} [has_binary_biproduct X Y]

instance : has_kernel (biprod.fst : X ⊞ Y ⟶ X) :=
has_limit.mk ⟨_, biprod.is_kernel_fst_kernel_fork X Y⟩

/-- The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`. -/
@[simps]
def kernel_biprod_fst_iso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y :=
limit.iso_limit_cone ⟨_, biprod.is_kernel_fst_kernel_fork X Y⟩

instance : has_kernel (biprod.snd : X ⊞ Y ⟶ Y) :=
has_limit.mk ⟨_, biprod.is_kernel_snd_kernel_fork X Y⟩

/-- The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`. -/
@[simps]
def kernel_biprod_snd_iso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X :=
limit.iso_limit_cone ⟨_, biprod.is_kernel_snd_kernel_fork X Y⟩

instance : has_cokernel (biprod.inl : X ⟶ X ⊞ Y) :=
has_colimit.mk ⟨_, biprod.is_cokernel_inl_cokernel_fork X Y⟩

/-- The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`. -/
@[simps]
def cokernel_biprod_inl_iso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y :=
colimit.iso_colimit_cocone ⟨_, biprod.is_cokernel_inl_cokernel_fork X Y⟩

instance : has_cokernel (biprod.inr : Y ⟶ X ⊞ Y) :=
has_colimit.mk ⟨_, biprod.is_cokernel_inr_cokernel_fork X Y⟩

/-- The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`. -/
@[simps]
def cokernel_biprod_inr_iso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X :=
colimit.iso_colimit_cocone ⟨_, biprod.is_cokernel_inr_cokernel_fork X Y⟩

end biprod_kernel

section is_zero

/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps]
def iso_biprod_zero {X Y : C} [has_binary_biproduct X Y] (hY : is_zero Y) : X ≅ X ⊞ Y :=
{ hom := biprod.inl,
  inv := biprod.fst,
  inv_hom_id' := begin
    apply category_theory.limits.biprod.hom_ext;
    simp only [category.assoc, biprod.inl_fst, category.comp_id, category.id_comp,
      biprod.inl_snd, comp_zero],
    apply hY.eq_of_tgt
  end }

/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
def iso_zero_biprod {X Y : C} [has_binary_biproduct X Y] (hY : is_zero X) : Y ≅ X ⊞ Y :=
{ hom := biprod.inr,
  inv := biprod.snd,
  inv_hom_id' := begin
    apply category_theory.limits.biprod.hom_ext;
    simp only [category.assoc, biprod.inr_snd, category.comp_id, category.id_comp,
      biprod.inr_fst, comp_zero],
    apply hY.eq_of_tgt
  end }

end is_zero

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

end limits

open category_theory.limits

-- TODO:
-- If someone is interested, they could provide the constructions:
--   has_binary_biproducts ↔ has_finite_biproducts
variables {C : Type.{u}} [category.{v} C] [has_zero_morphisms C] [has_binary_biproducts C]

/-- An object is indecomposable if it cannot be written as the biproduct of two nonzero objects. -/
def indecomposable (X : C) : Prop := ¬ is_zero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → is_zero Y ∨ is_zero Z

/--
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
lemma is_iso_left_of_is_iso_biprod_map
  {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso f :=
⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
  ⟨begin
    have t := congr_arg (λ p : W ⊞ X ⟶ W ⊞ X, biprod.inl ≫ p ≫ biprod.fst)
      (is_iso.hom_inv_id (biprod.map f g)),
    simp only [category.id_comp, category.assoc, biprod.inl_map_assoc] at t,
    simp [t],
  end,
  begin
    have t := congr_arg (λ p : Y ⊞ Z ⟶ Y ⊞ Z, biprod.inl ≫ p ≫ biprod.fst)
      (is_iso.inv_hom_id (biprod.map f g)),
    simp only [category.id_comp, category.assoc, biprod.map_fst] at t,
    simp only [category.assoc],
    simp [t],
  end⟩⟩⟩

/--
If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
lemma is_iso_right_of_is_iso_biprod_map
  {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso g :=
begin
  letI : is_iso (biprod.map g f) := by
  { rw [←biprod.braiding_map_braiding],
    apply_instance, },
  exact is_iso_left_of_is_iso_biprod_map g f,
end

end category_theory
