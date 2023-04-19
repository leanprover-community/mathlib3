/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.has_limits
import category_theory.discrete_category

/-!
# Categorical (co)products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `fan` is a cone over a discrete category
* `fan.mk` constructs a fan from an indexed collection of maps
* a `pi` is a `limit (discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

noncomputable theory

universes w v v₂ u u₂

open category_theory

namespace category_theory.limits

variables {β : Type w}
variables {C : Type u} [category.{v} C]

-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `discrete.functor`.

local attribute [tidy] tactic.discrete_cases

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
abbreviation fan (f : β → C) := cone (discrete.functor f)
/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbreviation cofan (f : β → C) := cocone (discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps]
def fan.mk {f : β → C} (P : C) (p : Π b, P ⟶ f b) : fan f :=
{ X := P,
  π := { app := λ X, p X.as } }

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps]
def cofan.mk {f : β → C} (P : C) (p : Π b, f b ⟶ P) : cofan f :=
{ X := P,
  ι := { app := λ X, p X.as } }

-- FIXME dualize as needed below (and rename?)

/-- Get the `j`th map in the fan -/
def fan.proj  {f : β → C} (p : fan f) (j : β) : p.X ⟶ f j := p.π.app (discrete.mk j)
@[simp] lemma fan_mk_proj {f : β → C} (P : C) (p : Π b, P ⟶ f b) (j : β) :
  (fan.mk P p).proj j = p j := rfl

/-- An abbreviation for `has_limit (discrete.functor f)`. -/
abbreviation has_product (f : β → C) := has_limit (discrete.functor f)

/-- An abbreviation for `has_colimit (discrete.functor f)`. -/
abbreviation has_coproduct (f : β → C) := has_colimit (discrete.functor f)

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `discrete` -/
@[simps] def mk_fan_limit {f : β → C} (t : fan f)
  (lift : Π s : fan f, s.X ⟶ t.X)
  (fac : ∀ (s : fan f) (j : β), lift s ≫ (t.proj j) = s.proj j)
  (uniq : ∀ (s : fan f) (m : s.X ⟶ t.X) (w : ∀ j : β, m ≫ t.proj j = s.proj j), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, by convert fac s j.as; simp,
  uniq' := λ s m w, uniq s m (λ j, w (discrete.mk j)), }


section
variables (C)

/-- An abbreviation for `has_limits_of_shape (discrete f)`. -/
abbreviation has_products_of_shape (β : Type v) := has_limits_of_shape.{v} (discrete β)
/-- An abbreviation for `has_colimits_of_shape (discrete f)`. -/
abbreviation has_coproducts_of_shape (β : Type v) := has_colimits_of_shape.{v} (discrete β)
end

/-- `pi_obj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (discrete.functor f)`,
so for most facts about `pi_obj f`, you will just use general facts about limits.) -/
abbreviation pi_obj (f : β → C) [has_product f] := limit (discrete.functor f)
/-- `sigma_obj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (discrete.functor f)`,
so for most facts about `sigma_obj f`, you will just use general facts about colimits.) -/
abbreviation sigma_obj (f : β → C) [has_coproduct f] := colimit (discrete.functor f)

notation `∏ ` f:20 := pi_obj f
notation `∐ ` f:20 := sigma_obj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
abbreviation pi.π (f : β → C) [has_product f] (b : β) : ∏ f ⟶ f b :=
limit.π (discrete.functor f) (discrete.mk b)
/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbreviation sigma.ι (f : β → C) [has_coproduct f] (b : β) : f b ⟶ ∐ f :=
colimit.ι (discrete.functor f) (discrete.mk b)

/-- The fan constructed of the projections from the product is limiting. -/
def product_is_product (f : β → C) [has_product f] :
  is_limit (fan.mk _ (pi.π f)) :=
is_limit.of_iso_limit (limit.is_limit (discrete.functor f)) (cones.ext (iso.refl _) (by tidy))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproduct_is_coproduct (f : β → C) [has_coproduct f] :
  is_colimit (cofan.mk _ (sigma.ι f)) :=
is_colimit.of_iso_colimit (colimit.is_colimit (discrete.functor f)) (cocones.ext (iso.refl _)
  (by tidy))

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ f`. -/
abbreviation pi.lift {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) : P ⟶ ∏ f :=
limit.lift _ (fan.mk P p)
/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbreviation sigma.desc {f : β → C} [has_coproduct f] {P : C} (p : Π b, f b ⟶ P) : ∐ f ⟶ P :=
colimit.desc _ (cofan.mk P p)

/--
Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
abbreviation pi.map {f g : β → C} [has_product f] [has_product g]
  (p : Π b, f b ⟶ g b) : ∏ f ⟶ ∏ g :=
lim_map (discrete.nat_trans (λ X, p X.as))

instance pi.map_mono {f g : β → C} [has_product f] [has_product g]
  (p : Π b, f b ⟶ g b) [Π i, mono (p i)] : mono $ pi.map p :=
@@limits.lim_map_mono _ _ _ _ _ (by { dsimp, apply_instance })

/--
Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbreviation pi.map_iso {f g : β → C} [has_products_of_shape β C]
  (p : Π b, f b ≅ g b) : ∏ f ≅ ∏ g :=
lim.map_iso (discrete.nat_iso (λ X, p X.as))
/--
Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbreviation sigma.map {f g : β → C} [has_coproduct f] [has_coproduct g]
  (p : Π b, f b ⟶ g b) : ∐ f ⟶ ∐ g :=
colim_map (discrete.nat_trans (λ X, p X.as))

instance sigma.map_epi {f g : β → C} [has_coproduct f] [has_coproduct g]
  (p : Π b, f b ⟶ g b) [Π i, epi (p i)] : epi $ sigma.map p :=
@@limits.colim_map_epi _ _ _ _ _ (by { dsimp, apply_instance })

/--
Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbreviation sigma.map_iso {f g : β → C} [has_coproducts_of_shape β C]
  (p : Π b, f b ≅ g b) : ∐ f ≅ ∐ g :=
colim.map_iso (discrete.nat_iso (λ X, p X.as))

section comparison

variables {D : Type u₂} [category.{v₂} D] (G : C ⥤ D)
variables (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `preserves_product.of_iso_comparison`. -/
def pi_comparison [has_product f] [has_product (λ b, G.obj (f b))] :
  G.obj (∏ f) ⟶ ∏ (λ b, G.obj (f b)) :=
pi.lift (λ b, G.map (pi.π f b))

@[simp, reassoc]
lemma pi_comparison_comp_π [has_product f] [has_product (λ b, G.obj (f b))] (b : β) :
  pi_comparison G f ≫ pi.π _ b = G.map (pi.π f b) :=
limit.lift_π _ (discrete.mk b)

@[simp, reassoc]
lemma map_lift_pi_comparison [has_product f] [has_product (λ b, G.obj (f b))]
  (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ pi_comparison G f = pi.lift (λ j, G.map (g j)) :=
by { ext, discrete_cases, simp [← G.map_comp] }

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `preserves_coproduct.of_iso_comparison`. -/
def sigma_comparison [has_coproduct f] [has_coproduct (λ b, G.obj (f b))] :
  ∐ (λ b, G.obj (f b)) ⟶ G.obj (∐ f) :=
sigma.desc (λ b, G.map (sigma.ι f b))

@[simp, reassoc]
lemma ι_comp_sigma_comparison [has_coproduct f] [has_coproduct (λ b, G.obj (f b))] (b : β) :
  sigma.ι _ b ≫ sigma_comparison G f = G.map (sigma.ι f b) :=
colimit.ι_desc _ (discrete.mk b)

@[simp, reassoc]
lemma sigma_comparison_map_desc [has_coproduct f] [has_coproduct (λ b, G.obj (f b))]
  (P : C) (g : Π j, f j ⟶ P) :
  sigma_comparison G f ≫ G.map (sigma.desc g) = sigma.desc (λ j, G.map (g j)) :=
by { ext, discrete_cases, simp [← G.map_comp] }

end comparison

variables (C)

/-- An abbreviation for `Π J, has_limits_of_shape (discrete J) C` -/
abbreviation has_products := Π (J : Type w), has_limits_of_shape (discrete J) C
/-- An abbreviation for `Π J, has_colimits_of_shape (discrete J) C` -/
abbreviation has_coproducts := Π (J : Type w), has_colimits_of_shape (discrete J) C

variable {C}

lemma has_smallest_products_of_has_products [has_products.{w} C] : has_products.{0} C :=
λ J, has_limits_of_shape_of_equivalence
  (discrete.equivalence equiv.ulift : discrete (ulift.{w} J) ≌ _)

lemma has_smallest_coproducts_of_has_coproducts [has_coproducts.{w} C] : has_coproducts.{0} C :=
λ J, has_colimits_of_shape_of_equivalence
  (discrete.equivalence equiv.ulift : discrete (ulift.{w} J) ≌ _)

lemma has_products_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), fan f)
  (lf_is_limit : ∀ {J : Type w} (f : J → C), is_limit (lf f)) : has_products.{w} C :=
λ (J : Type w), { has_limit := λ F, has_limit.mk
  ⟨(cones.postcompose discrete.nat_iso_functor.inv).obj (lf (λ j, F.obj ⟨j⟩)),
    (is_limit.postcompose_inv_equiv _ _).symm (lf_is_limit _)⟩ }

/-!
(Co)products over a type with a unique term.
-/
section unique
variables {C} [unique β] (f : β → C)

/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
def limit_cone_of_unique : limit_cone (discrete.functor f) :=
{ cone :=
  { X := f default,
    π := { app := λ j, eq_to_hom (by { dsimp, congr, }), }, },
  is_limit :=
  { lift := λ s, s.π.app default,
    fac' := λ s j, begin
      have w := (s.π.naturality (eq_to_hom (unique.default_eq _))).symm,
      dsimp at w,
      simpa [eq_to_hom_map] using w,
    end,
    uniq' := λ s m w, begin
      specialize w default,
      dsimp at w,
      simpa using w,
    end, }, }

@[priority 100] instance has_product_unique : has_product f :=
has_limit.mk (limit_cone_of_unique f)

/-- A product over a index type with exactly one term is just the object over that term. -/
@[simps]
def product_unique_iso : ∏ f ≅ f default :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (limit_cone_of_unique f).is_limit

/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
def colimit_cocone_of_unique : colimit_cocone (discrete.functor f) :=
{ cocone :=
  { X := f default,
    ι := { app := λ j, eq_to_hom (by { discrete_cases, dsimp, congr, }), }, },
  is_colimit :=
  { desc := λ s, s.ι.app default,
    fac' := λ s j, begin
      have w := (s.ι.naturality (eq_to_hom (unique.eq_default _))),
      dsimp at w,
      simpa [eq_to_hom_map] using w,
    end,
    uniq' := λ s m w, begin
      specialize w default,
      dsimp at w,
      simpa using w,
    end, }, }

@[priority 100] instance has_coproduct_unique : has_coproduct f :=
has_colimit.mk (colimit_cocone_of_unique f)

/-- A coproduct over a index type with exactly one term is just the object over that term. -/
@[simps]
def coproduct_unique_iso : ∐ f ≅ f default :=
is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
  (colimit_cocone_of_unique f).is_colimit

end unique

section reindex
variables {C} {γ : Type v} (ε : β ≃ γ) (f : γ → C)

section
variables [has_product f] [has_product (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def pi.reindex : pi_obj (f ∘ ε) ≅ pi_obj f :=
has_limit.iso_of_equivalence (discrete.equivalence ε) (discrete.nat_iso (λ i, iso.refl _))

@[simp, reassoc]
lemma pi.reindex_hom_π (b : β) : (pi.reindex ε f).hom ≫ pi.π f (ε b) = pi.π (f ∘ ε) b :=
begin
  dsimp [pi.reindex],
  simp only [has_limit.iso_of_equivalence_hom_π, discrete.nat_iso_inv_app,
    equivalence.equivalence_mk'_counit, discrete.equivalence_counit_iso, discrete.nat_iso_hom_app,
    eq_to_iso.hom, eq_to_hom_map],
  dsimp,
  simpa [eq_to_hom_map] using
    limit.w (discrete.functor (f ∘ ε)) (discrete.eq_to_hom' (ε.symm_apply_apply b)),
end

@[simp, reassoc]
lemma pi.reindex_inv_π (b : β) : (pi.reindex ε f).inv ≫ pi.π (f ∘ ε) b = pi.π f (ε b) :=
by simp [iso.inv_comp_eq]

end

section
variables [has_coproduct f] [has_coproduct (f ∘ ε)]

/-- Reindex a categorical coproduct via an equivalence of the index types. -/
def sigma.reindex : sigma_obj (f ∘ ε) ≅ sigma_obj f :=
has_colimit.iso_of_equivalence (discrete.equivalence ε) (discrete.nat_iso (λ i, iso.refl _))

@[simp, reassoc]
lemma sigma.ι_reindex_hom (b : β) : sigma.ι (f ∘ ε) b ≫ (sigma.reindex ε f).hom = sigma.ι f (ε b) :=
begin
  dsimp [sigma.reindex],
  simp only [has_colimit.iso_of_equivalence_hom_π, equivalence.equivalence_mk'_unit,
    discrete.equivalence_unit_iso, discrete.nat_iso_hom_app, eq_to_iso.hom, eq_to_hom_map,
    discrete.nat_iso_inv_app],
  dsimp,
  simp [eq_to_hom_map,
    ←colimit.w (discrete.functor f) (discrete.eq_to_hom' (ε.apply_symm_apply (ε b)))],
end

@[simp, reassoc]
lemma sigma.ι_reindex_inv (b : β) : sigma.ι f (ε b) ≫ (sigma.reindex ε f).inv = sigma.ι (f ∘ ε) b :=
by simp [iso.comp_inv_eq]

end

end reindex

end category_theory.limits
