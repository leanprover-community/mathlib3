/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.limits
import category_theory.discrete_category

noncomputable theory

universes v u

open category_theory

namespace category_theory.limits

variables {β : Type v}
variables {C : Type u} [category.{v} C]

-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `discrete.functor`.

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
abbreviation fan (f : β → C) := cone (discrete.functor f)
/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbreviation cofan (f : β → C) := cocone (discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps]
def fan.mk {f : β → C} (P : C) (p : Π b, P ⟶ f b) : fan f :=
{ X := P,
  π := { app := p } }

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps]
def cofan.mk {f : β → C} (P : C) (p : Π b, f b ⟶ P) : cofan f :=
{ X := P,
  ι := { app := p } }

/-- An abbreviation for `has_limit (discrete.functor f)`. -/
abbreviation has_product (f : β → C) := has_limit (discrete.functor f)

/-- An abbreviation for `has_colimit (discrete.functor f)`. -/
abbreviation has_coproduct (f : β → C) := has_colimit (discrete.functor f)

section
variables (C)

/-- An abbreviation for `has_limits_of_shape (discrete f)`. -/
abbreviation has_products_of_shape (β : Type v) := has_limits_of_shape.{v} (discrete β)
/-- An abbreviation for `has_colimits_of_shape (discrete f)`. -/
abbreviation has_coproducts_of_shape (β : Type v) := has_colimits_of_shape.{v} (discrete β)
end

/-- `pi_obj f` computes the product of a family of elements `f`. (It is defined as an abbreviation
   for `limit (discrete.functor f)`, so for most facts about `pi_obj f`, you will just use general facts
   about limits.) -/
abbreviation pi_obj (f : β → C) [has_product f] := limit (discrete.functor f)
/-- `sigma_obj f` computes the coproduct of a family of elements `f`. (It is defined as an abbreviation
   for `colimit (discrete.functor f)`, so for most facts about `sigma_obj f`, you will just use general facts
   about colimits.) -/
abbreviation sigma_obj (f : β → C) [has_coproduct f] := colimit (discrete.functor f)

notation `∏ ` f:20 := pi_obj f
notation `∐ ` f:20 := sigma_obj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
abbreviation pi.π (f : β → C) [has_product f] (b : β) : ∏ f ⟶ f b :=
limit.π (discrete.functor f) b
/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbreviation sigma.ι (f : β → C) [has_coproduct f] (b : β) : f b ⟶ ∐ f :=
colimit.ι (discrete.functor f) b

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
abbreviation pi.map {f g : β → C} [has_products_of_shape β C]
  (p : Π b, f b ⟶ g b) : ∏ f ⟶ ∏ g :=
lim.map (discrete.nat_trans p)
/--
Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbreviation pi.map_iso {f g : β → C} [has_products_of_shape β C]
  (p : Π b, f b ≅ g b) : ∏ f ≅ ∏ g :=
lim.map_iso (discrete.nat_iso p)
/--
Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbreviation sigma.map {f g : β → C} [has_coproducts_of_shape β C]
  (p : Π b, f b ⟶ g b) : ∐ f ⟶ ∐ g :=
colim.map (discrete.nat_trans p)
/--
Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbreviation sigma.map_iso {f g : β → C} [has_coproducts_of_shape β C]
  (p : Π b, f b ≅ g b) : ∐ f ≅ ∐ g :=
colim.map_iso (discrete.nat_iso p)

variables (C)

/-- An abbreviation for `Π J, has_limits_of_shape (discrete J) C` -/
abbreviation has_products := Π (J : Type v), has_limits_of_shape (discrete J) C
/-- An abbreviation for `Π J, has_colimits_of_shape (discrete J) C` -/
abbreviation has_coproducts := Π (J : Type v), has_colimits_of_shape (discrete J) C

variables {C}

section punit

instance has_products_of_shape_punit : has_products_of_shape punit C :=
{ has_limit := λ F,
  { cone :=
    { X := F.obj punit.star,
      π :=
      { app := λ j, F.map (eq_to_hom (by ext)), } },
    is_limit :=
    { lift := λ s, s.π.app punit.star,
      uniq' := λ s m w, by { specialize w punit.star, dsimp at w, simp [←w], }, }, }, }

instance pi_π_punit_is_iso (f : punit.{v+1} → C) : is_iso (pi.π f punit.star) :=
{ inv := pi.lift (λ x, eq_to_hom (by { rcases x, refl, })) }

-- This formulation lets us see that `pi.lift p` is `mono`/`epi`/`is_iso` iff `p punit.star` is.
@[simp]
lemma pi_lift_punit {f : punit.{v+1} → C} {P : C} (p : Π b, P ⟶ f b) :
  pi.lift p = p punit.star ≫ inv (pi.π f punit.star) :=
by tidy

instance has_coproducts_of_shape_punit : has_coproducts_of_shape punit C :=
{ has_colimit := λ F,
  { cocone :=
    { X := F.obj punit.star,
      ι :=
      { app := λ j, F.map (eq_to_hom (by ext)), } },
    is_colimit :=
    { desc := λ s, s.ι.app punit.star,
      uniq' := λ s m w, by { specialize w punit.star, dsimp at w, simp [←w], }, }, }, }

instance sigma_ι_punit_is_iso (f : punit.{v+1} → C) : is_iso (sigma.ι f punit.star) :=
{ inv := sigma.desc (λ x, eq_to_hom (by { rcases x, refl, })) }

-- This formulation lets us see that `sigma.desc p` is `mono`/`epi`/`is_iso` iff `p punit.star` is.
@[simp]
lemma sigma_desc_punit {f : punit.{v+1} → C} {P : C} (p : Π b, f b ⟶ P) :
  sigma.desc p = inv (sigma.ι f punit.star) ≫ p punit.star :=
by tidy

end punit

section sigma -- (In the sense of dependent pairs!)

variables (z : β → Type v)
variables (f : Π b, z b → C)

section
variables [∀ b, has_product (f b)]
variables [has_product (λ b, ∏ (f b))]

instance has_product_of_shape_sigma : has_product (λ p : Σ b, z b, f p.1 p.2) :=
{ cone :=
  { X := ∏ (λ b : β, ∏ (λ c : z b, f b c)),
    π :=
    { app := λ j,
        pi.π _ j.1 ≫ pi.π (λ c : z j.1, f j.1 c) j.2 ≫ eq_to_hom (by { cases j, refl, }),
      naturality' :=
        by { rintros ⟨j₁,j₂⟩ ⟨k₁,k₂⟩ ⟨⟨g⟩⟩, injection g with h₁ h₂, subst h₁, subst h₂, tidy, } } },
  is_limit :=
  { lift := λ s, pi.lift (λ b, pi.lift (λ c, s.π.app ⟨b, c⟩)),
    uniq' := λ s m w, by { ext b c, specialize w ⟨b,c⟩, dsimp at w, simp [←w], }, }, }
end

section
variables [∀ b, has_coproduct (f b)]
variables [has_coproduct (λ b, ∐ (f b))]

instance has_coproduct_of_shape_sigma : has_coproduct (λ p : Σ b, z b, f p.1 p.2) :=
{ cocone :=
  { X := ∐ (λ b : β, ∐ (λ c : z b, f b c)),
    ι :=
    { app := λ j,
        eq_to_hom (by { cases j, refl, }) ≫
          (sigma.ι (λ c : z j.1, f j.1 c) j.2 : _) ≫ sigma.ι (λ b : β, ∐ (λ c : z b, f b c)) j.1,
      naturality' :=
        by { rintros ⟨j₁,j₂⟩ ⟨k₁,k₂⟩ ⟨⟨g⟩⟩, injection g with h₁ h₂, subst h₁, subst h₂, tidy, } } },
  is_colimit :=
  { desc := λ s, sigma.desc (λ b, sigma.desc (λ c, s.ι.app ⟨b, c⟩)),
    uniq' := λ s m w, by { ext b c, specialize w ⟨b,c⟩, dsimp at w, simp [←w], }, }, }
end



end sigma

end category_theory.limits
