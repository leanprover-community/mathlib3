/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

/-!
# Pseudofunctors

A pseudofunctor `F` between bicategories `B` and `C` consists of
* a function on objects `map₀ : B ⟶ C`,
* a function on 1-morphisms `map₁ : (a ⟶ b) → (map₀ a ⟶ map₀ b)`,
* a function on 2-morphisms `map₂ : (f ⟶ g) → (map₁ f ⟶ map₁ g)`,
* an isormorphism `map₁_comp : 𝟙 (map₀ a) ≅ map₁ (𝟙 a)`,
* an isormorphism `map₁_id : map₁ f ≫ map₁ g ≅ map₁ (f ≫ g)`, and
* certain conditions on them.

The direction of isomorphisms `map₁_comp` and `map₁_id` here is the lax direction.

## Future work
* Lax and oplax functors.
-/

open category_theory

universes w₁ w₂ v₁ v₂ u₁ u₂

open category_theory.bicategory

namespace category_theory

section

variables
(B : Type u₁) [bicategory.{w₁ v₁} B]
(C : Type u₂) [bicategory.{w₂ v₂} C]

/--
A pseudofunctor `F` between bicategories `B` and `C` consists of a function on objects,
a function on 1-morphisms, and a function on 2-morphisms,

Unlike functors between categories, functions between 1-morphisms in pseudofunctors
do not need to strictly commute with compositions and strictly preserve identities.
Instead, there are specified isomorphisms `𝟙 (map₀ a) ≅ map₁ (𝟙 a)` and
`map₁ f ≫ map₁ g ≅ map₁ (f ≫ g)`.

Functions between 2-morphisms in pseudofunctors preserve associator, left unitor, and right unitor.
-/
structure pseudofunctor :=
(map₀ : B → C)
(map₁ {a b} : (a ⟶ b) → (map₀ a ⟶ map₀ b))
(map₂ {a b} {f g : a ⟶ b} : (f ⟶ g) → (map₁ f ⟶ map₁ g))
(map₁_id (a) : 𝟙 (map₀ a) ≅ map₁ (𝟙 a))
(map₁_comp {a b c} (f : a ⟶ b) (g : b ⟶ c) :
   map₁ f ≫ map₁ g ≅ map₁ (f ≫ g))
(map₁_comp_naturality_left' : ∀ {a b c} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
  (map₂ η ▹ map₁ g) ≫ (map₁_comp f' g).hom
  = (map₁_comp f g).hom ≫ map₂ (η ▹ g) . obviously)
(map₁_comp_naturality_right' : ∀ {a b c} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
 (map₁ f ◃ map₂ η) ≫ (map₁_comp f g').hom
  = (map₁_comp f g).hom  ≫ map₂ (f ◃ η) . obviously)
(map₂_id' : ∀ {a b} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map₁ f) . obviously)
(map₂_comp' : ∀ {a b} {f g h : a ⟶ b}
  (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  ((map₁_comp f g).hom ▹ map₁ h) ≫ (map₁_comp (f ≫ g) h).hom ≫ map₂ (α_ f g h).hom
  = (α_ (map₁ f) (map₁ g) (map₁ h)).hom ≫ (map₁ f ◃ (map₁_comp g h).hom)
  ≫ (map₁_comp f (g ≫ h)).hom . obviously)
(map₂_left_unitor' : ∀ {a b} (f : a ⟶ b),
  ((map₁_id a).hom ▹ map₁ f) ≫ (map₁_comp (𝟙 a) f).hom ≫ map₂ (λ_ _).hom
  =  (λ_ _).hom . obviously)
(map₂_right_unitor' : ∀ {a b} (f : a ⟶ b),
  (map₁ f ◃ (map₁_id b).hom) ≫ (map₁_comp f (𝟙 b)).hom ≫ map₂ (ρ_ _).hom
  =  (ρ_ _).hom . obviously)

restate_axiom pseudofunctor.map₁_comp_naturality_left'
attribute [simp, reassoc] pseudofunctor.map₁_comp_naturality_left
restate_axiom pseudofunctor.map₁_comp_naturality_right'
attribute [simp, reassoc] pseudofunctor.map₁_comp_naturality_right
restate_axiom pseudofunctor.map₂_id'
attribute [simp] pseudofunctor.map₂_id
restate_axiom pseudofunctor.map₂_comp'
attribute [reassoc, simp] pseudofunctor.map₂_comp
restate_axiom pseudofunctor.map₂_associator'
attribute [simp, reassoc] pseudofunctor.map₂_associator
restate_axiom pseudofunctor.map₂_left_unitor'
attribute [reassoc, simp] pseudofunctor.map₂_left_unitor
restate_axiom pseudofunctor.map₂_right_unitor'
attribute [reassoc, simp] pseudofunctor.map₂_right_unitor

end

section

namespace pseudofunctor

variables (B : Type u₁) [bicategory.{w₁ v₁} B]

/-- The identity pseudofunctor. -/
@[simps] def id : pseudofunctor B B :=
{ map₀ := id,
  map₁ := λ a b, @id (a ⟶ b),
  map₂ := λ a b f g, @id (f ⟶ g),
  map₁_comp := λ a b c f g, iso.refl (f ≫ g),
  map₁_id := λ a, iso.refl (𝟙 a) }

instance : inhabited (pseudofunctor B B) := ⟨id B⟩

end pseudofunctor

end

end category_theory
