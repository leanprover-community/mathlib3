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

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.bicategory

namespace category_theory

section

variables
(B : Type u₁) [bicategory.{w₁ v₁} B]
(C : Type u₂) [bicategory.{w₂ v₂} C]

/--
A pseudofunctor `F` between bicategories `B` and `C` consists of a function on objects,
a function on 1-morphisms, and a function on 2-morphisms,

Unlike functors between categories, functions between 1-morphisms do not need to strictly commute
with compositions, and do not need to strictly preserve identities. Instead, there are specified
isomorphisms `𝟙 (map₀ a) ≅ map₁ (𝟙 a)` and `map₁ f ≫ map₁ g ≅ map₁ (f ≫ g)`.

Functions between 2-morphisms preserve associator, left unitor, and right unitor.
-/
structure pseudofunctor :=
(map₀ : B → C)
(map₁ {a b : B} : (a ⟶ b) → (map₀ a ⟶ map₀ b))
(map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map₁ f ⟶ map₁ g))
(map₁_id (a : B) : 𝟙 (map₀ a) ≅ map₁ (𝟙 a))
(map₁_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map₁ f ≫ map₁ g ≅ map₁ (f ≫ g))
(map₁_comp_naturality_left' : ∀ {a b c} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
  (map₂ η ▷ map₁ g) ≫ (map₁_comp f' g).hom
  = (map₁_comp f g).hom ≫ map₂ (η ▷ g) . obviously)
(map₁_comp_naturality_right' : ∀ {a b c} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
  (map₁ f ◁ map₂ η) ≫ (map₁_comp f g').hom
  = (map₁_comp f g).hom ≫ map₂ (f ◁ η) . obviously)
(map₂_id' : ∀ {a b} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map₁ f) . obviously)
(map₂_comp' : ∀ {a b} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  ((map₁_comp f g).hom ▷ map₁ h) ≫ (map₁_comp (f ≫ g) h).hom ≫ map₂ (α_ f g h).hom
  = (α_ (map₁ f) (map₁ g) (map₁ h)).hom ≫ (map₁ f ◁ (map₁_comp g h).hom)
  ≫ (map₁_comp f (g ≫ h)).hom . obviously)
(map₂_left_unitor' : ∀ {a b} (f : a ⟶ b),
  ((map₁_id a).hom ▷ map₁ f) ≫ (map₁_comp (𝟙 a) f).hom ≫ map₂ (λ_ f).hom
  = (λ_ (map₁ f)).hom . obviously)
(map₂_right_unitor' : ∀ {a b} (f : a ⟶ b),
  (map₁ f ◁ (map₁_id b).hom) ≫ (map₁_comp f (𝟙 b)).hom ≫ map₂ (ρ_ f).hom
  = (ρ_ (map₁ f)).hom . obviously)

restate_axiom pseudofunctor.map₁_comp_naturality_left'
attribute [simp, reassoc] pseudofunctor.map₁_comp_naturality_left
restate_axiom pseudofunctor.map₁_comp_naturality_right'
attribute [simp, reassoc] pseudofunctor.map₁_comp_naturality_right
restate_axiom pseudofunctor.map₂_id'
attribute [simp] pseudofunctor.map₂_id
restate_axiom pseudofunctor.map₂_comp'
attribute [reassoc, simp] pseudofunctor.map₂_comp
restate_axiom pseudofunctor.map₂_associator'
attribute [reassoc] pseudofunctor.map₂_associator
restate_axiom pseudofunctor.map₂_left_unitor'
attribute [reassoc] pseudofunctor.map₂_left_unitor
restate_axiom pseudofunctor.map₂_right_unitor'
attribute [reassoc] pseudofunctor.map₂_right_unitor

end

namespace pseudofunctor

section

variables (B : Type u₁) [bicategory.{w₁ v₁} B]

/-- The identity pseudofunctor. -/
@[simps] def id : pseudofunctor B B :=
{ map₀ := id,
  map₁ := λ a b, @id (a ⟶ b),
  map₂ := λ a b f g, @id (f ⟶ g),
  map₁_comp := λ a b c f g, iso.refl (f ≫ g),
  map₁_id := λ a, iso.refl (𝟙 a) }

instance : inhabited (pseudofunctor B B) := ⟨id B⟩

end

section
variables
{B : Type u₁} [bicategory.{w₁ v₁} B]
{C : Type u₂} [bicategory.{w₂ v₂} C]
(F : pseudofunctor B C) {a b c d : B}

/--
Function on 1-morphisms as a functor.
-/
@[simps]
def map₁_functor (a b : B) :
  (a ⟶ b) ⥤ (F.map₀ a ⟶ F.map₀ b) :=
{ obj := λ f, F.map₁ f,
  map := λ f g η, F.map₂ η,
  map_id' := λ f, F.map₂_id f,
  map_comp' := λ f g h η θ, F.map₂_comp η θ }

@[reassoc]
lemma map₂_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  ((F.map₁ f) ◁ (F.map₁_comp g h).hom) ≫ (F.map₁_comp f (g ≫ h)).hom ≫ F.map₂ (α_ f g h).inv
  = (α_ (F.map₁ f) (F.map₁ g) (F.map₁ h)).inv ≫ ((F.map₁_comp f g).hom ▷ (F.map₁ h))
  ≫ (F.map₁_comp (f ≫ g) h).hom :=
begin
  rw [iso.eq_inv_comp, ←map₂_associator_assoc,
    ←map₂_comp, iso.hom_inv_id, map₂_id, category.comp_id]
end

@[reassoc, simp]
lemma map₂_associator_eq (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  F.map₂ (α_ f g h).hom
  = (F.map₁_comp (f ≫ g) h).inv ≫ ((F.map₁_comp f g).inv ▷ F.map₁ h)
  ≫ (α_ (F.map₁ f) (F.map₁ g) (F.map₁ h)).hom ≫ (F.map₁ f ◁ (F.map₁_comp g h).hom)
  ≫ (F.map₁_comp f (g ≫ h)).hom :=
begin
  apply (cancel_epi (F.map₁_comp (f ≫ g) h).hom).1,
  apply (cancel_epi ((F.map₁_comp f g).hom ▷ F.map₁ h)).1,
  rw map₂_associator,
  simp
end

@[reassoc, simp]
lemma map₂_associator_inv_eq (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  F.map₂ (α_ f g h).inv
  = (F.map₁_comp f (g ≫ h)).inv ≫ (F.map₁ f ◁ (F.map₁_comp g h).inv)
  ≫ (α_ (F.map₁ f) (F.map₁ g) (F.map₁ h)).inv ≫ ((F.map₁_comp f g).hom ▷ F.map₁ h)
  ≫ (F.map₁_comp (f ≫ g) h).hom :=
begin
  apply (cancel_epi (F.map₁_comp f (g ≫ h)).hom).1,
  apply (cancel_epi ((F.map₁ f) ◁ (F.map₁_comp g h).hom)).1,
  rw map₂_associator_inv,
  simp
end

@[reassoc, simp]
lemma map₂_left_unitor_eq (f : a ⟶ b) :
  F.map₂ (λ_ f).hom
  = (F.map₁_comp (𝟙 a) f).inv ≫ ((F.map₁_id a).inv ▷ F.map₁ f) ≫ (λ_ (F.map₁ f)).hom :=
begin
  rw [iso.eq_inv_comp, ←map₂_left_unitor, inv_hom_whisker_right_assoc]
end

@[reassoc, simp]
lemma map₂_left_unitor_inv_eq (f : a ⟶ b) :
  F.map₂ (λ_ f).inv
  = (λ_ (F.map₁ f)).inv ≫ ((F.map₁_id a).hom ▷ F.map₁ f) ≫ (F.map₁_comp (𝟙 a) f).hom :=
begin
  rw [iso.eq_inv_comp, ←map₂_left_unitor, category.assoc, category.assoc,
      ←map₂_comp, iso.hom_inv_id, F.map₂_id, category.comp_id]
end

@[reassoc, simp]
lemma map₂_right_unitor_eq (f : a ⟶ b) :
  F.map₂ (ρ_ f).hom
  = (F.map₁_comp f (𝟙 b)).inv ≫ (F.map₁ f ◁ (F.map₁_id b).inv) ≫ (ρ_ (F.map₁ f)).hom :=
begin
  rw [iso.eq_inv_comp, ←map₂_right_unitor, inv_hom_whisker_left_assoc]
end

@[reassoc, simp]
lemma map₂_right_unitor_inv_eq (f : a ⟶ b) :
  F.map₂ (ρ_ f).inv
  = (ρ_ (F.map₁ f)).inv ≫ (F.map₁ f ◁ (F.map₁_id b).hom) ≫ (F.map₁_comp f (𝟙 b)).hom :=
begin
  rw [iso.eq_inv_comp, ←map₂_right_unitor, category.assoc, category.assoc,
      ←map₂_comp, iso.hom_inv_id, F.map₂_id, category.comp_id]
end

@[simp, reassoc]
lemma map₁_comp_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
  (F.map₂ (η ▷ g)) ≫ (F.map₁_comp f' g).inv
  = (F.map₁_comp f g).inv ≫ (F.map₂ η ▷ F.map₁ g) :=
by rw [iso.comp_inv_eq, category.assoc, map₁_comp_naturality_left, iso.inv_hom_id_assoc]

@[simp, reassoc]
lemma map₁_comp_inv_naturality_right (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') :
  (F.map₂ (f ◁ η)) ≫ (F.map₁_comp f g').inv
  = (F.map₁_comp f g).inv ≫ (F.map₁ f ◁ F.map₂ η) :=
by rw [iso.comp_inv_eq, category.assoc, map₁_comp_naturality_right, iso.inv_hom_id_assoc]

end

section

variables
{A : Type u₁} [bicategory.{w₁ v₁} A]
{B : Type u₂} [bicategory.{w₂ v₂} B]
{C : Type u₃} [bicategory.{w₃ v₃} C]
(F : pseudofunctor.{w₁ w₂ v₁ v₂} A B) (G : pseudofunctor.{w₂ w₃ v₂ v₃} B C)

/--
If `F` is a pseudofunctor from `A` to `B` and `G` is a pseudofunctor from `B` to `C`,
`F.comp G` is a pseudofunctor from `A` to `C`.
-/
@[simps] def comp : pseudofunctor.{w₁ w₃ v₁ v₃} A C :=
{ map₀ := λ a, G.map₀ (F.map₀ a),
  map₁ := λ a b f, G.map₁ (F.map₁ f),
  map₂ := λ a b f g η, G.map₂ (F.map₂ η),
  map₁_id := λ a,
    G.map₁_id (F.map₀ a) ≪≫ (G.map₁_functor _ _).map_iso (F.map₁_id a),
  map₁_comp := λ a b c f g,
    G.map₁_comp (F.map₁ f) (F.map₁ g) ≪≫ (G.map₁_functor _ _).map_iso (F.map₁_comp f g),
  map₁_comp_naturality_left' := λ a b c f f' η g, by
  { dsimp,
    rw [map₁_comp_naturality_left_assoc, ←map₂_comp, map₁_comp_naturality_left],
    simp},
  map₁_comp_naturality_right' := λ a b c f g g' η, by
  { dsimp,
    rw [map₁_comp_naturality_right_assoc, ←map₂_comp, map₁_comp_naturality_right],
    simp },
  map₂_id'    := by { intros, simp only [map₂_id] },
  map₂_comp'  := by { intros, simp only [map₂_comp] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp,
    simp only [whisker_right_comp, whisker_left_comp, category.assoc],
    rw [map₁_comp_naturality_left_assoc, map₁_comp_naturality_right_assoc,
        ←map₂_associator_assoc],
    simp only [←map₂_comp],
    rw ←map₂_associator },
  map₂_left_unitor' := λ a b f, by
  { dsimp,
    simp only [whisker_right_comp, category.assoc],
    rw [map₁_comp_naturality_left_assoc, ←map₂_left_unitor],
    simp only [←map₂_comp],
    rw ←map₂_left_unitor },
  map₂_right_unitor' := λ a b f, by
  { dsimp,
    simp only [whisker_left_comp, category.assoc],
    rw [map₁_comp_naturality_right_assoc, ←map₂_right_unitor],
    simp only [←map₂_comp],
    rw ←map₂_right_unitor } }

end

end pseudofunctor

end category_theory
