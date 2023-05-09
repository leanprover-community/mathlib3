/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.isomorphism
import tactic.slice

/-!
# Bicategories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define typeclass for bicategories.

A bicategory `B` consists of
* objects `a : B`,
* 1-morphisms `f : a ⟶ b` between objects `a b : B`, and
* 2-morphisms `η : f ⟶ g` beween 1-morphisms `f g : a ⟶ b` between objects `a b : B`.

We use `u`, `v`, and `w` as the universe variables for objects, 1-morphisms, and 2-morphisms,
respectively.

A typeclass for bicategories extends `category_theory.category_struct` typeclass. This means that
we have
* a composition `f ≫ g : a ⟶ c` for each 1-morphisms `f : a ⟶ b` and `g : b ⟶ c`, and
* a identity `𝟙 a : a ⟶ a` for each object `a : B`.

For each object `a b : B`, the collection of 1-morphisms `a ⟶ b` has a category structure. The
2-morphisms in the bicategory are implemented as the morphisms in this family of categories.

The composition of 1-morphisms is in fact a object part of a functor
`(a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c)`. The definition of bicategories in this file does not
require this functor directly. Instead, it requires the whiskering functions. For a 1-morphism
`f : a ⟶ b` and a 2-morphism `η : g ⟶ h` between 1-morphisms `g h : b ⟶ c`, there is a
2-morphism `whisker_left f η : f ≫ g ⟶ f ≫ h`. Similarly, for a 2-morphism `η : f ⟶ g`
between 1-morphisms `f g : a ⟶ b` and a 1-morphism `f : b ⟶ c`, there is a 2-morphism
`whisker_right η h : f ≫ h ⟶ g ≫ h`. These satisfy the exchange law
`whisker_left f θ ≫ whisker_right η i = whisker_right η h ≫ whisker_left g θ`,
which is required as an axiom in the definition here.
-/

namespace category_theory

universes w v u

open category iso

/--
In a bicategory, we can compose the 1-morphisms `f : a ⟶ b` and `g : b ⟶ c` to obtain
a 1-morphism `f ≫ g : a ⟶ c`. This composition does not need to be strictly associative,
but there is a specified associator, `α_ f g h : (f ≫ g) ≫ h ≅ f ≫ (g ≫ h)`.
There is an identity 1-morphism `𝟙 a : a ⟶ a`, with specified left and right unitor
isomorphisms `λ_ f : 𝟙 a ≫ f ≅ f` and `ρ_ f : f ≫ 𝟙 a ≅ f`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://ncatlab.org/nlab/show/bicategory.
-/
@[nolint check_univs] -- intended to be used with explicit universe parameters
class bicategory (B : Type u) extends category_struct.{v} B :=
-- category structure on the collection of 1-morphisms:
(hom_category : ∀ (a b : B), category.{w} (a ⟶ b) . tactic.apply_instance)
-- left whiskering:
(whisker_left {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h)
(infixr ` ◁ `:81 := whisker_left)
-- right whiskering:
(whisker_right {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h)
(infixl ` ▷ `:81 := whisker_right)
-- associator:
(associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (f ≫ g) ≫ h ≅ f ≫ (g ≫ h))
(notation `α_` := associator)
-- left unitor:
(left_unitor {a b : B} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f)
(notation `λ_` := left_unitor)
-- right unitor:
(right_unitor {a b : B} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f)
(notation `ρ_` := right_unitor)
-- axioms for left whiskering:
(whisker_left_id' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
  f ◁ 𝟙 g = 𝟙 (f ≫ g) . obviously)
(whisker_left_comp' : ∀ {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
  f ◁ (η ≫ θ) = f ◁ η ≫ f ◁ θ . obviously)
(id_whisker_left' : ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
  𝟙 a ◁ η = (λ_ f).hom ≫ η ≫ (λ_ g).inv . obviously)
(comp_whisker_left' : ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
  (f ≫ g) ◁ η = (α_ f g h).hom ≫ f ◁ g ◁ η ≫ (α_ f g h').inv . obviously)
-- axioms for right whiskering:
(id_whisker_right' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
  𝟙 f ▷ g = 𝟙 (f ≫ g) . obviously)
(comp_whisker_right' : ∀ {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
  (η ≫ θ) ▷ i = η ▷ i ≫ θ ▷ i . obviously)
(whisker_right_id' : ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
  η ▷ 𝟙 b = (ρ_ f).hom ≫ η ≫ (ρ_ g).inv . obviously)
(whisker_right_comp' : ∀ {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
  η ▷ (g ≫ h) = (α_ f g h).inv ≫ η ▷ g ▷ h ≫ (α_ f' g h).hom . obviously)
-- associativity of whiskerings:
(whisker_assoc' : ∀ {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
  (f ◁ η) ▷ h = (α_ f g h).hom ≫ f ◁ (η ▷ h) ≫ (α_ f g' h).inv . obviously)
-- exchange law of left and right whiskerings:
(whisker_exchange' : ∀ {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
  f ◁ θ ≫ η ▷ i = η ▷ h ≫ g ◁ θ . obviously)
-- pentagon identity:
(pentagon' : ∀ {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
  (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom =
    (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom . obviously)
-- triangle identity:
(triangle' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
  (α_ f (𝟙 b) g).hom ≫ f ◁ (λ_ g).hom = (ρ_ f).hom ▷ g . obviously)

-- The precedence of the whiskerings is higher than that of the composition `≫`.
localized "infixr (name := bicategory.whisker_left) ` ◁ `:81 := bicategory.whisker_left"
  in bicategory
localized "infixl (name := bicategory.whisker_right) ` ▷ `:81 := bicategory.whisker_right"
  in bicategory
localized "notation (name := bicategory.associator) `α_` := bicategory.associator"
  in bicategory
localized "notation (name := bicategory.left_unitor) `λ_` := bicategory.left_unitor"
  in bicategory
localized "notation (name := bicategory.right_unitor) `ρ_` := bicategory.right_unitor"
  in bicategory

namespace bicategory

/-!
### Simp-normal form for 2-morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any 2-morphisms into simp-normal
form defined below. Rewriting into simp-normal form is also useful when applying (forthcoming)
`coherence` tactic.

The simp-normal form of 2-morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of 2-morphisms like `η₁ ≫ η₂ ≫ η₃ ≫ η₄ ≫ η₅` such that each `ηᵢ` is
  either a structural 2-morphisms (2-morphisms made up only of identities, associators, unitors)
  or non-structural 2-morphisms, and
2. each non-structural 2-morphism in the composition is of the form `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅`,
  where each `fᵢ` is a 1-morphism that is not the identity or a composite and `η` is a
  non-structural 2-morphisms that is also not the identity or a composite.

Note that `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅` is actually `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))`.
-/

restate_axiom whisker_left_id'
restate_axiom whisker_left_comp'
restate_axiom id_whisker_left'
restate_axiom comp_whisker_left'
restate_axiom id_whisker_right'
restate_axiom comp_whisker_right'
restate_axiom whisker_right_id'
restate_axiom whisker_right_comp'
restate_axiom whisker_assoc'
restate_axiom whisker_exchange'
restate_axiom pentagon'
restate_axiom triangle'

attribute [simp]  pentagon triangle
attribute [reassoc]
  whisker_left_comp id_whisker_left comp_whisker_left
  comp_whisker_right whisker_right_id whisker_right_comp
  whisker_assoc whisker_exchange pentagon triangle
/-
The following simp attributes are put in order to rewrite any 2-morphisms into normal forms. There
are associators and unitors in the RHS in the several simp lemmas here (e.g. `id_whisker_left`),
which at first glance look more complicated than the LHS, but they will be eventually reduced by the
pentagon or the triangle identities, and more generally, (forthcoming) `coherence` tactic.
-/
attribute [simp]
  whisker_left_id whisker_left_comp id_whisker_left comp_whisker_left
  id_whisker_right comp_whisker_right whisker_right_id whisker_right_comp
  whisker_assoc
attribute [instance] hom_category

variables {B : Type u} [bicategory.{w v} B] {a b c d e : B}

@[simp, reassoc]
lemma hom_inv_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
  f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g) :=
by rw [←whisker_left_comp, hom_inv_id, whisker_left_id]

@[simp, reassoc]
lemma hom_inv_whisker_right {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
  η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h) :=
by rw [←comp_whisker_right, hom_inv_id, id_whisker_right]

@[simp, reassoc]
lemma inv_hom_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
  f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h) :=
by rw [←whisker_left_comp, inv_hom_id, whisker_left_id]

@[simp, reassoc]
lemma inv_hom_whisker_right {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
  η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h) :=
by rw [←comp_whisker_right, inv_hom_id, id_whisker_right]

/-- The left whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps]
def whisker_left_iso (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
  f ≫ g ≅ f ≫ h :=
{ hom := f ◁ η.hom,
  inv := f ◁ η.inv }

instance whisker_left_is_iso (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [is_iso η] :
  is_iso (f ◁ η) :=
is_iso.of_iso (whisker_left_iso f (as_iso η))

@[simp]
lemma inv_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [is_iso η] :
  inv (f ◁ η) = f ◁ (inv η) :=
by { ext, simp only [←whisker_left_comp, whisker_left_id, is_iso.hom_inv_id] }

/-- The right whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps]
def whisker_right_iso {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
  f ≫ h ≅ g ≫ h :=
{ hom := η.hom ▷ h,
  inv := η.inv ▷ h }

instance whisker_right_is_iso {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [is_iso η] :
  is_iso (η ▷ h) :=
is_iso.of_iso (whisker_right_iso (as_iso η) h)

@[simp]
lemma inv_whisker_right {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [is_iso η] :
  inv (η ▷ h) = (inv η) ▷ h :=
by { ext, simp only [←comp_whisker_right, id_whisker_right, is_iso.hom_inv_id] }

@[simp, reassoc]
lemma pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i =
    (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv :=
eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
lemma pentagon_inv_inv_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom =
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv :=
by { rw [←cancel_epi (f ◁ (α_ g h i).inv), ←cancel_mono (α_ (f ≫ g) h i).inv], simp }

@[simp, reassoc]
lemma pentagon_inv_hom_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom =
    (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv :=
eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
lemma pentagon_hom_inv_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i :=
by simp [←cancel_epi (f ◁ (α_ g h i).inv)]

@[simp, reassoc]
lemma pentagon_hom_hom_inv_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv =
    (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom :=
eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
lemma pentagon_hom_inv_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv =
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i :=
by { rw [←cancel_epi (α_ f g (h ≫ i)).inv, ←cancel_mono ((α_ f g h).inv ▷ i)], simp }

@[simp, reassoc]
lemma pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv =
    (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom :=
eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
lemma pentagon_inv_hom_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
    (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom :=
by simp [←cancel_epi ((α_ f g h).hom ▷ i)]

@[simp, reassoc]
lemma pentagon_inv_inv_hom_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i =
    f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv :=
eq_of_inv_eq_inv (by simp)

lemma triangle_assoc_comp_left (f : a ⟶ b) (g : b ⟶ c) :
  (α_ f (𝟙 b) g).hom ≫ f ◁ (λ_ g).hom = (ρ_ f).hom ▷ g :=
triangle f g

@[simp, reassoc]
lemma triangle_assoc_comp_right (f : a ⟶ b) (g : b ⟶ c) :
  (α_ f (𝟙 b) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (λ_ g).hom :=
by rw [←triangle, inv_hom_id_assoc]

@[simp, reassoc]
lemma triangle_assoc_comp_right_inv (f : a ⟶ b) (g : b ⟶ c) :
  (ρ_ f).inv ▷ g ≫ (α_ f (𝟙 b) g).hom = f ◁ (λ_ g).inv :=
by simp [←cancel_mono (f ◁ (λ_ g).hom)]

@[simp, reassoc]
lemma triangle_assoc_comp_left_inv (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g :=
by simp [←cancel_mono ((ρ_ f).hom ▷ g)]

@[reassoc]
lemma associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  (η ▷ g) ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h) :=
by simp

@[reassoc]
lemma associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  η ▷ (g ≫ h) ≫ (α_ f' g h).inv = (α_ f g h).inv ≫ (η ▷ g) ▷ h :=
by simp

@[reassoc]
lemma whisker_right_comp_symm {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  (η ▷ g) ▷ h = (α_ f g h).hom ≫ η ▷ (g ≫ h) ≫ (α_ f' g h).inv :=
by simp

@[reassoc]
lemma associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ (η ▷ h) :=
by simp

@[reassoc]
lemma associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  f ◁ (η ▷ h) ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ (f ◁ η) ▷ h :=
by simp

@[reassoc]
lemma whisker_assoc_symm (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  f ◁ (η ▷ h) = (α_ f g h).inv ≫ (f ◁ η) ▷ h ≫ (α_ f g' h).hom :=
by simp

@[reassoc]
lemma associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ (g ◁ η) :=
by simp

@[reassoc]
lemma associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  f ◁ (g ◁ η) ≫ (α_ f g h').inv = (α_ f g h).inv ≫ (f ≫ g) ◁ η :=
by simp

@[reassoc]
lemma comp_whisker_left_symm (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  f ◁ (g ◁ η) = (α_ f g h).inv ≫ (f ≫ g) ◁ η ≫ (α_ f g h').hom :=
by simp

@[reassoc]
lemma left_unitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
  𝟙 a ◁ η ≫ (λ_ g).hom = (λ_ f).hom ≫ η :=
by simp

@[reassoc]
lemma left_unitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
  η ≫ (λ_ g).inv = (λ_ f).inv ≫ 𝟙 a ◁ η :=
by simp

lemma id_whisker_left_symm {f g : a ⟶ b} (η : f ⟶ g) :
  η = (λ_ f).inv ≫ 𝟙 a ◁ η ≫ (λ_ g).hom :=
by simp

@[reassoc]
lemma right_unitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
  η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η :=
by simp

@[reassoc]
lemma right_unitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
  η ≫ (ρ_ g).inv = (ρ_ f).inv ≫ η ▷ 𝟙 b :=
by simp

lemma whisker_right_id_symm {f g : a ⟶ b} (η : f ⟶ g) :
  η = (ρ_ f).inv ≫ η ▷ 𝟙 b ≫ (ρ_ g).hom :=
by simp

lemma whisker_left_iff {f g : a ⟶ b} (η θ : f ⟶ g) :
  (𝟙 a ◁ η = 𝟙 a ◁ θ) ↔ (η = θ) :=
by simp

lemma whisker_right_iff {f g : a ⟶ b} (η θ : f ⟶ g) :
  (η ▷ 𝟙 b = θ ▷ 𝟙 b) ↔ (η = θ) :=
by simp

/--
We state it as a simp lemma, which is regarded as an involved version of
`id_whisker_right f g : 𝟙 f ▷ g = 𝟙 (f ≫ g)`.
-/
@[reassoc, simp]
lemma left_unitor_whisker_right (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (λ_ (f ≫ g)).hom :=
by rw [←whisker_left_iff, whisker_left_comp, ←cancel_epi (α_ _ _ _).hom,
  ←cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle,
  ←associator_naturality_middle, ←comp_whisker_right_assoc, triangle,
  associator_naturality_left]; apply_instance

@[reassoc, simp]
lemma left_unitor_inv_whisker_right (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ f).inv ▷ g = (λ_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv :=
eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
lemma whisker_left_right_unitor (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).hom :=
by rw [←whisker_right_iff, comp_whisker_right, ←cancel_epi (α_ _ _ _).inv,
  ←cancel_epi (f ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right,
  ←associator_inv_naturality_middle, ←whisker_left_comp_assoc, triangle_assoc_comp_right,
  associator_inv_naturality_right]; apply_instance

@[reassoc, simp]
lemma whisker_left_right_unitor_inv (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g (𝟙 c)).hom :=
eq_of_inv_eq_inv (by simp)

/-
It is not so obvious whether `left_unitor_whisker_right` or `left_unitor_comp` should be a simp
lemma. Our choice is the former. One reason is that the latter yields the following loop:
[id_whisker_left]   : 𝟙 a ◁ (ρ_ f).hom ==> (λ_ (f ≫ 𝟙 b)).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv
[left_unitor_comp]  : (λ_ (f ≫ 𝟙 b)).hom ==> (α_ (𝟙 a) f (𝟙 b)).inv ≫ (λ_ f).hom ▷ 𝟙 b
[whisker_right_id]  : (λ_ f).hom ▷ 𝟙 b ==> (ρ_ (𝟙 a ≫ f)).hom ≫ (λ_ f).hom ≫ (ρ_ f).inv
[right_unitor_comp] : (ρ_ (𝟙 a ≫ f)).hom ==> (α_ (𝟙 a) f (𝟙 b)).hom ≫ 𝟙 a ◁ (ρ_ f).hom
-/
@[reassoc]
lemma left_unitor_comp (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ (f ≫ g)).hom = (α_ (𝟙 a) f g).inv ≫ (λ_ f).hom ▷ g :=
by simp

@[reassoc]
lemma left_unitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ (f ≫ g)).inv = (λ_ f).inv ▷ g ≫ (α_ (𝟙 a) f g).hom :=
by simp

@[reassoc]
lemma right_unitor_comp (f : a ⟶ b) (g : b ⟶ c) :
  (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c)).hom ≫ f ◁ (ρ_ g).hom :=
by simp

@[reassoc]
lemma right_unitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
  (ρ_ (f ≫ g)).inv = f ◁ (ρ_ g).inv ≫ (α_ f g (𝟙 c)).inv :=
by simp

@[simp]
lemma unitors_equal : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom :=
by rw [←whisker_left_iff, ←cancel_epi (α_ _ _ _).hom, ←cancel_mono (ρ_ _).hom, triangle,
  ←right_unitor_comp, right_unitor_naturality]; apply_instance

@[simp]
lemma unitors_inv_equal : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv :=
by simp [iso.inv_eq_inv]

end bicategory

end category_theory
