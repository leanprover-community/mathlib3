/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.isomorphism
import tactic.slice

/-!
# Bicategories

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
(infixr ` ◁ `:70 := whisker_left)
-- functoriality of left whiskering:
(whisker_left_id' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), f ◁ 𝟙 g = 𝟙 (f ≫ g) . obviously)
(whisker_left_comp' :
  ∀ {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
  f ◁ (η ≫ θ) = (f ◁ η) ≫ (f ◁ θ) . obviously)
-- right whiskering:
(whisker_right {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h)
(infixr ` ▷ `:70 := whisker_right)
-- functoriality of right whiskering:
(whisker_right_id' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), 𝟙 f ▷ g = 𝟙 (f ≫ g) . obviously)
(whisker_right_comp' :
  ∀ {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
  (η ≫ θ) ▷ i = (η ▷ i) ≫ (θ ▷ i) . obviously)
-- exchange law of left and right whiskerings:
(whisker_exchange' : ∀ {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
  (f ◁ θ) ≫ (η ▷ i) = (η ▷ h) ≫ (g ◁ θ) . obviously)
-- associator:
(associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (f ≫ g) ≫ h ≅ f ≫ (g ≫ h))
(notation `α_` := associator)
(associator_naturality_left' :
  ∀ {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
  ((η ▷ g) ▷ h) ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ (η ▷ (g ≫ h)) . obviously)
(associator_naturality_middle' :
  ∀ {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
  ((f ◁ η) ▷ h) ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ (f ◁ (η ▷ h)) . obviously)
(associator_naturality_right' :
  ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
  ((f ≫ g) ◁ η) ≫ (α_ f g h').hom = (α_ f g h).hom ≫ (f ◁ (g ◁ η)) . obviously)
--left unitor:
(left_unitor {a b : B} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f)
(notation `λ_` := left_unitor)
(left_unitor_naturality' : ∀ {a b} {f f' : a ⟶ b} (η : f ⟶ f'),
  (𝟙 a ◁ η) ≫ (λ_ f').hom = (λ_ f ).hom ≫ η . obviously)
-- right unitor:
(right_unitor {a b : B} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f)
(notation `ρ_` := right_unitor)
(right_unitor_naturality' : ∀ {a b} {f f' : a ⟶ b} (η : f ⟶ f'),
  (η ▷ 𝟙 b) ≫ (ρ_ f').hom = (ρ_ f ).hom ≫ η . obviously)
-- pentagon identity:
(pentagon' : ∀ {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
  ((α_ f g h).hom ▷ i) ≫ (α_ f (g ≫ h) i).hom ≫ (f ◁ (α_ g h i).hom) =
    (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom . obviously)
-- triangle identity:
(triangle' : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
  (α_ f (𝟙 b) g).hom ≫ (f ◁ (λ_ g).hom) = (ρ_ f).hom ▷ g . obviously)

restate_axiom bicategory.whisker_left_id'
restate_axiom bicategory.whisker_left_comp'
restate_axiom bicategory.whisker_right_id'
restate_axiom bicategory.whisker_right_comp'
restate_axiom bicategory.whisker_exchange'
restate_axiom bicategory.associator_naturality_left'
restate_axiom bicategory.associator_naturality_middle'
restate_axiom bicategory.associator_naturality_right'
restate_axiom bicategory.left_unitor_naturality'
restate_axiom bicategory.right_unitor_naturality'
restate_axiom bicategory.pentagon'
restate_axiom bicategory.triangle'
attribute [simp]
  bicategory.whisker_left_id bicategory.whisker_right_id
  bicategory.whisker_exchange bicategory.triangle
attribute [reassoc]
  bicategory.whisker_left_comp bicategory.whisker_right_comp
  bicategory.whisker_exchange bicategory.associator_naturality_left
  bicategory.associator_naturality_middle bicategory.associator_naturality_right
  bicategory.left_unitor_naturality bicategory.right_unitor_naturality
  bicategory.pentagon bicategory.triangle
attribute [simp] bicategory.whisker_left_comp bicategory.whisker_right_comp
attribute [instance] bicategory.hom_category

localized "infixr ` ◁ `:70 := bicategory.whisker_left" in bicategory
localized "infixr ` ▷ `:70 := bicategory.whisker_right" in bicategory
localized "notation `α_` := bicategory.associator" in bicategory
localized "notation `λ_` := bicategory.left_unitor" in bicategory
localized "notation `ρ_` := bicategory.right_unitor" in bicategory

namespace bicategory

section

variables {B : Type u} [bicategory.{w v} B] {a b c d e : B}

@[simp, reassoc]
lemma hom_inv_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
  (f ◁ η.hom) ≫ (f ◁ η.inv) = 𝟙 (f ≫ g) :=
by rw [←whisker_left_comp, hom_inv_id, whisker_left_id]

@[simp, reassoc]
lemma hom_inv_whisker_right {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
  (η.hom ▷ h) ≫ (η.inv ▷ h) = 𝟙 (f ≫ h) :=
by rw [←whisker_right_comp, hom_inv_id, whisker_right_id]

@[simp, reassoc]
lemma inv_hom_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
  (f ◁ η.inv) ≫ (f ◁ η.hom) = 𝟙 (f ≫ h) :=
by rw [←whisker_left_comp, inv_hom_id, whisker_left_id]

@[simp, reassoc]
lemma inv_hom_whisker_right {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
  (η.inv ▷ h) ≫ (η.hom ▷ h) = 𝟙 (g ≫ h) :=
by rw [←whisker_right_comp, inv_hom_id, whisker_right_id]

/-- The left whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps]
def whisker_left_iso (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
  f ≫ g ≅ f ≫ h :=
{ hom := f ◁ η.hom,
  inv := f ◁ η.inv,
  hom_inv_id' := by simp only [hom_inv_whisker_left],
  inv_hom_id' := by simp only [inv_hom_whisker_left] }

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
  inv := η.inv ▷ h,
  hom_inv_id' := by simp only [hom_inv_whisker_right],
  inv_hom_id' := by simp only [inv_hom_whisker_right] }

instance whisker_right_is_iso {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [is_iso η] :
  is_iso (η ▷ h) :=
is_iso.of_iso (whisker_right_iso (as_iso η) h)

@[simp]
lemma inv_whisker_right {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [is_iso η] :
  inv (η ▷ h) = (inv η) ▷ h :=
by { ext, simp only [←whisker_right_comp, whisker_right_id, is_iso.hom_inv_id] }

@[reassoc]
lemma left_unitor_inv_naturality {f f' : a ⟶ b} (η : f ⟶ f') :
  η ≫ (λ_ f').inv = (λ_ f).inv ≫ (𝟙 a ◁ η) :=
begin
  apply (cancel_mono (λ_ f').hom).1,
  simp only [assoc, comp_id, inv_hom_id, left_unitor_naturality, inv_hom_id_assoc]
end

@[reassoc]
lemma right_unitor_inv_naturality {f f' : a ⟶ b} (η : f ⟶ f') :
  η ≫ (ρ_ f').inv = (ρ_ f ).inv ≫ (η ▷ 𝟙 b) :=
begin
  apply (cancel_mono (ρ_ f').hom).1,
  simp only [assoc, comp_id, inv_hom_id, right_unitor_naturality, inv_hom_id_assoc]
end

@[simp]
lemma right_unitor_conjugation {f g : a ⟶ b} (η : f ⟶ g) :
  (ρ_ f).inv ≫ (η ▷ 𝟙 b) ≫ (ρ_ g).hom = η :=
by rw [right_unitor_naturality, inv_hom_id_assoc]

@[simp]
lemma left_unitor_conjugation {f g : a ⟶ b} (η : f ⟶ g) :
  (λ_ f).inv ≫ (𝟙 a ◁ η) ≫ (λ_ g).hom = η :=
by rw [left_unitor_naturality, inv_hom_id_assoc]

@[simp]
lemma whisker_left_iff {f g : a ⟶ b} (η θ : f ⟶ g) :
  (𝟙 a ◁ η = 𝟙 a ◁ θ) ↔ (η = θ) :=
by rw [←cancel_mono (λ_ g).hom, left_unitor_naturality, left_unitor_naturality,
    cancel_iso_hom_left]

@[simp]
lemma whisker_right_iff {f g : a ⟶ b} (η θ : f ⟶ g) :
  (η ▷ 𝟙 b = θ ▷ 𝟙 b) ↔ (η = θ) :=
by rw [←cancel_mono (ρ_ g).hom, right_unitor_naturality, right_unitor_naturality,
    cancel_iso_hom_left]

@[reassoc]
lemma left_unitor_comp' (f : a ⟶ b) (g : b ⟶ c) :
  (α_ (𝟙 a) f g).hom ≫ (λ_ (f ≫ g)).hom = (λ_ f).hom ▷ g :=
by rw [←whisker_left_iff, whisker_left_comp, ←cancel_epi (α_ (𝟙 a) (𝟙 a ≫ f) g).hom,
    ←cancel_epi ((α_ (𝟙 a) (𝟙 a) f).hom ▷ g), pentagon_assoc, triangle,
    ←associator_naturality_middle, ←whisker_right_comp_assoc, triangle,
    associator_naturality_left, cancel_iso_hom_left]

-- We state it as a `@[simp]` lemma. Generally, we think the component index of a natural
-- transformation "weighs more" in considering the complexity of an expression than
-- does a structural isomorphism (associator, etc).
@[reassoc, simp]
lemma left_unitor_comp (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ (f ≫ g)).hom = (α_ (𝟙 a) f g).inv ≫ ((λ_ f).hom ▷ g) :=
by { rw [←left_unitor_comp', inv_hom_id_assoc] }

lemma left_unitor_comp_inv' (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv = ((λ_ f).inv ▷ g) :=
eq_of_inv_eq_inv (by simp only [left_unitor_comp, inv_whisker_right,
  is_iso.iso.inv_inv, hom_inv_id_assoc, is_iso.inv_comp])

@[reassoc, simp]
lemma left_unitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ (f ≫ g)).inv = ((λ_ f).inv ▷ g) ≫ (α_ (𝟙 a) f g).hom :=
by { rw [←left_unitor_comp_inv'], simp only [inv_hom_id, assoc, comp_id] }

@[reassoc, simp]
lemma right_unitor_comp (f : a ⟶ b) (g : b ⟶ c) :
  (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c)).hom ≫ (f ◁ (ρ_ g).hom) :=
by rw [←whisker_right_iff, whisker_right_comp, ←cancel_mono (α_ f g (𝟙 c)).hom,
    assoc, associator_naturality_middle, ←triangle_assoc, ←triangle,
    whisker_left_comp, pentagon_assoc, ←associator_naturality_right]

@[reassoc, simp]
lemma right_unitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
  (ρ_ (f ≫ g)).inv = (f ◁ (ρ_ g).inv) ≫ (α_ f g (𝟙 c)).inv :=
eq_of_inv_eq_inv (by simp only [inv_whisker_left, right_unitor_comp,
  is_iso.iso.inv_inv, is_iso.inv_comp])

@[reassoc]
lemma whisker_left_right_unitor_inv (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g (𝟙 c)).hom :=
by simp only [right_unitor_comp_inv, comp_id, inv_hom_id, assoc]

@[reassoc]
lemma whisker_left_right_unitor (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).hom :=
by simp only [right_unitor_comp, inv_hom_id_assoc]

@[reassoc]
lemma left_unitor_inv_whisker_right (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ f).inv ▷ g = (λ_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv :=
by simp only [left_unitor_comp_inv, assoc, comp_id, hom_inv_id]

@[reassoc]
lemma left_unitor_whisker_right (f : a ⟶ b) (g : b ⟶ c) :
  (λ_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (λ_ (f ≫ g)).hom :=
by simp only [left_unitor_comp, hom_inv_id_assoc]

@[reassoc]
lemma associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  (η ▷ (g ≫ h)) ≫ (α_ f' g h).inv = (α_ f g h).inv ≫ ((η ▷ g) ▷ h) :=
by rw [comp_inv_eq, assoc, associator_naturality_left, inv_hom_id_assoc]

@[reassoc]
lemma associator_conjugation_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  (α_ f g h).hom ≫ (η ▷ (g ≫ h)) ≫ (α_ f' g h).inv = (η ▷ g) ▷ h :=
by rw [associator_inv_naturality_left, hom_inv_id_assoc]

@[reassoc]
lemma associator_inv_conjugation_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  (α_ f g h).inv ≫ ((η ▷ g) ▷ h) ≫ (α_ f' g h).hom = η ▷ (g ≫ h) :=
by rw [associator_naturality_left, inv_hom_id_assoc]

@[reassoc]
lemma associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  (f ◁ (η ▷ h)) ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ ((f ◁ η) ▷ h) :=
by rw [comp_inv_eq, assoc, associator_naturality_middle, inv_hom_id_assoc]

@[reassoc]
lemma associator_conjugation_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  (α_ f g h).hom ≫ (f ◁ (η ▷ h)) ≫ (α_ f g' h).inv = (f ◁ η) ▷ h :=
by rw [associator_inv_naturality_middle, hom_inv_id_assoc]

@[reassoc]
lemma associator_inv_conjugation_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  (α_ f g h).inv ≫ ((f ◁ η) ▷ h) ≫ (α_ f g' h).hom = f ◁ (η ▷ h) :=
by rw [associator_naturality_middle, inv_hom_id_assoc]

@[reassoc]
lemma associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  (f ◁ (g ◁ η)) ≫ (α_ f g h').inv = (α_ f g h).inv ≫ ((f ≫ g) ◁ η) :=
by rw [comp_inv_eq, assoc, associator_naturality_right, inv_hom_id_assoc]

@[reassoc]
lemma associator_conjugation_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  (α_ f g h).hom ≫ (f ◁ (g ◁ η)) ≫ (α_ f g h').inv = (f ≫ g) ◁ η :=
by rw [associator_inv_naturality_right, hom_inv_id_assoc]

@[reassoc]
lemma associator_inv_conjugation_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  (α_ f g h).inv ≫ ((f ≫ g) ◁ η) ≫ (α_ f g h').hom = f ◁ (g ◁ η) :=
by rw [associator_naturality_right, inv_hom_id_assoc]

@[reassoc]
lemma pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (f ◁ (α_ g h i).inv) ≫ (α_ f (g ≫ h) i).inv ≫ ((α_ f g h).inv ▷ i) =
    (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv :=
eq_of_inv_eq_inv (by simp only [pentagon, inv_whisker_left, inv_whisker_right,
  is_iso.iso.inv_inv, is_iso.inv_comp, assoc])

@[reassoc]
lemma pentagon_inv_inv_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f (g ≫ h) i).inv ≫ ((α_ f g h).inv ▷ i) ≫ (α_ (f ≫ g) h i).hom =
    (f ◁ (α_ g h i).hom) ≫ (α_ f g (h ≫ i)).inv :=
begin
  rw ←((eq_comp_inv _).mp (pentagon_inv f g h i)),
  slice_rhs 1 2 { rw [←whisker_left_comp, hom_inv_id] },
  simp only [assoc, id_comp, whisker_left_id]
end

@[reassoc]
lemma pentagon_inv_hom_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ (f ≫ g) h i).inv ≫ ((α_ f g h).hom ▷ i) ≫ (α_ f (g ≫ h) i).hom =
    (α_ f g (h ≫ i)).hom ≫ (f ◁ (α_ g h i).inv) :=
eq_of_inv_eq_inv (by simp only [pentagon_inv_inv_hom_hom_inv, inv_whisker_left,
  is_iso.iso.inv_hom, inv_whisker_right, is_iso.iso.inv_inv, is_iso.inv_comp, assoc])

@[reassoc]
lemma pentagon_hom_inv_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (f ◁ (α_ g h i).hom) ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
    (α_ f (g ≫ h) i).inv ≫ ((α_ f g h).inv ▷ i) :=
begin
  rw ←((eq_comp_inv _).mp (pentagon_inv f g h i)),
  slice_lhs 1 2 { rw [←whisker_left_comp, hom_inv_id] },
  simp only [assoc, id_comp, whisker_left_id, comp_id, hom_inv_id]
end

@[reassoc]
lemma pentagon_hom_hom_inv_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ (f ◁ (α_ g h i).inv) =
    ((α_ f g h).hom ▷ i) ≫ (α_ f (g ≫ h) i).hom :=
eq_of_inv_eq_inv (by simp only [pentagon_hom_inv_inv_inv_inv, inv_whisker_left,
  is_iso.iso.inv_hom, inv_whisker_right, is_iso.iso.inv_inv, is_iso.inv_comp, assoc])

@[reassoc]
lemma pentagon_hom_inv_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f g (h ≫ i)).hom ≫ (f ◁ (α_ g h i).inv) ≫ (α_ f (g ≫ h) i).inv =
    (α_ (f ≫ g) h i).inv ≫ ((α_ f g h).hom ▷ i) :=
begin
  have pent := pentagon f g h i,
  rw ←inv_comp_eq at pent,
  rw ←pent,
  simp only [hom_inv_whisker_left_assoc, assoc, comp_id, hom_inv_id]
end

@[reassoc]
lemma pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f (g ≫ h) i).hom ≫ (f ◁ (α_ g h i).hom) ≫ (α_ f g (h ≫ i)).inv =
    ((α_ f g h).inv ▷ i) ≫ (α_ (f ≫ g) h i).hom :=
eq_of_inv_eq_inv (by simp only [pentagon_hom_inv_inv_inv_hom, inv_whisker_left,
  is_iso.iso.inv_hom, inv_whisker_right, is_iso.iso.inv_inv, is_iso.inv_comp, assoc])

@[reassoc]
lemma pentagon_inv_hom_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  ((α_ f g h).inv ▷ i) ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
    (α_ f (g ≫ h) i).hom ≫ (f ◁ (α_ g h i).hom) :=
by { rw ←pentagon f g h i, simp only [inv_hom_whisker_right_assoc] }

@[reassoc]
lemma pentagon_inv_inv_hom_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv ≫ ((α_ f g h).hom ▷ i) =
    (f ◁ (α_ g h i).inv) ≫ (α_ f (g ≫ h) i).inv :=
eq_of_inv_eq_inv (by simp only [pentagon_inv_hom_hom_hom_hom, inv_whisker_left,
  is_iso.iso.inv_hom, inv_whisker_right, is_iso.iso.inv_inv, is_iso.inv_comp, assoc])

lemma triangle_assoc_comp_left (f : a ⟶ b) (g : b ⟶ c) :
  (α_ f (𝟙 b) g).hom ≫ (f ◁ (λ_ g).hom) = (ρ_ f).hom ▷ g :=
triangle f g

@[simp, reassoc]
lemma triangle_assoc_comp_right (f : a ⟶ b) (g : b ⟶ c) :
  (α_ f (𝟙 b) g).inv ≫ ((ρ_ f).hom ▷ g) = f ◁ (λ_ g).hom :=
by rw [←triangle, inv_hom_id_assoc]

@[simp, reassoc]
lemma triangle_assoc_comp_right_inv (f : a ⟶ b) (g : b ⟶ c) :
  ((ρ_ f).inv ▷ g) ≫ (α_ f (𝟙 b) g).hom = f ◁ (λ_ g).inv :=
begin
  apply (cancel_mono (f ◁ (λ_ g).hom)).1,
  simp only [inv_hom_whisker_left, inv_hom_whisker_right, assoc, triangle]
end

@[simp, reassoc]
lemma triangle_assoc_comp_left_inv (f : a ⟶ b) (g : b ⟶ c) :
  (f ◁ (λ_ g).inv) ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g :=
begin
  apply (cancel_mono ((ρ_ f).hom ▷ g)).1,
  simp only [triangle_assoc_comp_right, inv_hom_whisker_left, inv_hom_whisker_right, assoc]
end

lemma unitors_equal : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom :=
by rw [←whisker_left_iff, ←cancel_epi (α_ (𝟙 a) (𝟙 _) (𝟙 _)).hom,
       ←cancel_mono (ρ_ (𝟙 a)).hom, triangle, ←right_unitor_comp, right_unitor_naturality]

lemma unitors_inv_equal : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv :=
by { ext, rw [←unitors_equal], simp only [hom_inv_id] }

end

end bicategory

end category_theory
