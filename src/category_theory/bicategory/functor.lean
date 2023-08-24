/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

/-!
# Oplax functors and pseudofunctors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.map_id a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.map_comp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

A pseudofunctor is an oplax functor whose `map_id` and `map_comp` are isomorphisms. We provide
several constructors for pseudofunctors:
* `pseudofunctor.mk` : the default constructor, which requires `map₂_whisker_left` and
  `map₂_whisker_right` instead of naturality of `map_comp`.
* `pseudofunctor.mk_of_oplax` : construct a pseudofunctor from an oplax functor whose
  `map_id` and `map_comp` are isomorphisms. This constructor uses `iso` to describe isomorphisms.
* `pseudofunctor.mk_of_oplax'` : similar to `mk_of_oplax`, but uses `is_iso` to describe
  isomorphisms.

The additional constructors are useful when constructing a pseudofunctor where the construction
of the oplax functor associated with it is already done. For example, the composition of
pseudofunctors can be defined by using the composition of oplax functors as follows:
```lean
def pseudofunctor.comp (F : pseudofunctor B C) (G : pseudofunctor C D) : pseudofunctor B D :=
mk_of_oplax ((F : oplax_functor B C).comp G)
{ map_id_iso := λ a, (G.map_functor _ _).map_iso (F.map_id a) ≪≫ G.map_id (F.obj a),
  map_comp_iso := λ a b c f g,
    (G.map_functor _ _).map_iso (F.map_comp f g) ≪≫ G.map_comp (F.map f) (F.map g) }
```
although the composition of pseudofunctors in this file is defined by using the default constructor
because `obviously` is smart enough. Similarly, the composition is also defined by using
`mk_of_oplax'` after giving appropriate instances for `is_iso`. The former constructor
`mk_of_oplax` requires isomorphisms as data type `iso`, and so it is useful if you don't want
to forget the definitions of the inverses. On the other hand, the latter constructor
`mk_of_oplax'` is useful if you want to use propositional type class `is_iso`.

## Main definitions

* `category_theory.oplax_functor B C` : an oplax functor between bicategories `B` and `C`
* `category_theory.oplax_functor.comp F G` : the composition of oplax functors
* `category_theory.pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`
* `category_theory.pseudofunctor.comp F G` : the composition of pseudofunctors

## Future work

There are two types of functors between bicategories, called lax and oplax functors, depending on
the directions of `map_id` and `map_comp`. We may need both in mathlib in the future, but for
now we only define oplax functors.
-/

set_option old_structure_cmd true

namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section
variables {B : Type u₁} [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
variables {C : Type u₂} [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]
variables {D : Type u₃} [quiver.{v₃+1} D] [∀ a b : D, quiver.{w₃+1} (a ⟶ b)]

/--
A prelax functor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `oplax_functor`.
-/
structure prelax_functor
  (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
  (C : Type u₂) [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)] extends prefunctor B C :=
(map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g))

/-- The prefunctor between the underlying quivers. -/
add_decl_doc prelax_functor.to_prefunctor

namespace prelax_functor

instance has_coe_to_prefunctor : has_coe (prelax_functor B C) (prefunctor B C) := ⟨to_prefunctor⟩

variables (F : prelax_functor B C)

@[simp] lemma to_prefunctor_eq_coe : F.to_prefunctor = F := rfl
@[simp] lemma to_prefunctor_obj : (F : prefunctor B C).obj = F.obj := rfl
@[simp] lemma to_prefunctor_map : @prefunctor.map B _ C _ F = @map _ _ _ _ _ _ F := rfl

/-- The identity prelax functor. -/
@[simps]
def id (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)] : prelax_functor B B :=
{ map₂ := λ a b f g η, η, .. prefunctor.id B }

instance : inhabited (prelax_functor B B) := ⟨prelax_functor.id B⟩

/-- Composition of prelax functors. -/
@[simps]
def comp (F : prelax_functor B C) (G : prelax_functor C D) : prelax_functor B D :=
{ map₂ := λ a b f g η, G.map₂ (F.map₂ η), .. (F : prefunctor B C).comp ↑G }

end prelax_functor

end

section
variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables {D : Type u₃} [bicategory.{w₃ v₃} D]

/--
This auxiliary definition states that oplax functors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
We use this auxiliary definition instead of writing it directly in the definition
of oplax functors because doing so will cause a timeout.
-/
@[simp]
def oplax_functor.map₂_associator_aux
  (obj : B → C) (map : Π {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (map₂ : Π {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
  (map_comp : Π {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ⟶ map f ≫ map g)
  {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
map₂ (α_ f g h).hom ≫ map_comp f (g ≫ h) ≫ map f ◁ map_comp g h =
  map_comp (f ≫ g) h ≫ map_comp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom

/--
An oplax functor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` do not need to strictly commute with the composition,
and do not need to strictly preserve the identity. Instead, there are specified 2-morphisms
`F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

`F.map₂` strictly commute with compositions and preserve the identity. They also preserve the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure oplax_functor (B : Type u₁) [bicategory.{w₁ v₁} B] (C : Type u₂) [bicategory.{w₂ v₂} C]
  extends prelax_functor B C :=
(map_id (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a))
(map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g)
(map_comp_naturality_left' : ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
  map₂ (η ▷ g) ≫ map_comp f' g = map_comp f g ≫ map₂ η ▷ map g . obviously)
(map_comp_naturality_right' : ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
  map₂ (f ◁ η) ≫ map_comp f g' = map_comp f g ≫ map f ◁ map₂ η . obviously)
(map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) . obviously)
(map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  oplax_functor.map₂_associator_aux obj (λ _ _, map) (λ a b f g, map₂) (λ a b c, map_comp) f g h
    . obviously)
(map₂_left_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (λ_ f).hom = map_comp (𝟙 a) f ≫ map_id a ▷ map f ≫ (λ_ (map f)).hom . obviously)
(map₂_right_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (ρ_ f).hom = map_comp f (𝟙 b) ≫ map f ◁ map_id b ≫ (ρ_ (map f)).hom . obviously)

namespace oplax_functor

restate_axiom map_comp_naturality_left'
restate_axiom map_comp_naturality_right'
restate_axiom map₂_id'
restate_axiom map₂_comp'
restate_axiom map₂_associator'
restate_axiom map₂_left_unitor'
restate_axiom map₂_right_unitor'
attribute [simp] map_comp_naturality_left map_comp_naturality_right map₂_id map₂_associator
attribute [reassoc]
  map_comp_naturality_left map_comp_naturality_right map₂_comp
  map₂_associator map₂_left_unitor map₂_right_unitor
attribute [simp] map₂_comp map₂_left_unitor map₂_right_unitor

section

/-- The prelax functor between the underlying quivers. -/
add_decl_doc oplax_functor.to_prelax_functor

instance has_coe_to_prelax : has_coe (oplax_functor B C) (prelax_functor B C) :=
⟨to_prelax_functor⟩

variables (F : oplax_functor B C)

@[simp] lemma to_prelax_eq_coe : F.to_prelax_functor = F := rfl
@[simp] lemma to_prelax_functor_obj : (F : prelax_functor B C).obj = F.obj := rfl
@[simp] lemma to_prelax_functor_map : @prelax_functor.map B _ _ C _ _ F = @map _ _ _ _ F := rfl
@[simp] lemma to_prelax_functor_map₂ : @prelax_functor.map₂ B _ _ C _ _ F = @map₂ _ _ _ _ F := rfl

/-- Function between 1-morphisms as a functor. -/
@[simps]
def map_functor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
{ obj := λ f, F.map f,
  map := λ f g η, F.map₂ η }

/-- The identity oplax functor. -/
@[simps]
def id (B : Type u₁) [bicategory.{w₁ v₁} B] : oplax_functor B B :=
{ map_id := λ a, 𝟙 (𝟙 a),
  map_comp := λ a b c f g, 𝟙 (f ≫ g),
  .. prelax_functor.id B }

instance : inhabited (oplax_functor B B) := ⟨id B⟩

/-- Composition of oplax functors. -/
@[simps]
def comp (F : oplax_functor B C) (G : oplax_functor C D) : oplax_functor B D :=
{ map_id := λ a,
    (G.map_functor _ _).map (F.map_id a) ≫ G.map_id (F.obj a),
  map_comp := λ a b c f g,
    (G.map_functor _ _).map (F.map_comp f g) ≫ G.map_comp (F.map f) (F.map g),
  map_comp_naturality_left' := λ a b c f f' η g, by
  { dsimp,
    rw [←map₂_comp_assoc, map_comp_naturality_left, map₂_comp_assoc, map_comp_naturality_left,
      assoc] },
  map_comp_naturality_right' := λ a b c f g g' η, by
  { dsimp,
    rw [←map₂_comp_assoc, map_comp_naturality_right, map₂_comp_assoc, map_comp_naturality_right,
      assoc] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp,
    simp only [map₂_associator, ←map₂_comp_assoc, ←map_comp_naturality_right_assoc,
      whisker_left_comp, assoc],
    simp only [map₂_associator, map₂_comp, map_comp_naturality_left_assoc,
      comp_whisker_right, assoc] },
  map₂_left_unitor' := λ a b f, by
  { dsimp,
    simp only [map₂_left_unitor, map₂_comp, map_comp_naturality_left_assoc,
      comp_whisker_right, assoc] },
  map₂_right_unitor' := λ a b f, by
  { dsimp,
    simp only [map₂_right_unitor, map₂_comp, map_comp_naturality_right_assoc,
      whisker_left_comp, assoc] },
  .. (F : prelax_functor B C).comp ↑G }

/--
A structure on an oplax functor that promotes an oplax functor to a pseudofunctor.
See `pseudofunctor.mk_of_oplax`.
-/
@[nolint has_nonempty_instance]
structure pseudo_core (F : oplax_functor B C) :=
(map_id_iso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a))
(map_comp_iso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g)
(map_id_iso_hom' : ∀ {a : B}, (map_id_iso a).hom = F.map_id a . obviously)
(map_comp_iso_hom' : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
  (map_comp_iso f g).hom = F.map_comp f g . obviously)

restate_axiom pseudo_core.map_id_iso_hom'
restate_axiom pseudo_core.map_comp_iso_hom'
attribute [simp] pseudo_core.map_id_iso_hom pseudo_core.map_comp_iso_hom

end

end oplax_functor

/--
This auxiliary definition states that pseudofunctors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
We use this auxiliary definition instead of writing it directly in the definition
of pseudofunctors because doing so will cause a timeout.
-/
@[simp]
def pseudofunctor.map₂_associator_aux
  (obj : B → C) (map : Π {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (map₂ : Π {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
  (map_comp : Π {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ≅ map f ≫ map g)
  {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
map₂ (α_ f g h).hom = (map_comp (f ≫ g) h).hom ≫ (map_comp f g).hom ▷ map h ≫
  (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (map_comp g h).inv ≫ (map_comp f (g ≫ h)).inv

/--
A pseudofunctor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` do not need to strictly commute with the compositions,
and do not need to strictly preserve the identity. Instead, there are specified 2-isomorphisms
`F.map (𝟙 a) ≅ 𝟙 (F.obj a)` and `F.map (f ≫ g) ≅ F.map f ≫ F.map g`.

`F.map₂` strictly commute with compositions and preserve the identity. They also preserve the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure pseudofunctor (B : Type u₁) [bicategory.{w₁ v₁} B] (C : Type u₂) [bicategory.{w₂ v₂} C]
  extends prelax_functor B C :=
(map_id (a : B) : map (𝟙 a) ≅ 𝟙 (obj a))
(map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g)
(map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) . obviously)
(map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_whisker_left' : ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
  map₂ (f ◁ η) = (map_comp f g).hom ≫ map f ◁ map₂ η ≫ (map_comp f h).inv . obviously)
(map₂_whisker_right' : ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
  map₂ (η ▷ h) = (map_comp f h).hom ≫ map₂ η ▷ map h ≫ (map_comp g h).inv . obviously)
(map₂_associator' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  pseudofunctor.map₂_associator_aux obj (λ a b, map) (λ a b f g, map₂) (λ a b c, map_comp) f g h
    . obviously)
(map₂_left_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (λ_ f).hom = (map_comp (𝟙 a) f).hom ≫ (map_id a).hom ▷ map f ≫ (λ_ (map f)).hom
    . obviously)
(map₂_right_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (ρ_ f).hom = (map_comp f (𝟙 b)).hom ≫ map f ◁ (map_id b).hom ≫ (ρ_ (map f)).hom
    . obviously)

namespace pseudofunctor

restate_axiom map₂_id'
restate_axiom map₂_comp'
restate_axiom map₂_whisker_left'
restate_axiom map₂_whisker_right'
restate_axiom map₂_associator'
restate_axiom map₂_left_unitor'
restate_axiom map₂_right_unitor'
attribute [reassoc]
  map₂_comp map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor
attribute [simp]
  map₂_id map₂_comp map₂_whisker_left map₂_whisker_right
  map₂_associator map₂_left_unitor map₂_right_unitor

section
open iso

/-- The prelax functor between the underlying quivers. -/
add_decl_doc pseudofunctor.to_prelax_functor

instance has_coe_to_prelax_functor : has_coe (pseudofunctor B C) (prelax_functor B C) :=
⟨to_prelax_functor⟩

variables (F : pseudofunctor B C)

@[simp] lemma to_prelax_functor_eq_coe : F.to_prelax_functor = F := rfl
@[simp] lemma to_prelax_functor_obj : (F : prelax_functor B C).obj = F.obj := rfl
@[simp] lemma to_prelax_functor_map : @prelax_functor.map B _ _ C _ _ F = @map _ _ _ _ F := rfl
@[simp] lemma to_prelax_functor_map₂ : @prelax_functor.map₂ B _ _ C _ _ F = @map₂ _ _ _ _ F := rfl

/-- The oplax functor associated with a pseudofunctor. -/
def to_oplax : oplax_functor B C :=
{ map_id := λ a, (F.map_id a).hom,
  map_comp := λ a b c f g, (F.map_comp f g).hom,
  .. (F : prelax_functor B C) }

instance has_coe_to_oplax : has_coe (pseudofunctor B C) (oplax_functor B C) := ⟨to_oplax⟩

@[simp] lemma to_oplax_eq_coe : F.to_oplax = F := rfl
@[simp] lemma to_oplax_obj : (F : oplax_functor B C).obj = F.obj := rfl
@[simp] lemma to_oplax_map : @oplax_functor.map B _ C _ F = @map _ _ _ _ F := rfl
@[simp] lemma to_oplax_map₂ : @oplax_functor.map₂ B _ C _ F = @map₂ _ _ _ _ F := rfl
@[simp] lemma to_oplax_map_id (a : B) : (F : oplax_functor B C).map_id a = (F.map_id a).hom := rfl
@[simp] lemma to_oplax_map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
  (F : oplax_functor B C).map_comp f g = (F.map_comp f g).hom := rfl

/-- Function on 1-morphisms as a functor. -/
@[simps]
def map_functor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
(F : oplax_functor B C).map_functor a b

/-- The identity pseudofunctor. -/
@[simps]
def id (B : Type u₁) [bicategory.{w₁ v₁} B] : pseudofunctor B B :=
{ map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, iso.refl (f ≫ g),
  .. prelax_functor.id B }

instance : inhabited (pseudofunctor B B) := ⟨id B⟩

/-- Composition of pseudofunctors. -/
@[simps]
def comp (F : pseudofunctor B C) (G : pseudofunctor C D) : pseudofunctor B D :=
{ map_id := λ a, (G.map_functor _ _).map_iso (F.map_id a) ≪≫ G.map_id (F.obj a),
  map_comp := λ a b c f g,
    (G.map_functor _ _).map_iso (F.map_comp f g) ≪≫ G.map_comp (F.map f) (F.map g),
  .. (F : prelax_functor B C).comp ↑G }

/--
Construct a pseudofunctor from an oplax functor whose `map_id` and `map_comp` are isomorphisms.
-/
@[simps]
def mk_of_oplax (F : oplax_functor B C) (F' : F.pseudo_core) : pseudofunctor B C :=
{ map_id := F'.map_id_iso,
  map_comp := λ _ _ _, F'.map_comp_iso,
  map₂_whisker_left' := λ a b c f g h η, by
  { dsimp,
    rw [F'.map_comp_iso_hom f g, ←F.map_comp_naturality_right_assoc,
      ←F'.map_comp_iso_hom f h, hom_inv_id, comp_id] },
  map₂_whisker_right' := λ a b c f g η h, by
  { dsimp,
    rw [F'.map_comp_iso_hom f h, ←F.map_comp_naturality_left_assoc,
      ←F'.map_comp_iso_hom g h, hom_inv_id, comp_id] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp,
    rw [F'.map_comp_iso_hom (f ≫ g) h, F'.map_comp_iso_hom f g, ←F.map₂_associator_assoc,
      ←F'.map_comp_iso_hom f (g ≫ h), ←F'.map_comp_iso_hom g h,
      hom_inv_whisker_left_assoc, hom_inv_id, comp_id] },
  .. (F : prelax_functor B C) }

/--
Construct a pseudofunctor from an oplax functor whose `map_id` and `map_comp` are isomorphisms.
-/
@[simps]
noncomputable
def mk_of_oplax' (F : oplax_functor B C)
  [∀ a, is_iso (F.map_id a)] [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), is_iso (F.map_comp f g)] :
  pseudofunctor B C :=
{ map_id := λ a, as_iso (F.map_id a),
  map_comp := λ a b c f g, as_iso (F.map_comp f g),
  map₂_whisker_left' := λ a b c f g h η, by
  { dsimp,
    rw [←assoc, is_iso.eq_comp_inv, F.map_comp_naturality_right] },
  map₂_whisker_right' := λ a b c f g η h, by
  { dsimp,
    rw [←assoc, is_iso.eq_comp_inv, F.map_comp_naturality_left] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp,
    simp only [←assoc],
    rw [is_iso.eq_comp_inv, ←inv_whisker_left, is_iso.eq_comp_inv],
    simp only [assoc, F.map₂_associator] },
  .. (F : prelax_functor B C) }

end

end pseudofunctor

end

end category_theory
