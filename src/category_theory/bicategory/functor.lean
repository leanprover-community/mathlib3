/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

/-!
# Oplax functors and pseudofunctors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (obj a ⟶ obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (map f ⟶ map g)`,
* a family of 2-morphisms `F.map_id a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.map_comp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.
A pseudofunctor is an oplax functor whose `map_id` and `map_comp` are isomorphisms.

## Main definitions

* `oplax_functor B C` : an oplax functor between bicategories `B` and `C`
* `oplax_functor.comp F G` : the composition of oplax functors
* `pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`
* `pseudofunctor.comp F G` : the composition of pseudofunctors

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
variables (B : Type u₁) [quiver.{v₁+1} B] [∀ a b : B, quiver.{w₁+1} (a ⟶ b)]
variables (C : Type u₂) [quiver.{v₂+1} C] [∀ a b : C, quiver.{w₂+1} (a ⟶ b)]

/--
A prelax functor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `oplax_functor`.
-/
structure prelax_functor extends prefunctor B C :=
(map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g))

/-- The prefunctor between the underlying quivers. -/
add_decl_doc prelax_functor.to_prefunctor

namespace prelax_functor

variables {B C} {D : Type u₃} [quiver.{v₃+1} D] [∀ a b : D, quiver.{w₃+1} (a ⟶ b)]
variables (F : prelax_functor B C) (G : prelax_functor C D)

instance has_coe_to_prefunctor : has_coe (prelax_functor B C) (prefunctor B C) := ⟨to_prefunctor⟩

@[simp] lemma to_prefunctor_eq_coe : F.to_prefunctor = F := rfl
@[simp] lemma to_prefunctor_obj : (F : prefunctor B C).obj = F.obj := rfl
@[simp] lemma to_prefunctor_map : (F : prefunctor B C).map = F.map := rfl

variables (B)

/-- The identity prelax functor. -/
@[simps]
def id : prelax_functor B B :=
{ map₂ := λ a b f g η, η, .. prefunctor.id B }

instance : inhabited (prelax_functor B B) := ⟨prelax_functor.id B⟩

variables {B}

/-- Composition of prelax functors. -/
@[simps]
def comp : prelax_functor B D :=
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
map₂ (α_ f g h).hom ≫ map_comp f (g ≫ h) ≫ (map f ◁ map_comp g h) =
  map_comp (f ≫ g) h ≫ (map_comp f g ▷ map h) ≫ (α_ (map f) (map g) (map h)).hom

variables (B C)

/--
An oplax functor `F` between bicategories `B` and `C` consists of functions between objects,
1-morphisms, and 2-morphisms.

Unlike functors between categories, functions between 1-morphisms do not need to strictly commute
with compositions, and do not need to strictly preserve the identity. Instead, there are
specified 2-morphisms `F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

Functions between 2-morphisms strictly commute with compositions and preserve the identity.
They also preserve the associator, the left unitor, and the right unitor modulo some adjustments
of domains and codomains of 2-morphisms.
-/
structure oplax_functor extends prelax_functor B C :=
(map_id (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a))
(map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g)
(map_comp_naturality_left' : ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
  map₂ (η ▷ g) ≫ map_comp f' g = map_comp f g ≫ (map₂ η ▷ map g) . obviously)
(map_comp_naturality_right' : ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
  map₂ (f ◁ η) ≫ map_comp f g' = map_comp f g ≫ (map f ◁ map₂ η) . obviously)
(map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) . obviously)
(map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  oplax_functor.map₂_associator_aux obj (λ a b, map) (λ a b f g, map₂) (λ a b c, map_comp) f g h
    . obviously)
(map₂_left_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (λ_ f).hom = map_comp (𝟙 a) f ≫ (map_id a ▷ map f) ≫ (λ_ (map f)).hom . obviously)
(map₂_right_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (ρ_ f).hom = map_comp f (𝟙 b) ≫ (map f ◁ map_id b) ≫ (ρ_ (map f)).hom . obviously)

restate_axiom oplax_functor.map_comp_naturality_left'
restate_axiom oplax_functor.map_comp_naturality_right'
restate_axiom oplax_functor.map₂_id'
restate_axiom oplax_functor.map₂_comp'
restate_axiom oplax_functor.map₂_associator'
restate_axiom oplax_functor.map₂_left_unitor'
restate_axiom oplax_functor.map₂_right_unitor'
attribute [simp]
  oplax_functor.map_comp_naturality_left oplax_functor.map_comp_naturality_right
  oplax_functor.map₂_id oplax_functor.map₂_associator
attribute [reassoc]
  oplax_functor.map_comp_naturality_left oplax_functor.map_comp_naturality_right
  oplax_functor.map₂_comp oplax_functor.map₂_associator
  oplax_functor.map₂_left_unitor oplax_functor.map₂_right_unitor
attribute [simp]
  oplax_functor.map₂_comp oplax_functor.map₂_left_unitor oplax_functor.map₂_right_unitor

variables {B C}

namespace oplax_functor

section
variables (F : oplax_functor B C) (G : oplax_functor C D)

/-- Function between 1-morphisms as a functor. -/
@[simps]
def map_functor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
{ obj := λ f, F.map f,
  map := λ f g η, F.map₂ η }

/-- The prelax functor between the underlying quivers. -/
add_decl_doc oplax_functor.to_prelax_functor

instance has_coe_to_prelax : has_coe (oplax_functor B C) (prelax_functor B C) :=
⟨to_prelax_functor⟩

@[simp] lemma to_prelax_eq_coe : F.to_prelax_functor = F := rfl
@[simp] lemma to_prelax_functor_obj : (F : prelax_functor B C).obj = F.obj := rfl
@[simp] lemma to_prelax_functor_map : (F : prelax_functor B C).map = F.map := rfl
@[simp] lemma to_prelax_functor_map₂ : (F : prelax_functor B C).map₂ = F.map₂ := rfl

variables (B)

/-- The identity oplax functor. -/
@[simps]
def id : oplax_functor B B :=
{ map_id := λ a, 𝟙 (𝟙 a),
  map_comp := λ a b c f g, 𝟙 (f ≫ g),
  .. prelax_functor.id B }

instance : inhabited (oplax_functor B B) := ⟨id B⟩

variables {B}

/-- Composition of oplax functors. -/
@[simps]
def comp : oplax_functor B D :=
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
      whisker_right_comp, assoc] },
  map₂_left_unitor' := λ a b f, by
  { dsimp,
    simp only [map₂_left_unitor, map₂_comp, map_comp_naturality_left_assoc,
      whisker_right_comp, assoc] },
  map₂_right_unitor' := λ a b f, by
  { dsimp,
    simp only [map₂_right_unitor, map₂_comp, map_comp_naturality_right_assoc,
      whisker_left_comp, assoc] },
  .. (F : prelax_functor B C).comp ↑G }

structure pseudo_core (F : oplax_functor B C) :=
(map_id_iso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a))
(map_comp_iso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g)
(map_id_iso_hom' : ∀ {a : B}, (map_id_iso a).hom = F.map_id a . obviously)
(map_comp_iso_hom' : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
  (map_comp_iso f g).hom = F.map_comp f g . obviously)

restate_axiom pseudo_core.map_id_iso_hom'
restate_axiom pseudo_core.map_comp_iso_hom'
attribute [simp] pseudo_core.map_id_iso_hom pseudo_core.map_comp_iso_hom

class is_pseudo : Prop :=
(map_id_is_iso' : ∀ (a : B), is_iso (F.map_id a) . tactic.apply_instance)
(map_comp_is_iso' : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
  is_iso (F.map_comp f g) . tactic.apply_instance)

restate_axiom is_pseudo.map_id_is_iso'
restate_axiom is_pseudo.map_comp_is_iso'
attribute [instance] is_pseudo.map_id_is_iso is_pseudo.map_comp_is_iso

end

end oplax_functor

/--
The auxiliary definition that claims that pseudofunctors preserve the associators
modulo some adjustments of domains and codomains of 2-morphisms. -/
/-
The reason for using this auxiliary definition instead of writing it directly in the definition
of pseudofunctors is that doing so will cause a timeout.
-/
@[simp]
def pseudofunctor.map₂_associator_aux
  (obj : B → C) (map : Π {X Y : B}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (map₂ : Π {a b : B} {f g : a ⟶ b}, (f ⟶ g) → (map f ⟶ map g))
  (map_comp : Π {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ≅ map f ≫ map g)
  {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : Prop :=
map₂ (α_ f g h).hom = (map_comp (f ≫ g) h).hom ≫ ((map_comp f g).hom ▷ map h) ≫
  (α_ (map f) (map g) (map h)).hom ≫ (map f ◁ (map_comp g h).inv) ≫ (map_comp f (g ≫ h)).inv

variables (B C)

/--
A pseudofunctors `F` between bicategories `B` and `C` consists of functions between objects,
1-morphisms, and 2-morphisms.

Unlike functors between categories, functions between 1-morphisms do not need to strictly commute
with compositions, and do not need to strictly preserve the identity. Instead, there are
specified 2-isomorphisms `F.map (𝟙 a) ≅ 𝟙 (F.obj a)` and `F.map (f ≫ g) ≅ F.map f ≫ F.map g`.

Functions between 2-morphisms strictly commute with compositions and preserve the identity.
They also preserve the associator, the left unitor, and the right unitor modulo some adjustments
of domains and codomains of 2-morphisms.
-/
structure pseudofunctor extends prelax_functor B C :=
(map_id (a : B) : map (𝟙 a) ≅ 𝟙 (obj a))
(map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g)
(map₂_whisker_right' : ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
  map₂ (η ▷ h) = (map_comp f h).hom ≫ (map₂ η ▷ map h) ≫ (map_comp g h).inv . obviously)
(map₂_whisker_left' : ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
  map₂ (f ◁ η) = (map_comp f g).hom ≫ (map f ◁ map₂ η) ≫ (map_comp f h).inv . obviously)
(map₂_id' : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) . obviously)
(map₂_comp' : ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
  map₂ (η ≫ θ) = map₂ η ≫ map₂ θ . obviously)
(map₂_associator' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
  pseudofunctor.map₂_associator_aux obj (λ a b, map) (λ a b f g, map₂) (λ a b c, map_comp) f g h
    . obviously)
(map₂_left_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (λ_ f).hom = (map_comp (𝟙 a) f).hom ≫ ((map_id a).hom ▷ map f) ≫ (λ_ (map f)).hom
    . obviously)
(map₂_right_unitor' : ∀ {a b : B} (f : a ⟶ b),
  map₂ (ρ_ f).hom = (map_comp f (𝟙 b)).hom ≫ (map f ◁ (map_id b).hom) ≫ (ρ_ (map f)).hom
    . obviously)

restate_axiom pseudofunctor.map₂_whisker_right'
restate_axiom pseudofunctor.map₂_whisker_left'
restate_axiom pseudofunctor.map₂_id'
restate_axiom pseudofunctor.map₂_comp'
restate_axiom pseudofunctor.map₂_associator'
restate_axiom pseudofunctor.map₂_left_unitor'
restate_axiom pseudofunctor.map₂_right_unitor'
attribute [simp]
  pseudofunctor.map₂_whisker_right pseudofunctor.map₂_whisker_left
  pseudofunctor.map₂_id pseudofunctor.map₂_associator
attribute [reassoc]
  pseudofunctor.map₂_whisker_right pseudofunctor.map₂_whisker_left
  pseudofunctor.map₂_comp pseudofunctor.map₂_associator
  pseudofunctor.map₂_left_unitor pseudofunctor.map₂_right_unitor
attribute [simp]
  pseudofunctor.map₂_comp pseudofunctor.map₂_left_unitor pseudofunctor.map₂_right_unitor

variables {B C}

namespace pseudofunctor

section
open iso
variables (F : pseudofunctor B C) (G : pseudofunctor C D)

/-- Function on 1-morphisms as a functor. -/
@[simps]
def map_functor {a b : B} : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) :=
{ obj := λ f, F.map f,
  map := λ f g η, F.map₂ η }

/-- The prelax functor between the underlying quivers. -/
add_decl_doc pseudofunctor.to_prelax_functor

instance has_coe_to_prelax : has_coe (pseudofunctor B C) (prelax_functor B C) :=
⟨to_prelax_functor⟩

@[simp] lemma to_prelax_eq_coe : F.to_prelax_functor = F := rfl
@[simp] lemma to_prelax_functor_obj : (F : prelax_functor B C).obj = F.obj := rfl
@[simp] lemma to_prelax_functor_map : (F : prelax_functor B C).map = F.map := rfl
@[simp] lemma to_prelax_functor_map₂ : (F : prelax_functor B C).map₂ = F.map₂ := rfl

/-- The oplax functor associated with a pseudofunctor. -/
def to_oplax : oplax_functor B C :=
{ map_id := λ a, (F.map_id a).hom,
  map_comp := λ a b c f g, (F.map_comp f g).hom,
  .. (F : prelax_functor B C) }

instance has_coe_to_oplax : has_coe (pseudofunctor B C) (oplax_functor B C) := ⟨to_oplax⟩

@[simp] lemma to_oplax_eq_coe : F.to_oplax = F := rfl
@[simp] lemma to_oplax_obj : (F : oplax_functor B C).obj = F.obj := rfl
@[simp] lemma to_oplax_map : (F : oplax_functor B C).map = F.map := rfl
@[simp] lemma to_oplax_map₂ : (F : oplax_functor B C).map₂ = F.map₂ := rfl
@[simp] lemma to_oplax_map_id (a : B) : (F : oplax_functor B C).map_id a = (F.map_id a).hom := rfl
@[simp] lemma to_oplax_map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
  (F : oplax_functor B C).map_comp f g = (F.map_comp f g).hom := rfl

variables (B)

/-- The identity pseudofunctor. -/
@[simps]
def id : pseudofunctor B B :=
{ map_id := λ a, iso.refl (𝟙 a),
  map_comp := λ a b c f g, iso.refl (f ≫ g),
  .. prelax_functor.id B }

instance : inhabited (pseudofunctor B B) := ⟨id B⟩

variables {B}

/-- Composition of pseudofunctors. -/
@[simps]
def comp : pseudofunctor B D :=
{ map_id := λ a, G.map_functor.map_iso (F.map_id a) ≪≫ G.map_id (F.obj a),
  map_comp := λ a b c f g,
    G.map_functor.map_iso (F.map_comp f g) ≪≫ G.map_comp (F.map f) (F.map g),
  .. (F : prelax_functor B C).comp ↑G }

/--
Construct a pseudofunctor from an oplax functor whose `map_id` and `map_comp` are isomorphisms.
-/
def mk_of_oplax {F : oplax_functor B C} (F' : oplax_functor.pseudo_core F) : pseudofunctor B C :=
{ map_id := F'.map_id_iso,
  map_comp := F'.map_comp_iso,
  map₂_whisker_right' := λ a b c f g η h, by
  { dsimp,
    rw [F'.map_comp_iso_hom f h, ←F.map_comp_naturality_left_assoc,
      ←F'.map_comp_iso_hom g h, hom_inv_id, comp_id] },
  map₂_whisker_left' := λ a b c f g h η, by
  { dsimp,
    rw [F'.map_comp_iso_hom f g, ←F.map_comp_naturality_right_assoc,
      ←F'.map_comp_iso_hom f h, hom_inv_id, comp_id] },
  map₂_associator' := λ a b c d f g h, by
  { dsimp,
    rw [F'.map_comp_iso_hom (f ≫ g) h, F'.map_comp_iso_hom f g, ←F.map₂_associator_assoc,
      ←F'.map_comp_iso_hom f (g ≫ h), ←F'.map_comp_iso_hom g h,
      hom_inv_whisker_left_assoc, hom_inv_id, comp_id] },
  .. (F : prelax_functor B C) }

/--
Construct a pseudofunctor from an oplax functor whose `map_id` and `map_comp` are isomorphisms.
-/
noncomputable
def mk_of_oplax' {F : oplax_functor B C} [oplax_functor.is_pseudo F] : pseudofunctor B C :=
{ map_id := λ a, as_iso (F.map_id a),
  map_comp := λ a b c f g, as_iso (F.map_comp f g),
  map₂_whisker_right' := λ a b c f g η h, by
  { dsimp,
    rw [←assoc, is_iso.eq_comp_inv, F.map_comp_naturality_left] },
  map₂_whisker_left' := λ a b c f g h η, by
  { dsimp,
    rw [←assoc, is_iso.eq_comp_inv, F.map_comp_naturality_right] },
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
