/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import data.opposite

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/

open opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universes v v₁ v₂ u u₁ u₂

/--
A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class quiver (V : Type u) :=
(hom : V → V → Sort v)

infixr ` ⟶ `:10 := quiver.hom -- type as \h

/--
A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure prefunctor (V : Type u₁) [quiver.{v₁} V] (W : Type u₂) [quiver.{v₂} W] :=
(obj [] : V → W)
(map : Π {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y))

namespace prefunctor

@[ext]
lemma ext {V : Type u} [quiver.{v₁} V] {W : Type u₂} [quiver.{v₂} W]
  {F G : prefunctor V W}
  (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ (X Y : V) (f : X ⟶ Y),
           F.map f = eq.rec_on (h_obj Y).symm (eq.rec_on (h_obj X).symm (G.map f))) : F = G :=
begin
  cases F with F_obj _, cases G with G_obj _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext X Y f,
  simpa using h_map X Y f,
end

/--
The identity morphism between quivers.
-/
@[simps]
def id (V : Type*) [quiver V] : prefunctor V V :=
{ obj := id,
  map := λ X Y f, f, }

instance (V : Type*) [quiver V] : inhabited (prefunctor V V) := ⟨id V⟩

/--
Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type*} [quiver U] {V : Type*} [quiver V] {W : Type*} [quiver W]
  (F : prefunctor U V) (G : prefunctor V W) : prefunctor U W :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y f, G.map (F.map f), }

@[simp]
lemma comp_assoc
  {U V W Z : Type*} [quiver U] [quiver V] [quiver W] [quiver Z]
  (F : prefunctor U V) (G : prefunctor V W) (H : prefunctor W Z) :
  (F.comp G).comp H = F.comp (G.comp H) := rfl

infix ` ⥤q `:50 := prefunctor

infix ` ⋙q `:50 := prefunctor.comp

notation `𝟭q` := id

end prefunctor

namespace quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [quiver V] : quiver Vᵒᵖ :=
⟨λ a b, (unop b) ⟶ (unop a)⟩

/--
The opposite of an arrow in `V`.
-/
def hom.op {V} [quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := f
/--
Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def hom.unop {V} [quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := f

attribute [irreducible] quiver.opposite

/-- A type synonym for a quiver with no arrows. -/
@[nolint has_nonempty_instance]
def empty (V) : Type u := V

instance empty_quiver (V : Type u) : quiver.{u} (empty V) := ⟨λ a b, pempty⟩

@[simp] lemma empty_arrow {V : Type u} (a b : empty V) : (a ⟶ b) = pempty := rfl

/-- A quiver is thin if it has no parallel arrows. -/
@[reducible] def is_thin (V : Type u) [quiver V] := ∀ (a b : V), subsingleton (a ⟶ b)

section push
/-!
### Pushing the quiver structure on `V` along a map `V → W`
-/

variables {V : Type*} [quiver V] {W : Type*} (σ : V → W)

/-- The `quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unused_arguments]
def push (σ : V → W) := W

instance [h : nonempty W] : nonempty (push σ) := h

/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint has_nonempty_instance]
inductive push_quiver {V : Type u} [quiver.{v} V] {W : Type u₂} (σ : V → W) :
  W → W → Type (max u u₂ v)
| arrow {X Y : V} (f : X ⟶ Y) : push_quiver (σ X) (σ Y)

instance : quiver (push σ) := ⟨push_quiver σ⟩

namespace push

/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q push σ :=
{ obj := σ,
  map := λ X Y f, push_quiver.arrow f}

@[simp] lemma of_obj : ((of σ)).obj = σ := rfl

variables {W' : Type*} [quiver W'] (φ : prefunctor V W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x) )

include φ h

/-- Any map `φ : V → W'` factoring through `τ : W → W'` lifts to a prefunctor from `V` to `W`. -/
def lift : push σ ⥤q W' :=
{ obj := τ,
  map := @push_quiver.rec V _ W σ
    (λ X Y f, τ X ⟶ τ Y)
    (λ X Y f, by { rw [←h X, ←h Y], exact φ.map f, }) }

lemma lift_spec_obj : (lift σ φ τ h).obj = τ := rfl

lemma lift_spec_comp : of σ ⋙q lift σ φ τ h = φ :=
begin
  fapply prefunctor.ext,
  { rintros, simp only [prefunctor.comp_obj], symmetry, exact h X, },
  { rintros _ _ f, simp only [prefunctor.comp_map],
    apply eq_of_heq,
    iterate 2 { apply (cast_heq _ _).trans },
    symmetry,
    iterate 2 { apply (eq_rec_heq _ _).trans },
    refl, },
end

lemma lift_unique (Φ : push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : of σ ⋙q Φ = φ) :
  Φ = lift σ φ τ h :=
begin
  dsimp only [of,lift],
  fapply prefunctor.ext,
  { rintros, simp_rw [←Φ₀], },
  { rintros _ _ ⟨⟩, subst_vars, simp only [prefunctor.comp_map, cast_eq], refl, }
end

end push

end push

end quiver

