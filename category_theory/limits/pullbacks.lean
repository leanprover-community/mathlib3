import category_theory.limits.limits

open category_theory

namespace tactic
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed
end tactic

namespace category_theory.limits

universes u v w

local attribute [tidy] tactic.case_bash

inductive walking_cospan : Type v
| left | right | one
inductive walking_span : Type v
| zero | left | right

open walking_cospan
open walking_span

inductive walking_cospan_hom : walking_cospan → walking_cospan → Type v
| inl : walking_cospan_hom left one
| inr : walking_cospan_hom right one
| id : Π X : walking_cospan.{v}, walking_cospan_hom X X
inductive walking_span_hom : walking_span → walking_span → Type v
| inl : walking_span_hom zero left
| inr : walking_span_hom zero right
| id : Π X : walking_span.{v}, walking_span_hom X X

open walking_cospan_hom
open walking_span_hom

instance walking_cospan_category : small_category walking_cospan :=
{ hom := walking_cospan_hom,
  id := walking_cospan_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
  end }
instance walking_span_category : small_category walking_span :=
{ hom := walking_span_hom,
  id := walking_span_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id left) := inl
  | _, _, _, inr, (id right) := inr
  end }

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan.{v} ⥤ C :=
{ obj := λ x, match x with
  | left := X
  | right := Y
  | one := Z
  end,
  map' := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl := f
  | _, _, inr := g
  end }
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | left := Y
  | right := Z
  end,
  map' := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl := f
  | _, _, inr := g
  end }

variables {X Y Z : C}

section pullback
def square (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

variables {f : X ⟶ Z} {g : Y ⟶ Z}

def is_pullback (t : square f g) := is_limit t

variables {t : square f g}

instance is_pullback_subsingleton : subsingleton (is_pullback t) := by dsimp [is_pullback]; apply_instance
end pullback

section pushout
def cosquare (f : X ⟶ Y) (g : X ⟶ Z) := cocone (span f g)

variables {f : X ⟶ Y} {g : X ⟶ Z}

def is_pushout (t : cosquare f g) := is_colimit t

variables {t : cosquare f g}

instance is_pushout_subsingleton : subsingleton (is_pushout t) := by dsimp [is_pushout]; apply_instance
end pushout

variable (C)

class has_pullbacks :=
(square : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), square.{u v} f g)
(is_pullback : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), is_pullback (square f g) . obviously)
class has_pushouts :=
(cosquare : Π {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), cosquare.{u v} f g)
(is_pushout : Π {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), is_pushout (cosquare f g) . obviously)

-- Special cases of this may be marked with [instance] as desired.
def has_pullbacks_of_has_limits [limits.has_limits_of_shape.{u v} walking_cospan C] : has_pullbacks.{u v} C :=
{ square := λ X Y Z f g, limit.cone (cospan f g),
  is_pullback := λ X Y Z f g, limit.universal_property (cospan f g) }
def has_pushouts_of_has_colimits [limits.has_colimits_of_shape.{u v} walking_span C] : has_pushouts.{u v} C :=
{ cosquare := λ X Y Z f g, colimit.cocone (span f g),
  is_pushout := λ X Y Z f g, colimit.universal_property (span f g) }

variable {C}

section pullback
variable [has_pullbacks.{u v} C]
variables (f : X ⟶ Z) (g : Y ⟶ Z)

def pullback.square : square f g := has_pullbacks.square.{u v} f g
def pullback := (pullback.square f g).X
def pullback.π₁ : pullback f g ⟶ X := (pullback.square f g).π.app left
def pullback.π₂ : pullback f g ⟶ Y := (pullback.square f g).π.app right
@[simp] lemma pullback.w : pullback.π₁ f g ≫ f = pullback.π₂ f g ≫ g :=
begin
  erw ((pullback.square f g).w inl),
  erw ((pullback.square f g).w inr)
end
def pullback.universal_property : is_pullback (pullback.square f g) :=
has_pullbacks.is_pullback.{u v} C f g

instance has_limits_of_shape_of_has_pullbacks [has_pullbacks.{u v} C] : 
  limits.has_limits_of_shape.{u v} walking_cospan C :=
sorry

-- TODO
-- pullback.lift
-- pullback.lift_π₁
-- pullback.lift_π₂
-- pullback.hom_ext


end pullback

-- TODO pushout

end category_theory.limits
