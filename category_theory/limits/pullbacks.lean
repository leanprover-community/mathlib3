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

open walking_cospan

inductive walking_cospan_hom : walking_cospan → walking_cospan → Type v
| inl : walking_cospan_hom left one
| inr : walking_cospan_hom right one
| id : Π X : walking_cospan.{v}, walking_cospan_hom X X

open walking_cospan_hom

instance walking_cospan_category : small_category walking_cospan :=
{ hom := walking_cospan_hom,
  id := walking_cospan_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
  end }

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan ⥤ C :=
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

variables {X Y Z : C}

def square (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

variables {f : X ⟶ Z} {g : Y ⟶ Z}

def is_pullback (t : square f g) := is_limit t

variables {t : square f g}

instance is_pullback_subsingleton : subsingleton (is_pullback t) := by dsimp [is_pullback]; apply_instance

variable (C)

class has_pullbacks :=
(square : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), square.{u v} f g)
(is_pullback : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), is_pullback (square f g) . obviously)

-- Special cases of this may be marked with [instance] as desired.
def has_pullbacks_of_has_limits [limits.has_limits.{u v} C] : has_pullbacks.{u v} C :=
{ square := λ X Y Z f g, limit.cone (cospan f g),
  is_pullback := λ X Y Z f g, limit.universal_property (cospan f g) }

variable {C}

section
variable [has_pullbacks.{u v} C]
variables (f g)

def pullback.square : square f g := has_pullbacks.square.{u v} f g
def pullback := (pullback.square f g).X
def pullback.π₁ : pullback f g ⟶ X := (pullback.square f g).π left
def pullback.π₂ : pullback f g ⟶ Y := (pullback.square f g).π right
@[simp] lemma pullback.w : pullback.π₁ f g ≫ f = pullback.π₂ f g ≫ g :=
begin
  erw ((pullback.square f g).w inl),
  erw ((pullback.square f g).w inr)
end
def pullback.universal_property : is_pullback (pullback.square f g) :=
has_pullbacks.is_pullback.{u v} C f g

end

end category_theory.limits
