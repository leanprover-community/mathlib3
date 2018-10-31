import category_theory.limits.limits
import category_theory.limits.pullbacks

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes u v w

inductive walking_pair : Type v
| zero | one

open walking_pair

inductive walking_pair_hom : walking_pair → walking_pair → Type v
| inl : walking_pair_hom zero one
| inr : walking_pair_hom zero one
| id : Π X : walking_pair.{v}, walking_pair_hom X X

open walking_pair_hom

instance walking_pair_category : small_category walking_pair :=
{ hom := walking_pair_hom,
  id := walking_pair_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
  end }

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def pair {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : walking_pair.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | one := Y
  end,
  map' := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl := f
  | _, _, inr := g
  end }

variables {X Y : C}

def fork (f : X ⟶ Y) (g : X ⟶ Y) := cone (pair f g)

variables {f : X ⟶ Y} {g : X ⟶ Y}

def is_equalizer (t : fork f g) := is_limit t

variables {t : fork f g}

instance is_equalizer_subsingleton : subsingleton (is_equalizer t) := by dsimp [is_equalizer]; apply_instance

variable (C)

class has_equalizers :=
(fork : Π {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y), fork.{u v} f g)
(is_equalizer : Π {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y), is_equalizer (fork f g) . obviously)

-- Special cases of this may be marked with [instance] as desired.
def has_equalizers_of_has_limits [limits.has_limits.{u v} C] : has_equalizers.{u v} C :=
{ fork := λ X Y f g, limit.cone (pair f g),
  is_equalizer := λ X Y f g, limit.universal_property (pair f g) }

variable {C}

section
variable [has_equalizers.{u v} C]
variables (f g)

def equalizer.fork : fork f g := has_equalizers.fork.{u v} f g
def equalizer := (equalizer.fork f g).X
def equalizer.ι : equalizer f g ⟶ X := (equalizer.fork f g).π.app zero
@[simp] lemma equalizer.w : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
begin
  erw ((equalizer.fork f g).w inl),
  erw ((equalizer.fork f g).w inr)
end
def equalizer.universal_property : is_equalizer (equalizer.fork f g) :=
has_equalizers.is_equalizer.{u v} C f g

end

end category_theory.limits
