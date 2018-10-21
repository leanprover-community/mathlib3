import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes u v w

inductive walking_cospan
| left | right | one

open walking_cospan

inductive walking_cospan_hom : walking_cospan → walking_cospan → Type
| inl : walking_cospan_hom left one
| inr : walking_cospan_hom right one
| id : Π X : walking_cospan, walking_cospan_hom X X

open walking_cospan_hom

instance walking_cospan_category : category walking_cospan :=
{ hom := walking_cospan_hom,
  id := walking_cospan_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
  end }

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {β : Type v}

def fan (f : β → C) := cone (functor.of_function f)

variables {f : β → C}

def is_product (t : fan f) := is_limit t

variables {t : fan f}

instance is_product_subsingleton : subsingleton (is_product t) := by dsimp [is_product]; apply_instance

variable (C)

class has_products :=
(fan : Π {β : Type v} (f : β → C), fan.{u v} f)
(is_product : Π {β : Type v} (f : β → C), is_product (fan f) . obviously)
