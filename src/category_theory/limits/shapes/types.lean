/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.types
import category_theory.limits.shapes.products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `category_theory.limits.types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `punit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`.

It is not intended that these definitions will be global instances:
they should be turned on as needed.

The exception to this rule is that the monoidal category structure on `Type`
uses these definitions.
-/

universes u

open category_theory
open category_theory.limits

namespace category_theory.limits.types

/-- The category of types has `punit` as a terminal object. -/
def types_has_terminal : has_terminal (Type u) :=
{ has_limit := λ F,
  { cone :=
    { X := punit,
      π := by tidy, },
    is_limit := by tidy, } }

open category_theory.limits.walking_pair

local attribute [tidy] tactic.case_bash

/--
The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
def types_has_binary_products : has_binary_products (Type u) :=
{ has_limit := λ F,
  { cone :=
    { X := F.obj left × F.obj right,
      π :=
      { app := by { rintro ⟨_|_⟩, exact prod.fst, exact prod.snd, } }, },
    is_limit :=
    { lift := λ s x, (s.π.app left x, s.π.app right x),
      uniq' := λ s m w,
      begin
        ext,
        exact congr_fun (w left) x,
        exact congr_fun (w right) x,
      end }, } }

/--
The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def types_has_products : has_products (Type u) := λ J,
{ has_limit := λ F,
  { cone :=
    { X := Π j, F.obj j,
      π :=
      { app := λ j f, f j }, },
    is_limit :=
    { lift := λ s x j, s.π.app j x,
      uniq' := λ s m w,
      begin
        ext x j,
        have := congr_fun (w j) x,
        exact this,
      end }, } }

local attribute [instance, priority 200] types_has_products
-- We slightly increase the priority of `types_has_terminal` and `types_has_binary_products`
-- so that they come ahead of `types_has_products`.
local attribute [instance, priority 300] types_has_terminal
local attribute [instance, priority 300] types_has_binary_products

@[simp] lemma terminal : (⊤_ (Type u)) = punit := rfl
lemma terminal_from {P : Type u} (f : P ⟶ ⊤_ (Type u)) (p : P) : f p = punit.star :=
by ext

@[simp] lemma prod (X Y : Type u) : limits.prod X Y = prod X Y := rfl
@[simp] lemma prod_fst {X Y : Type u} (p : limits.prod X Y) :
  (@limits.prod.fst.{u} _ _ X Y _ : limits.prod X Y → X) p = p.1 := rfl
@[simp] lemma prod_snd {X Y : Type u} (p : limits.prod X Y) :
  (@limits.prod.snd.{u} _ _ X Y _ : limits.prod X Y → Y) p = p.2 := rfl

@[simp] lemma prod_lift {X Y Z : Type u} {f : X ⟶ Y} {g : X ⟶ Z} :
  limits.prod.lift f g = (λ x, (f x, g x)) := rfl
@[simp] lemma prod_map {W X Y Z : Type u} {f : W ⟶ X} {g : Y ⟶ Z} :
  limits.prod.map f g = (λ p : W × Y, (f p.1, g p.2)) := rfl

@[simp] lemma pi {J : Type u} (f : J → Type u) : pi_obj f = Π j, f j := rfl
@[simp] lemma pi_π {J : Type u} {f : J → Type u} (j : J) (g : pi_obj f) :
  (pi.π f j : pi_obj f → f j) g = g j := rfl

@[simp] lemma pi_lift {J : Type u} {f : J → Type u} {W : Type u} {g : Π j, W ⟶ f j} :
  pi.lift g = (λ w j, g j w) := rfl
@[simp] lemma pi_map {J : Type u} {f g : J → Type u} {h : Π j, f j ⟶ g j} :
  pi.map h = λ (k : Π j, f j) j, h j (k j) := rfl

end category_theory.limits.types
