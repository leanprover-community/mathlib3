/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import topology.sheaves.sheaf
import category_theory.full_subcategory

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

variables (C : Type u) [category.{v} C] [limits.has_products C]

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace C :=
(sheaf_condition : sheaf_condition 𝒪)

variables {C}

namespace SheafedSpace

instance coe_carrier : has_coe (SheafedSpace C) Top :=
{ coe := λ X, X.carrier }

@[simp] lemma as_coe (X : SheafedSpace C) : X.carrier = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (carrier) (𝒪) (h) : (({ carrier := carrier, 𝒪 := 𝒪, sheaf_condition := h } :
  SheafedSpace.{v} C) : Top.{v}) = carrier := rfl

instance (X : SheafedSpace.{v} C) : topological_space X := X.carrier.str

instance : category (SheafedSpace C) :=
show category (induced_category (PresheafedSpace C) SheafedSpace.to_PresheafedSpace),
by apply_instance

def To_PresheafedSpace : (SheafedSpace C) ⥤ (PresheafedSpace C) :=
induced_functor _

variables (C)

section
local attribute [simp] id comp presheaf.pushforward

variables {C}

@[simp] lemma id_base (X : SheafedSpace C) :
  ((𝟙 X) : X ⟶ X).base = (𝟙 (X : Top.{v})) := rfl

lemma id_c (X : SheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c =
  (((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id (X.carrier)).hom) _)) := rfl

@[simp] lemma id_c_app (X : SheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = eq_to_hom (by { op_induction U, cases U, refl }) :=
by { op_induction U, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

-- Implementation note: this harmless looking lemma causes deterministic timeouts,
-- but happily we can survive without it.
-- lemma comp_c {X Y Z : SheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
--   (α ≫ β).c = (β.c ≫ (whisker_left (opens.map β.f).op α.c)) := rfl

@[simp] lemma comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U))) ≫
    (Top.presheaf.pushforward.comp _ _ _).inv.app U := rfl

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f.base }

end

end SheafedSpace

end algebraic_geometry
