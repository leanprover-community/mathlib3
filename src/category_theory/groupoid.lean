/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import category_theory.category
import category_theory.isomorphism

namespace category_theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

class groupoid (obj : Type u) extends category.{v} obj :=
(inv       : Π {X Y : obj}, (X ⟶ Y) → (Y ⟶ X))
(inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y . obviously)
(comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X . obviously)

restate_axiom groupoid.inv_comp'
restate_axiom groupoid.comp_inv'

attribute [simp] groupoid.inv_comp groupoid.comp_inv

abbreviation large_groupoid (C : Type (u+1)) : Type (u+1) := groupoid.{u} C
abbreviation small_groupoid (C : Type u) : Type (u+1) := groupoid.{u} C

instance of_groupoid {C : Type u} [groupoid.{v} C] {X Y : C} (f : X ⟶ Y) : is_iso f :=
{ inv := groupoid.inv f }

end category_theory
