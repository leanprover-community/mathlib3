/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison

Defines a category, as a typeclass parametrised by the type of objects.
Introduces notations
  `X ⟶ Y` for the morphism spaces,
  `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

import tactic.restate_axiom
import tactic.replacer
import tactic.interactive

namespace category_theory

universes u v

/- 
The propositional fields of `category` are annotated with the auto_param `obviously`, which is just a synonym for `skip`.
Actually, there is a tactic called `obviously` which is not part of this pull request, which should be used here. It successfully
discharges a great many of these goals. For now, proofs which could be provided entirely by `obviously` (and hence omitted entirely
and discharged by an auto_param), are all marked with a comment "-- obviously says:".
-/
def_replacer obviously

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be specified explicitly, as `category.{u v} C`. (See also `large_category` and `small_category`.)
-/
class category (obj : Type u) : Type (max u (v+1)) :=
(hom      : obj → obj → Type v)
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
(id_comp' : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f . obviously)
(comp_id' : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f . obviously)
(assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp f g) h = comp f (comp g h) . obviously)

notation `𝟙` := category.id -- type as \b1
infixr ` ≫ `:80 := category.comp -- type as \gg
infixr ` ⟶ `:10 := category.hom -- type as \h

-- `restate_axiom` is a command that creates a lemma from a structure field, discarding any auto_param wrappers from the type.
-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)
restate_axiom category.id_comp'
restate_axiom category.comp_id'
restate_axiom category.assoc'
attribute [simp] category.id_comp category.comp_id category.assoc

/--
A `large_category` has objects in one universe level higher than the universe level of the morphisms. 
It is useful for examples such as the category of types, or the category of groups, etc.
-/
abbreviation large_category (C : Type (u+1)) : Type (u+1) := category.{u+1 u} C
/--
A `small_category` has objects and morphisms in the same universe level.
-/
abbreviation small_category (C : Type u)     : Type (u+1) := category.{u u} C

variables {C : Type u} [𝒞 : category.{u v} C] {X Y Z : C}
include 𝒞

class epi  (f : X ⟶ Y) : Prop := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) : Prop :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

@[simp] lemma cancel_epi  (f : X ⟶ Y) [epi f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h := 
⟨ λ p, epi.left_cancellation g h p, begin intro a, subst a end ⟩
@[simp] lemma cancel_mono (f : X ⟶ Y) [mono f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h := 
⟨ λ p, mono.right_cancellation g h p, begin intro a, subst a end ⟩


end category_theory
