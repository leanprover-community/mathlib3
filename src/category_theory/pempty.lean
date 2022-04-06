/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.discrete_category

/-!
# The empty category

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/

universes w v u -- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
namespace functor

variables (C : Type u) [category.{v} C]

/-- Equivalence between two empty categories. -/
def empty_equivalence : discrete.{w} pempty ≌ discrete.{v} pempty :=
equivalence.mk
{ obj := pempty.elim, map := λ x, x.elim }
{ obj := pempty.elim, map := λ x, x.elim }
(by tidy) (by tidy)

/-- The canonical functor out of the empty category. -/
def empty : discrete.{w} pempty ⥤ C := discrete.functor pempty.elim

variable {C}
/-- Any two functors out of the empty category are isomorphic. -/
def empty_ext (F G : discrete.{w} pempty ⥤ C) : F ≅ G :=
discrete.nat_iso (λ x, pempty.elim x)

/--
Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
def unique_from_empty (F : discrete.{w} pempty ⥤ C) : F ≅ empty C :=
empty_ext _ _

/--
Any two functors out of the empty category are *equal*. You probably want to use
`empty_ext` instead of this.
-/
lemma empty_ext' (F G : discrete.{w} pempty ⥤ C) : F = G :=
functor.ext (λ x, x.elim) (λ x _ _, x.elim)

end functor

end category_theory
