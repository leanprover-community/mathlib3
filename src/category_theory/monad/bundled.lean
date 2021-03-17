/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.monad.basic
import category_theory.eq_to_hom

/-!
# Bundled Monads

We define bundled (co)monads as a structure consisting of a functor `func : C ⥤ C` endowed with
a term of type `(co)monad func`. See `category_theory.monad.basic` for the definition.
The type of bundled (co)monads on a category `C` is denoted `(Co)Monad C`.

We also define morphisms of bundled (co)monads as morphisms of their underlying (co)monads
in the sense of `category_theory.(co)monad_hom`. We construct a category instance on `(Co)Monad C`.
-/

namespace category_theory
open category

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables (C : Type u) [category.{v} C]

end category_theory
