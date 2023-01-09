/-
Copyright (c) 2023 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/

import category_theory.abelian.basic
import category_theory.abelian.exact
import category_theory.limits.filtered

/-!
# AB5-categories

We define AB5-categories as abelian categories which have all coproducts and all filtered colimits,
and in which the the functor `colim : (J ⥤ C) ⥤ C` is right exact.
-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits

variables (C : Type u) [category.{v} C] [abelian C] [has_coproducts.{v} C]

namespace category_theory

/--
AB5-categories are abelian categories which have all coproducts and all filtered colimits, and
in which the the functor `colim : (J ⥤ C) ⥤ C` is right exact.
-/
class ab5 : Type (max u (v + 1)) :=
(existence [] : ∀ (J : Type v) [small_category J] [is_filtered J], has_colimits_of_shape J C)
(preserves_finite_limits [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  preserves_finite_limits (colim : (J ⥤ C) ⥤ C))

end category_theory
