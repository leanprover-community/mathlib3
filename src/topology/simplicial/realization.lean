/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import category_theory.comma
import topology.simplicial.simplex_category
import topology.category.Top

/-! # Geometric realization of simplicial types -/

universe variables u

open category_theory

namespace sType

open simplex_category

@[derive category]
def category_of_simplices (X : sType.{u}) :=
comma (skeletal_functor ⋙ standard_simplex) ((category_theory.functor.const punit.{1}).obj X)

set_option pp.universes true

#print category_of_simplices.category

/-- The geometric realization of a simplicial type.
This functor is left adjoint to `Top.singular`. -/
def realization : sType ⥤ Top := sorry


end sType
