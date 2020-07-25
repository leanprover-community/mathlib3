/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import category_theory.comma
import topology.simplicial.basic
import topology.category.Top

/-! # Geometric realization of simplicial types -/

universe variables u

open category_theory

namespace sType

@[derive large_category]
def category_of_simplices (X : sType.{u}) :=
comma standard_simplex ((category_theory.functor.const punit.{u+1}).obj X)

/-- The geometric realization of a simplicial type.
This functor is left adjoint to `Top.singular`. -/
def realization : sType ⥤ Top := sorry


end sType
