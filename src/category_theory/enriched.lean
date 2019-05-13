import category_theory.types
import category_theory.monoidal.types
import category_theory.monoidal.functor

universes v u

open category_theory
open category_theory.monoidal

namespace category_theory

variables (C : Sort u)
variables (V : Sort v) [𝒱 : monoidal_category.{v} V]
include 𝒱

class enriched_over (F : lax_monoidal_functor.{v v} V (Sort v)) extends category.{v} C :=
(e_hom : C → C → V)
(e_id : )

end category_theory
