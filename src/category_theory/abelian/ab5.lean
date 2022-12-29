import category_theory.abelian.basic
import category_theory.abelian.exact
import category_theory.limits.filtered

universes w' w v u

noncomputable theory

open category_theory
open category_theory.limits

variables {C : Type u} [category.{v} C] [abelian C]

namespace category_theory

class ab5 : Type (max u (v + 1)) :=
(existence : ∀ (J : Type v) [small_category J] [is_filtered J], has_colimits_of_shape J C)
(preserves_finite_limits [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  preserves_finite_limits (limits.colim : (J ⥤ C) ⥤ C))
(preserves_finite_colimits [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  preserves_finite_colimits (limits.colim : (J ⥤ C) ⥤ C))

end category_theory
