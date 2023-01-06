import category_theory.abelian.basic
import category_theory.abelian.exact
import category_theory.limits.filtered

universes v u

noncomputable theory

open category_theory
open category_theory.limits

variables (C : Type u) [category.{v} C] [abelian C] [has_coproducts.{v} C]

namespace category_theory

class ab5 : Type (max u (v + 1)) :=
(existence [] : ∀ (J : Type v) [small_category J] [is_filtered J], has_colimits_of_shape J C)
(preserves_finite_limits [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  preserves_finite_limits (colim : (J ⥤ C) ⥤ C))

namespace ab5

variables {C} [ab5 C]

lemma has_colimits_of : has_colimits C :=
has_colimits_of_has_coequalizers_and_coproducts

instance preserves_colimits_colim (J : Type*) [category J] [has_colimits_of_shape J C] :
  preserves_colimits (colim : (J ⥤ C) ⥤ C) :=
adjunction.left_adjoint_preserves_colimits colim_const_adj

end ab5

end category_theory
