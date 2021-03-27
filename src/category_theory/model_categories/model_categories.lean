import category_theory.model_categories.arrow_classes

namespace category_theory

universes v v' u u'

namespace category_theory

open category_theory

variables {M : Type u} [category.{v} M]

class model_category (obj : Type u) extends category.{v} u  :=
  (finite_lim : limits.has_finite_limits M)
  (finite_colim : limits.has_finite_colimits M)
  (W C F : arrow_cond M)
  (W_23 : two_out_of_three W)
  (weak_factorization_system_C_WF : weak_factorization_system C (W ∩ F))
  (weak_factorization_system_WC_F : weak_factorization_system (W ∩ C) F)

variables [model_category M]
end category_theory
