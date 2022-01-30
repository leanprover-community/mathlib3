import algebraic_geometry.pullbacks
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.limits.constructions.equalizers

open category_theory category_theory.limits opposite

namespace algebraic_geometry

lemma has_finite_limits_of_has_terminal_has_pullbacks
  {C : Type*} [category C] [has_terminal C] [has_pullbacks C] : has_finite_limits C :=
@@finite_limits_from_equalizers_and_finite_products _
  (@@has_finite_products_of_has_binary_and_terminal _
    (has_binary_products_of_terminal_and_pullbacks C) infer_instance)
  (@@has_equalizers_of_pullbacks_and_binary_products _
    (has_binary_products_of_terminal_and_pullbacks C) infer_instance)

noncomputable
def Spec_Z_is_terminal : is_terminal (Scheme.Spec.obj (op $ CommRing.of ℤ)) :=
(terminal_op_of_initial CommRing.Z_is_initial).is_terminal_obj Scheme.Spec _

instance : has_terminal Scheme := has_terminal_of_has_terminal_of_preserves_limit Scheme.Spec

instance : has_finite_limits Scheme :=
has_finite_limits_of_has_terminal_has_pullbacks


end algebraic_geometry
