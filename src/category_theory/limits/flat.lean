import category_theory.limits.filtered_colimit_commutes_finite_limit
import category_theory.elements
import category_theory.limits.preserves.limits

namespace category_theory
open limits

universes w₁ w₂ v₁ v₂ u₁ u₂

variables (J : Type v₁) [small_category J]
variables (C : Type u₁) [category.{v₂} C]
variables (F : C ⥤ Type v₂) (hF : is_filtered F.elementsᵒᵖ)

set_option pp.universes true

def my_thm (hF : is_filtered F.elementsᵒᵖ) :
  preserves_limits_of_shape J F :=
begin
  have := F.elementsᵒᵖ,
  have θ : F.elementsᵒᵖ × J ⥤ Type v₁, sorry,
  have := limits.colimit_limit_to_limit_colimit_is_iso θ,
end

end category_theory
