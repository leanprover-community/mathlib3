import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

open category_theory

namespace category_theory.limits

universes v u

variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

@[simps]
def cokernel_image_ι {X Y : C} (f : X ⟶ Y)
  [has_image f] [has_cokernel (image.ι f)] [has_cokernel f]
  [epi (factor_thru_image f)] :
  cokernel (image.ι f) ≅ cokernel f :=
{ hom := cokernel.desc _ (cokernel.π f)
  begin
    have w := cokernel.condition f,
    conv at w { to_lhs, congr, rw ←image.fac f, },
    rw [←has_zero_morphisms.comp_zero (limits.factor_thru_image f), category.assoc, cancel_epi] at w,
    exact w,
  end,
  inv := cokernel.desc _ (cokernel.π _)
  begin
    conv { to_lhs, congr, rw ←image.fac f, },
    rw [category.assoc, cokernel.condition, has_zero_morphisms.comp_zero],
  end, }

end category_theory.limits
