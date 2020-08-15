import category_theory.abelian.basic
import algebra.homology.exact

universes v u

open category_theory
open category_theory.limits
open category_theory.preadditive

variables {C : Type u} [category.{v} C] [abelian C]

namespace category_theory.abelian
variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

local attribute [instance] has_equalizers_of_has_kernels

--set_option pp.all true

lemma exact_iff' {cg : kernel_fork g} (hg : is_limit cg)
  {cf : cokernel_cofork f} (hf : is_colimit cf) : exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 :=
begin
  split,
  { introI h,
    exact ⟨h.1, bla' f g cg cf⟩ },
  { refine λ h, ⟨h.1, _⟩,
    suffices hl : is_limit (kernel_fork.of_ι (image.ι f) ((epi_iff_cancel_zero (factor_thru_image f)).1
      (by apply_instance) _ (image.ι f ≫ g) (by simp [h.1]))),
    { have : image_to_kernel_map f g h.1 = (is_limit.cone_point_unique_up_to_iso hl (limit.is_limit _)).hom,
      { ext,
        simp only [image.fac, category.assoc, kernel.lift_ι],
        rw is_limit.cone_point_unique_up_to_iso_hom_comp hl (limit.is_limit _)
          walking_parallel_pair.zero,

        simp,
       },
      rw this,
      apply_instance },

     }
end

theorem exact_iff : exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 :=
exact_iff' f g (limit.is_limit _) (colimit.is_colimit _)

end category_theory.abelian
