import category_theory.abelian.basic
import algebra.homology.exact

universes v u

open category_theory
open category_theory.limits
open category_theory.preadditive

variables {C : Type u} [category.{v} C] [abelian C]

namespace category_theory.abelian
variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma exact_iff' {kg : kernel_fork g} (hkg : is_limit kg)
  {cf : cokernel_cofork f} (hcf : is_colimit cf) : exact f g ↔ f ≫ g = 0 ∧ kg.ι ≫ cf.π = 0 :=
begin
  refine ⟨λ h, ⟨h.1, _⟩, λ h, ⟨h.1, _⟩⟩,
  { --have := (epi_iff_cancel_zero _).1 h.2 _ _,
    apply (mono_iff_cancel_zero (is_colimit.cocone_point_unique_up_to_iso hcf (colimit.is_colimit _)).hom).1
      (by apply_instance),
    apply (epi_iff_cancel_zero (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) hkg).hom).1
      (by apply_instance),
    simp,

  }
end

theorem exact_iff : exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 :=
exact_iff' f g (limit.is_limit _) (colimit.is_colimit _)

end category_theory.abelian
