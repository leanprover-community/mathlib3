import algebra.homology2.additive
import algebra.homology2.internal_hom
import algebra.category.Module.abelian
import algebra.category.Module.subobject
import category_theory.limits.shapes.concrete_category
import algebra.category.Module.epi_mono

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

section

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_object V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

structure homotopy (f g : C ⟶ D) extends ihom (-1) C D :=
(comm' : ∀ i, to_ihom.to_pred i i ≫ D.d_to i + C.d_from i ≫ to_ihom.from_succ i i + g.f i = f.f i)

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

theorem homology_map_eq_of_homotopy (h : homotopy f g) (i : ι) :
  (homology_functor V c i).map f = (homology_functor V c i).map g :=
begin
  dsimp [homology_functor],
  ext,
  simp only [cokernel.π_desc],
  dunfold cycles_map,
  simp only [←h.comm' i],
  simp only [add_zero, zero_comp,
    cycles_arrow_d_from_assoc, preadditive.comp_add],
  apply eq_of_sub_eq_zero, -- move this higher, needs some lemmas
  rw [←preadditive.sub_comp],
  suffices h :
    (D.cycles i).factor_thru ((C.cycles i).arrow ≫ h.to_ihom.to_pred i i ≫ D.d_to i) _ ≫
      cokernel.π (D.boundaries_to_cycles i) = 0,
  { simp [h], },
  { dsimp [cycles],
    erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
    { simp, },
    { rw [←category.assoc],
      apply image_subobject_factors_comp_self, }, },
end

end
