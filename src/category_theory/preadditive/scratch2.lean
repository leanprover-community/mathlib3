import category_theory.limits.shapes.biproducts
import algebra.homology.exact

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

instance [has_equalizers C] : has_coequalizers Cᵒᵖ := sorry
instance [has_coequalizers C] : has_equalizers Cᵒᵖ := sorry
-- instance [has_images C] : has_images Cᵒᵖ := sorry
instance [has_zero_morphisms C] [has_cokernels C] : has_kernels Cᵒᵖ := sorry

instance exact.op [has_zero_morphisms C] [has_equalizers C] [has_images C] [has_images Cᵒᵖ]
  [has_coequalizers C]
  {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [exact f g] : exact g.op f.op := sorry

end category_theory
