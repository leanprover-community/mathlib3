import category_theory.monoidal.category
import algebra.category.Group.limits

noncomputable theory

namespace Group

open category_theory category_theory.monoidal_category category_theory.limits

instance : monoidal_category Group :=
{ tensor_obj := λ X Y, X ⨯ Y,
  tensor_hom := λ X1 Y1 X2 Y2 f g, limits.prod.map f g,
  tensor_id' := λ _ _, limits.prod.map_id_id,
  tensor_comp' := λ _ _ _ _ _ _ f1 f2 g1 g2, begin
    ext1,
  end,
  tensor_unit := _,
  associator := _,
  associator_naturality' := _,
  left_unitor := _,
  left_unitor_naturality' := _,
  right_unitor := _,
  right_unitor_naturality' := _,
  pentagon' := _,
  triangle' := _ }


end Group
