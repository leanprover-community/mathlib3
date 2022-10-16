import category_theory.monoidal.Mon_
import category_theory.monoidal.of_has_finite_products
import algebra.category.Group.biproducts
import algebra.category.Group.limits

noncomputable theory

namespace category_theory

open category_theory.limits

instance (R : Mon_ AddCommGroup) : ring R.X :=
let i : ∀ (X Y : AddCommGroup), (AddCommGroup.of (X × Y)) ≅ X ⨯ Y :=
  λ X Y, ((AddCommGroup.binary_product_limit_cone X Y).is_limit.cone_point_unique_up_to_iso
    (limit.is_limit _)) in
{ one := R.one 0,
  mul := λ x y, R.mul $
    ((AddCommGroup.binary_product_limit_cone _ _).is_limit.cone_point_unique_up_to_iso
      (limit.is_limit _)).hom ⟨x, y⟩,
  one_mul := λ x, begin
    dsimp, simp only [map_zero],
    have := (prod.left_unitor R.X).inv,
    have := fun_like.congr_fun R.one_mul ((prod.left_unitor R.X).hom x),
    rw [Mon_.one_mul_hom, category.comp_id, eq_self_iff_true] at this,
    change _ = (prod.left_unitor R.X).hom ((i _ R.X).hom ⟨0, x⟩) at this,

  end,..(infer_instance : add_comm_group R.X) }

end category_theory
