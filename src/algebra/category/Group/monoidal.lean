import category_theory.monoidal.of_has_finite_products
import category_theory.monoidal.Mon_
import algebra.category.Group.limits
import algebra.category.Group.biproducts

noncomputable theory

namespace AddCommGroup

open category_theory category_theory.monoidal_category category_theory.limits

instance : category_theory.monoidal_category AddCommGroup :=
category_theory.monoidal_of_has_finite_products _

instance (R : Mon_ AddCommGroup) : ring R.X :=
{ one := R.one 0,
  mul := λ x y, R.mul sorry,
  one_mul := sorry,
  mul_one := sorry,
  mul_assoc := sorry,
  ..(infer_instance : add_comm_group R.X) }


end AddCommGroup
