import topology.homotopy.basic
import category_theory.quotient
import topology.category.Top

def homotopic : hom_rel Top := λ x y, continuous_map.homotopic

instance : category_theory.congruence homotopic :=
{ is_equiv := λ x y,
  { refl := continuous_map.homotopic.refl,
    trans := continuous_map.homotopic.trans,
    symm := continuous_map.homotopic.symm },
  comp_left := λ x y z f g g' h, continuous_map.homotopic.hcomp (by refl) h,
  comp_right := λ x y z f f' g h, continuous_map.homotopic.hcomp h (by refl) }

@[derive category_theory.category]
def hTop := category_theory.quotient homotopic
