import category_theory.concrete_category.operations
import algebra.category.Ring.basic
import algebra.category.Group.internal

namespace category_theory

namespace concrete_category

namespace operations

def Ring_zero : operation₀ Ring :=
{ app := λ R, 0, }

def Ring_one : operation₀ Ring :=
{ app := λ R, 1, }

def Ring_neg : operation₁ Ring :=
{ app := λ R x, -x, }

def Ring_add : operation₂ Ring :=
{ app := λ R x, x.1 + x.2, }

def Ring_mul : operation₂ Ring :=
{ app := λ R x, x.1 * x.2, }

end operations

namespace internal

namespace Ring

open concrete_category.operations

variables {C : Type*} [category C]

def mk (R : internal Ab C)
  (yoneda_one : (functor.const Cᵒᵖ).obj punit ⟶ yoneda.obj R.obj)
  (yoneda_mul : concat₂ (yoneda.obj R.obj) (yoneda.obj R.obj) ⟶ yoneda.obj R.obj)
  (yoneda_mul_one : lift₂ (to_functor_const_punit ≫ yoneda_one) (𝟙 _) ≫ yoneda_mul = 𝟙 _)
  (yoneda_mul_mul : lift₂ (pr₁₂_₃ ≫ yoneda_mul) pr₃_₃ ≫ yoneda_mul =
    lift₂ pr₁_₃ (pr₂₃_₃ ≫ yoneda_mul) ≫ yoneda_mul) :
  internal Ring C :=
sorry

end Ring

end internal

end concrete_category

end category_theory
