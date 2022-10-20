import category_theory.concrete_category.operations
import algebra.category.Ring.basic

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

end concrete_category

end category_theory
