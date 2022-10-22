import category_theory.concrete_category.operations
import algebra.category.Ring.basic
import algebra.category.Group.internal

universe v

def Ring.mk (R : Ab) (one' : R) (mul' : R × R → R)
  (mul_assoc : ∀ (x y z : R), mul' ⟨mul' ⟨x, y⟩, z⟩ = mul' ⟨x, mul' ⟨y, z⟩⟩)
  (one_mul : ∀ (x : R), mul' ⟨one', x⟩ = x)
  (mul_one : ∀ (x : R), mul' ⟨x, one'⟩ = x)
  (add_mul : ∀ (x y z : R), mul' ⟨x + y, z⟩ = mul' ⟨x, z⟩ + mul' ⟨y, z⟩)
  (mul_add : ∀ (x y z : R), mul' ⟨x, y + z⟩ = mul' ⟨x, y⟩ + mul' ⟨x, z⟩) : Ring :=
⟨R.1,
{ add := λ x y, x+y,
  neg := λ x, -x ,
  zero := 0,
  zero_add := by tidy,
  add_zero := by tidy,
  add_assoc := add_assoc,
  add_left_neg := add_left_neg,
  add_comm := add_comm,
  one := one',
  mul := λ x y, mul' ⟨x, y⟩,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := mul_add,
  right_distrib := add_mul, }⟩

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
  (yoneda_one : internal_yoneda_operation₀ R.obj)
  (yoneda_mul : Ab.yoneda_bilinear R R R)
  (yoneda_one_mul : internal_yoneda_operation₂_gen.one_smul yoneda_mul.φ yoneda_one)
  (yoneda_mul_one : internal_yoneda_operation₂_gen.smul_one yoneda_mul.φ yoneda_one)
  (yoneda_mul_mul : internal_yoneda_operation₂_gen.mul_smul yoneda_mul.φ yoneda_mul.φ) :
  internal Ring C :=
{ obj := R.obj,
  presheaf :=
  { obj := λ Y, begin
      refine Ring.mk (R.presheaf.obj Y) (yoneda_one.to_presheaf Y)
        (yoneda_mul.φ.on_internal_presheaf.app Y) _ _ _ _ _,
      { sorry, },
      { sorry, },
      { sorry, },
      { intros x₁ x₁' x₂,
        simp only [internal_yoneda_operation₂_gen.on_internal_presheaf_app,
          Ab.yoneda_bilinear.on_internal_presheaf_right_distrib], },
      { intros x₁ x₂ x₂',
        simp only [internal_yoneda_operation₂_gen.on_internal_presheaf_app,
          Ab.yoneda_bilinear.on_internal_presheaf_left_distrib], },
    end,
    map := λ Y Y' f, ⟨R.presheaf_type.map f, yoneda_one.to_presheaf_map f,
      yoneda_mul.φ.on_internal_presheaf_curry_naturality f,
      (R.presheaf.map f).map_zero, (R.presheaf.map f).map_add⟩, },
  iso := sorry, }

end Ring

end internal

end concrete_category

end category_theory
