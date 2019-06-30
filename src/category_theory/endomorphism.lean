import category_theory.category category_theory.isomorphism algebra.group.units data.equiv.algebra

universes v u

namespace category_theory
variables {C : Type u} [𝒞_struct : category_struct.{v+1} C] (X : C)
include 𝒞_struct

def End (X : C) := X ⟶ X

variables {X}

instance End.has_one : has_one (End X) := ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
instance End.has_mul : has_mul (End X) := ⟨λ x y, y ≫ x⟩

@[simp] lemma End.one_def : (1 : End X) = 𝟙 X := rfl

@[simp] lemma End.mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl

omit 𝒞_struct
variable [𝒞 : category.{v+1} C]
include 𝒞

instance End.monoid : monoid (End X) :=
by refine { .. End.has_one, .. End.has_mul, .. }; dsimp [has_mul.mul,has_one.one]; obviously

def Aut (X : C) := X ≅ X

attribute [extensionality Aut] iso.ext

instance: group (Aut X) :=
by refine { one := iso.refl X,
            inv := iso.symm,
            mul := flip iso.trans, .. } ; dunfold flip; obviously

def units_End_eqv_Aut : (units (End X)) ≃* Aut X :=
{ to_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  inv_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  left_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  right_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  hom := ⟨λ f g, by rcases f; rcases g; refl⟩ }
end category_theory
