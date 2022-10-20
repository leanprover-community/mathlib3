import category_theory.concrete_category.internal
import algebra.category.Group.preadditive
import category_theory.internal_operation

noncomputable theory

def Ab.mk (A : Type*) (zero' : A) (neg' : A ⟶ A) (add' : A × A → A)
  (add_assoc' : ∀ (x y z : A), add' ⟨add' ⟨x, y⟩, z⟩ = add' ⟨x, add' ⟨y, z⟩⟩)
  (add_comm' : ∀ (x y : A), add' ⟨x, y⟩ = add' ⟨y, x⟩)
  (zero_add' : ∀ (x : A), add' ⟨zero', x⟩ = x)
  (add_left_neg' : ∀ (x : A), add' ⟨neg' x, x⟩ = zero') :
  Ab :=
⟨A,
{ zero := zero',
  neg := neg',
  add := λ x y, add' ⟨x, y⟩,
  add_assoc := add_assoc',
  add_comm := add_comm',
  zero_add := zero_add',
  add_zero := λ x, by { change add' ⟨x, zero'⟩ = x, rw [add_comm', zero_add'], },
  add_left_neg := add_left_neg', }⟩

namespace category_theory

namespace concrete_category

namespace operations

def Ab_zero : operation₀ Ab :=
{ app := λ M, 0, }

def Ab_neg : operation₁ Ab :=
{ app := λ M x, -x, }

def Ab_add : operation₂ Ab :=
{ app := λ M x, x.1 + x.2, }

end operations

namespace internal

namespace Ab

open concrete_category.operations limits

variables {C : Type*} [category C] (M : internal Ab C)

def zero [has_terminal C] := Ab_zero.on_internal_obj M
def neg := Ab_neg.on_internal_obj M
def add [has_binary_products C] := Ab_add.on_internal_obj M
def yoneda_presheaf_zero := Ab_zero.on_internal_yoneda_presheaf M
def yoneda_presheaf_neg := Ab_neg.on_internal_yoneda_presheaf M
def yoneda_presheaf_add := Ab_add.on_internal_yoneda_presheaf M

def mk (X : C)
  (yoneda_zero : (functor.const Cᵒᵖ).obj punit ⟶ yoneda.obj X)
  (yoneda_neg : yoneda.obj X ⟶ yoneda.obj X)
  (yoneda_add : concat₂ (yoneda.obj X) (yoneda.obj X) ⟶ yoneda.obj X)
  (yoneda_add_comm : yoneda_add = lift₂ pr₂ pr₁ ≫ yoneda_add)
  (yoneda_add_assoc : lift₂ (pr₁₂_₃ ≫ yoneda_add) pr₃_₃ ≫ yoneda_add =
    lift₂ pr₁_₃ (pr₂₃_₃ ≫ yoneda_add) ≫ yoneda_add)
  (yoneda_zero_add : lift₂ (to_functor_const_punit ≫ yoneda_zero) (𝟙 _) ≫ yoneda_add = 𝟙 _ )
  (yoneda_add_left_neg : lift₂ yoneda_neg (𝟙 _) ≫ yoneda_add = to_functor_const_punit ≫ yoneda_zero) :
  internal Ab C :=
{ obj := X,
  presheaf :=
  { obj := λ Y, begin
      refine Ab.mk ((yoneda.obj X).obj Y) (yoneda_zero.app Y punit.star)
        (yoneda_neg.app Y) (yoneda_add.app Y) _ _ _ _,
      { intros x y z,
        exact congr_fun (congr_app yoneda_add_assoc Y) ⟨x, ⟨y, z⟩⟩, },
      { intros x y,
        exact congr_fun (congr_app yoneda_add_comm Y) ⟨x, y⟩, },
      { exact congr_fun (congr_app yoneda_zero_add Y), },
      { exact congr_fun (congr_app yoneda_add_left_neg Y), },
    end,
    map := λ Y Y' f, ⟨(yoneda.obj X).map f,
      congr_fun (yoneda_zero.naturality f).symm punit.star,
      λ x y, congr_fun (yoneda_add.naturality f).symm ⟨x, y⟩⟩, },
  iso := by refl, }

def mk' (X : C) [has_terminal C] [has_binary_product X X] [has_binary_product X (prod X X)]
  (zero : ⊤_ C ⟶ X) (neg : X ⟶ X) (add : prod X X ⟶ X) (add_comm : internal_operation₂.comm add)
  (add_assoc : internal_operation₂.assoc add) (add_zero : internal_operation₂.zero_add add zero)
  (add_left_neg : internal_operation₂.add_left_neg add zero neg) :
  internal Ab C :=
Ab.mk X (internal_operation₀.yoneda_equiv X zero)
  (internal_operation₁.yoneda_equiv X neg)
  (internal_operation₂.yoneda_equiv X add)
  (internal_operation₂.yoneda_equiv_comm X add add_comm)
  (internal_operation₂.yoneda_equiv_assoc X add add_assoc)
  (internal_operation₂.yoneda_equiv_zero_add X add zero add_zero)
  (internal_operation₂.yoneda_equiv_add_left_neg X add zero neg add_left_neg)

end Ab

end internal

end concrete_category

end category_theory
