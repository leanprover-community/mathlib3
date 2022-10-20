import category_theory.concrete_category.basic
import category_theory.limits.shapes.terminal
import category_theory.limits.functor_category
import category_theory.limits.types

universes v₁ v₂ u₂

namespace category_theory

open limits

namespace concrete_category

variables (A : Type u₂) [category.{v₂} A] [concrete_category.{v₁} A]
  {D : Type*} [category D]

namespace operations

@[simps]
def concat₂ (F₁ F₂ : D ⥤ Type v₁) : D ⥤ Type v₁ :=
{ obj := λ X, F₁.obj X × F₂.obj X,
  map := λ X Y f a, ⟨F₁.map f a.1, F₂.map f a.2⟩, }

@[simps]
def concat₃ (F₁ F₂ F₃ : D ⥤ Type v₁) : D ⥤ Type v₁ :=
{ obj := λ X, F₁.obj X × (F₂.obj X × F₃.obj X),
  map := λ X Y f a, ⟨F₁.map f a.1, ⟨F₂.map f a.2.1, F₃.map f a.2.2⟩⟩, }

@[simps]
def pr₁ {F₁ F₂ : D ⥤ Type v₁} : concat₂ F₁ F₂ ⟶ F₁ :=
{ app := λ X x, x.1, }

@[simps]
def pr₂ {F₁ F₂ : D ⥤ Type v₁} : concat₂ F₁ F₂ ⟶ F₂ :=
{ app := λ X x, x.2, }

@[simps]
def pr₁_₃ {F₁ F₂ F₃ : D ⥤ Type v₁} : concat₃ F₁ F₂ F₃ ⟶ F₁ :=
{ app := λ X x, x.1, }

@[simps]
def pr₂_₃ {F₁ F₂ F₃ : D ⥤ Type v₁} : concat₃ F₁ F₂ F₃ ⟶ F₂ :=
{ app := λ X x, x.2.1, }

@[simps]
def pr₃_₃ {F₁ F₂ F₃ : D ⥤ Type v₁} : concat₃ F₁ F₂ F₃ ⟶ F₃ :=
{ app := λ X x, x.2.2, }

@[simps]
def lift₂ {F F₁ F₂ : D ⥤ Type v₁} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) : F ⟶ concat₂ F₁ F₂ :=
{ app := λ X x, ⟨τ₁.app X x, τ₂.app X x⟩,
  naturality' := λ X Y f, begin
    ext,
    { apply congr_fun (τ₁.naturality f), },
    { apply congr_fun (τ₂.naturality f), },
  end, }

def lift₃ {F F₁ F₂ F₃ : D ⥤ Type v₁} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) (τ₃ : F ⟶ F₃) :
  F ⟶ concat₃ F₁ F₂ F₃ :=
{ app := λ X x, ⟨τ₁.app X x, ⟨τ₂.app X x, τ₃.app X x⟩⟩,
  naturality' := λ X Y f, begin
    ext,
    { apply congr_fun (τ₁.naturality f), },
    { apply congr_fun (τ₂.naturality f), },
    { apply congr_fun (τ₃.naturality f), },
  end, }

@[simps]
def pr₁₂_₃ {F₁ F₂ F₃ : D ⥤ Type v₁} : concat₃ F₁ F₂ F₃ ⟶ concat₂ F₁ F₂ :=
lift₂ pr₁_₃ pr₂_₃

@[simps]
def pr₁₃_₃ {F₁ F₂ F₃ : D ⥤ Type v₁} : concat₃ F₁ F₂ F₃ ⟶ concat₂ F₁ F₃ :=
lift₂ pr₁_₃ pr₃_₃

@[simps]
def pr₂₃_₃ {F₁ F₂ F₃ : D ⥤ Type v₁} : concat₃ F₁ F₂ F₃ ⟶ concat₂ F₂ F₃ :=
lift₂ pr₂_₃ pr₃_₃

end operations

open operations

def to_functor_const_punit {F : D ⥤ Type v₁} :
  F ⟶ (functor.const D).obj punit :=
{ app := λ X x, punit.star, }

def operation₀ := ((functor.const A).obj punit ⟶ forget A)
def operation₁ := forget A ⟶ forget A
def operation₂ := concat₂ (forget A) (forget A) ⟶ forget A
def operation₃ := concat₃ (forget A) (forget A) (forget A)
  ⟶ forget A

namespace operation₂

variables {A} (oper : operation₂ A)

@[simp]
def assoc : Prop :=
lift₂ (pr₁₂_₃ ≫ oper) pr₃_₃ ≫ oper = lift₂ pr₁_₃ (pr₂₃_₃ ≫ oper) ≫ oper

@[simp]
def comm : Prop :=
oper = lift₂ pr₂ pr₁ ≫ oper

end operation₂

end concrete_category

end category_theory
