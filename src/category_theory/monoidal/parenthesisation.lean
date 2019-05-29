import category_theory.monoidal.functor
import category_theory.eq_to_hom

universes v₁ u₁

open category_theory
open category_theory.monoidal_category

namespace category_theory

inductive parenthesised (C : Type u₁) : Type u₁
| unit {} : parenthesised
| of : C → parenthesised
| tensor : parenthesised → parenthesised → parenthesised

variables {C : Type u₁}

namespace parenthesised

@[simp] def to_list : parenthesised C → list C
| unit         := []
| (of X)       := [X]
| (tensor P Q) := to_list P ++ to_list Q

end parenthesised

open parenthesised

-- inductive reparenthesisation : parenthesised C → parenthesised C → Type u₁
-- | left : Π (P), reparenthesisation (tensor unit P) P
-- | left_inv : Π (P), reparenthesisation P (tensor unit P)
-- | right : Π (P), reparenthesisation (tensor P unit) P
-- | right_inv : Π (P), reparenthesisation P (tensor P unit)
-- | assoc : Π (P Q R), reparenthesisation (tensor (tensor P Q) R) (tensor P (tensor Q R))
-- | assoc_inv : Π (P Q R), reparenthesisation (tensor P (tensor Q R)) (tensor (tensor P Q) R)
-- | tensor_left : Π (P) {Q R}, reparenthesisation Q R → reparenthesisation (tensor P Q) (tensor P R)
-- | tensor_right : Π {P Q} (R), reparenthesisation P Q → reparenthesisation (tensor P R) (tensor Q R)
-- | id : Π (P), reparenthesisation P P
-- | comp : Π {P Q R}, reparenthesisation P Q → reparenthesisation Q R → reparenthesisation P R
-- .

instance : monoidal_category (parenthesised C) :=
{ hom          := λ P Q, P.to_list = Q.to_list,
  id           := λ P, rfl,
  comp         := λ _ _ _ f g, eq.trans f g,
  tensor_unit  := unit,
  tensor_obj   := tensor,
  tensor_hom   := λ _ _ _ _ f g, begin dsimp at *, rw [f, g] end,
  left_unitor  := by tidy,
  right_unitor := by tidy,
  associator   := by tidy }.

@[simp] lemma to_list_tensor (X Y : parenthesised C) : to_list (X ⊗ Y) = to_list X ++ to_list Y := rfl

variables [𝒞 : monoidal_category.{v₁} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

def tensor_list (X : list C) : C := X.foldl (⊗) (𝟙_ C)
@[simp] lemma tensor_list_nil : tensor_list list.nil = 𝟙_ C := rfl

def tensorator : Π (X Y : parenthesised C),
    tensor_list (to_list X) ⊗ tensor_list (to_list Y) ⟶ tensor_list (to_list (X ⊗ Y))
| unit _ := (λ_ _).hom
| _ unit := begin dsimp, simp only [to_list, list.append_nil], exact (ρ_ _).hom end
| (tensor P Q) R := begin tidy?, end
.

def foo : monoidal_functor.{0 v₁} (parenthesised C) C :=
{ obj := λ P, tensor_list P.to_list,
  map := λ P Q f, eq_to_hom begin congr, exact f end,
  ε := 𝟙 _,
  μ := tensorator }

end category_theory
