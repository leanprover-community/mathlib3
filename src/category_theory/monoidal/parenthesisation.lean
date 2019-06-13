import category_theory.monoidal.functor
import category_theory.eq_to_hom
import category_theory.natural_isomorphism
import category_theory.monoidal.strictification

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

def map {D : Type u₁} (f : C → D) : parenthesised C → parenthesised D
| unit := unit
| (of X) := of (f X)
| (tensor P Q) := tensor (map P) (map Q)

variables [𝒞 : monoidal_category.{v₁} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

def eval : parenthesised C → C
| unit         := 𝟙_ C
| (of X)       := X
| (tensor P Q) := eval P ⊗ eval Q

variables {D : Type u₁} [𝒟 : monoidal_category.{v₁} D]
include 𝒟
variables (F : monoidal_functor.{v₁ v₁} C D)

def map_eval_comparison : Π (X : parenthesised C), (X.map F.obj).eval ≅ F.obj X.eval
| unit         := as_iso (F.ε)
| (of X)       := iso.refl _
| (tensor P Q) := (tensor_iso (map_eval_comparison P) (map_eval_comparison Q)) ≪≫ as_iso (F.μ _ _)

end parenthesised

open parenthesised

inductive reparenthesisation : parenthesised C → parenthesised C → Type u₁
| left         : Π (P), reparenthesisation (tensor unit P) P
| left_inv     : Π (P), reparenthesisation P (tensor unit P)
| right        : Π (P), reparenthesisation (tensor P unit) P
| right_inv    : Π (P), reparenthesisation P (tensor P unit)
| assoc        : Π (P Q R), reparenthesisation (tensor (tensor P Q) R) (tensor P (tensor Q R))
| assoc_inv    : Π (P Q R), reparenthesisation (tensor P (tensor Q R)) (tensor (tensor P Q) R)
| tensor_left  : Π (P) {Q R}, reparenthesisation Q R → reparenthesisation (tensor P Q) (tensor P R)
| tensor_right : Π {P Q} (R), reparenthesisation P Q → reparenthesisation (tensor P R) (tensor Q R)
| id           : Π (P), reparenthesisation P P
| comp         : Π {P Q R}, reparenthesisation P Q → reparenthesisation Q R → reparenthesisation P R
.

namespace reparenthesisation

def map {D : Type u₁} (f : C → D) : Π {P Q : parenthesised C}, reparenthesisation P Q → reparenthesisation (P.map f) (Q.map f)
| _ _ (left P)           := left (P.map f)
| _ _ (left_inv P)       := left_inv (P.map f)
| _ _ (right P)          := right (P.map f)
| _ _ (right_inv P)      := right_inv (P.map f)
| _ _ (assoc P Q R)      := assoc (P.map f) (Q.map f) (R.map f)
| _ _ (assoc_inv P Q R)  := assoc_inv (P.map f) (Q.map f) (R.map f)
| _ _ (tensor_left P α)  := tensor_left (P.map f) (map α)
| _ _ (tensor_right R α) := tensor_right (R.map f) (map α)
| _ _ (id P)             := id (P.map f)
| _ _ (comp α β)         := comp (map α) (map β)


variables [𝒞 : monoidal_category.{v₁} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

def eval : Π {P Q : parenthesised C} (α : reparenthesisation P Q), P.eval ⟶ Q.eval
| _ _ (left P)           := (λ_ P.eval).hom
| _ _ (left_inv P)       := (λ_ P.eval).inv
| _ _ (right P)          := (ρ_ P.eval).hom
| _ _ (right_inv P)      := (ρ_ P.eval).inv
| _ _ (assoc P Q R)      := (α_ P.eval Q.eval R.eval).hom
| _ _ (assoc_inv P Q R)  := (α_ P.eval Q.eval R.eval).inv
| _ _ (tensor_left P α)  := 𝟙 (P.eval) ⊗ (eval α)
| _ _ (tensor_right R α) := (eval α) ⊗ 𝟙 (R.eval)
| _ _ (id P)             := 𝟙 P.eval
| _ _ (comp α β)         := (eval α) ≫ (eval β)

variables {D : Type u₁} [𝒟 : monoidal_category.{v₁} D]
include 𝒟
variables (F : monoidal_functor.{v₁ v₁} C D)

lemma map_eval {P Q : parenthesised C} (α : reparenthesisation P Q) :
  (map_eval_comparison F _).hom ≫ F.map (α.eval) ≫ (map_eval_comparison F _).inv = (α.map F.obj).eval :=
sorry

end reparenthesisation

section
variables [𝒞 : monoidal_strictification.strictly_monoidal.{v₁} C]
include 𝒞

theorem monoidal_coherence_aux {P Q : parenthesised C} (α β : reparenthesisation P Q) : α.eval = β.eval :=
sorry
end

section
variables [𝒞 : monoidal_category.{v₁} C]
include 𝒞

theorem monoidal_coherence {P Q : parenthesised C} (α β : reparenthesisation P Q) : α.eval = β.eval :=
sorry
end


-- instance : monoidal_category (parenthesised C) :=
-- { hom          := λ P Q, P.to_list = Q.to_list,
--   id           := λ P, rfl,
--   comp         := λ _ _ _ f g, eq.trans f g,
--   tensor_unit  := unit,
--   tensor_obj   := tensor,
--   tensor_hom   := λ _ _ _ _ f g, begin dsimp at *, rw [f, g] end,
--   left_unitor  := by tidy,
--   right_unitor := by tidy,
--   associator   := by tidy }.

-- @[simp] lemma to_list_tensor (X Y : parenthesised C) : to_list (X ⊗ Y) = to_list X ++ to_list Y := rfl

-- variables [𝒞 : monoidal_category.{v₁} C]
-- include 𝒞

-- local notation `𝟙_` := tensor_unit
-- local notation `α_` := associator
-- local notation `λ_` := left_unitor
-- local notation `ρ_` := right_unitor

-- def tensor_list (X : list C) : C := X.foldl (⊗) (𝟙_ C)
-- @[simp] lemma tensor_list_nil : tensor_list list.nil = 𝟙_ C := rfl

-- def tensorator : Π (X Y : parenthesised C),
--     tensor_list (to_list X) ⊗ tensor_list (to_list Y) ⟶ tensor_list (to_list (X ⊗ Y))
-- | unit _ := (λ_ _).hom
-- | _ unit := begin dsimp, simp only [to_list, list.append_nil], exact (ρ_ _).hom end
-- | (tensor P Q) R := begin tidy?, end
-- .

-- def foo : monoidal_functor.{0 v₁} (parenthesised C) C :=
-- { obj := λ P, tensor_list P.to_list,
--   map := λ P Q f, eq_to_hom begin congr, exact f end,
--   ε := 𝟙 _,
--   μ := tensorator }

end category_theory
