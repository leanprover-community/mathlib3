import category_theory.monoidal.functor
import category_theory.eq_to_hom
import category_theory.natural_isomorphism
import category_theory.monoidal.strictification

universes v₁ u₁

open category_theory
open category_theory.monoidal_category

lemma congr_heq {α α'} {β : α → Sort*} {β' : α' → Sort*}
  (f : Π a, β a) (f' : Π a, β' a) (a : α) (a' : α')
  (hf : f == f') (h : a == a') : f a == f' a' :=
begin
  cases h,
  cases h,
  sorry
end
lemma congr_arg_heq' {α} {β : α → Sort*} (f : ∀ a, β a) : ∀ {a₁ a₂ : α}, a₁ == a₂ → f a₁ == f a₂
| a _ h := begin cases h, exact heq.rfl end

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
  F.map (α.eval) = (map_eval_comparison F _).inv ≫ (α.map F.obj).eval ≫ (map_eval_comparison F _).hom :=
sorry

end reparenthesisation

open reparenthesisation monoidal_strictification

section
variables [𝒞 : strictly_monoidal.{v₁} C]
include 𝒞

theorem monoidal_coherence_aux : Π {P Q : parenthesised C} (α : reparenthesisation P Q), { h : P.eval = Q.eval // α.eval = eq_to_hom h }
| _ _ (left P)           := begin have := (strictly_monoidal.left_unitor_trivial (eval P)), fsplit, exact this.val, exact congr_arg iso.hom this.property end
| _ _ (left_inv P)       := sorry
| _ _ (right P)          := sorry
| _ _ (right_inv P)      := sorry
| _ _ (assoc P Q R)      := sorry
| _ _ (assoc_inv P Q R)  := sorry
| _ _ (tensor_left R α)  :=
  begin
    dsimp [reparenthesisation.eval],
    split,
    rw (monoidal_coherence_aux α).2,
    rw id_tensor_eq_to_hom,
  end
| _ _ (tensor_right R α) :=
  begin
    dsimp [reparenthesisation.eval],
    split,
    rw (monoidal_coherence_aux α).2,
    rw eq_to_hom_tensor_id,
  end
| _ _ (id P)             := ⟨rfl, rfl⟩
| _ _ (comp α β)         :=
  begin
    cases monoidal_coherence_aux α with vα pα,
    cases monoidal_coherence_aux β with vβ pβ,
    split,
    { dsimp [reparenthesisation.eval],
      rw [pα, pβ],
      simp },
    { exact vα.trans vβ }
  end

theorem monoidal_coherence_aux' {P Q : parenthesised C} (α β : reparenthesisation P Q) : α.eval = β.eval :=
by rw [(monoidal_coherence_aux α).2, (monoidal_coherence_aux β).2]

end

section
variables [𝒞 : monoidal_category.{v₁} C]
include 𝒞

theorem monoidal_coherence {P Q : parenthesised C} (α β : reparenthesisation P Q) : α.eval = β.eval :=
begin
  let F := monoidal_strictification C,
  apply F.to_functor.injectivity,
  rw map_eval,
  rw map_eval,
  rw monoidal_coherence_aux',
end
end

end category_theory
