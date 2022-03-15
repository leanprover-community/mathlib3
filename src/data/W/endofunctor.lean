/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import data.W.basic
import category_theory.endofunctor.algebra
import category_theory.equivalence
import category_theory.functor.category

/-!
# Endofunctors associated to `W_type`s

Any `W_type` can be seen as initial algebras of their associated polynomial endofunctors.


## Main results
* `W_type.endofunctor`: makes the endofunctor associated to the `W_type`
* `W_type.data`: combines the data of `α : Type _` and `β : α → Type _` into a structure.
  This is given an instance of a category, which can be seen as a subcategory of `Type _ ⥤ Type _`
* `W_type.data.endofunctor`: packages `W_type.endofunctor` into a (fully faithful) functor from
  `W_type.data` to the endofunctor category `Type _ ⥤ Type _`
* `W_type.algebra` makes a `W_type` an algbera over its associated endofunctor
* `W_type.is_initial` shows that `W_type.algebra` is an initial algebra
-/

universes u₀ u₁

namespace W_type

open category_theory
open category_theory.endofunctor

/-- The polynomial endofunctor associated to a `W_type` -/
@[simps] def endofunctor {α : Type u₀} (β : α → Type u₁) : Type (max u₀ u₁) ⥤ Type (max u₀ u₁) :=
{ obj := λ X, Σ (a : α), β a → X,
  map := λ X Y f p, ⟨ p.1 , f ∘ p.2 ⟩ }

/--
The data of a `W_type` consists of an index `α` of constructors and
their dependently indexed arities `β`.
This will form a category.
-/
@[nolint check_univs]
structure data :=
{α : Type u₀}
(β : α → Type u₁)

/--
The category of `W_type`s with objects as a pair `(α,β)`
(viewed as the associated polynomial endofunctors)
and morphisms as natural transformations
this can be seen as a full subcategory of `C ⥤ C` -/
instance : category data :=
{ hom := λ W₀ W₁, nat_trans (endofunctor W₀.β) (endofunctor W₁.β),
  id := λ _, nat_trans.id _,
  comp := λ _ _ _, nat_trans.vcomp }

namespace data

/--
The trivial embedding into the endofunctor category
realizes `W_type.endofunctor` as a functor.
This is useful when reducing categorical statements about `W : W_type.data`
to facts about `W_type.endofunctor W.β`
-/
@[simps] def endofunctor : data.{u₀ u₁} ⥤ Type (max u₀ u₁) ⥤ Type (max u₀ u₁) :=
{ obj := λ W, endofunctor W.β,
  map := λ _ _ ν, ν }

instance : full endofunctor := { preimage := λ _ _ ν, ν }

instance : faithful endofunctor := {}

/-- Two `W_type`s are isomorphic if their defining types are equivalent -/
def iso_of_equiv {W₀ W₁ : data} (hα : W₀.α ≃ W₁.α) (hβ : ∀ a : W₀.α, W₀.β a ≃ W₁.β (hα.to_fun a)) :
  W₀ ≅ W₁ :=
preimage_iso (nat_iso.of_components
  (λ X, equiv.to_iso $ equiv.sigma_congr hα (λ a, equiv.Pi_congr' (hβ _) (by { intro, refl })))
  (by { intros, funext,
    simp only [types_comp_apply, equiv.to_iso, equiv.sigma_congr, equiv.to_fun_as_coe,
      equiv.coe_trans, function.comp_app, equiv.sigma_congr_right_apply, equiv.coe_Pi_congr',
      endofunctor_map_snd, equiv.coe_refl, id.def, equiv.sigma_congr_left_apply],
    dsimp only [data.endofunctor, W_type.endofunctor],
    simp [equiv.Pi_congr'_apply] }) : endofunctor.obj W₀ ≅ endofunctor.obj W₁)

open category_theory.endofunctor.algebra

/-- If the `W_type`s are isomorphic then their algebra categories are equivalent -/
def algebra_equiv_of_iso {W₀ W₁ : data} (hiso : W₀ ≅ W₁) :
algebra (endofunctor.obj W₀) ≌ algebra (endofunctor.obj W₁) :=
equiv_of_nat_iso $ functor.map_iso _ hiso

/--
The endofunctor `Σ (x : γ), X ^ (fin n) ≃ γ X ^ n `
-/
@[simp] def monomial (γ : Type u₀) (n : ℕ) : data := ⟨ λ x : γ, ulift (fin n) ⟩

/--
The identity endofunctor as a W_type,
`X ≃ punit X ^ 1`
-/
@[simp] def X : data := monomial punit 1

/--
The polynomial endofunctor taking anything to `⊥_ = pempty`,
since `pempty ≃ pempty X ^ 0` -/
@[simps] instance : has_zero data := { zero := monomial pempty 0 }

instance : inhabited data := ⟨ 0 ⟩

/--
The polynomial endofunctor taking anything to `⊤_ = punit`,
since `punit ≃ punit X ^ 0`
-/
@[simps] instance : has_one data := { one := monomial punit 0 }

/--
The constant functor going to a type `γ` is a polynomial
`γ = Σ (a : γ) 1 = Σ (a : γ) X ^ fin 0`
-/
instance : has_coe (Type u₀) data.{u₀ u₀} := { coe := λ γ, monomial γ 0 }

@[simp] lemma coe_β_eq (γ : Type u₀) :
  (γ : data.{u₀ u₀}).β = λ (_ : γ), ulift (fin 0) := rfl

/--
The sum of two polynomial endofunctors
`Σ (a : α₀) X^(β a) + Σ (a : α₁) X^(β₁ a) ≃ Σ (a : α₀ ⊕ α₁) X^((β₀ ⊕ β₁) a)`
-/
@[simps] def addition : data.{u₁ u₀} → data.{u₁ u₀} → data.{u₁ u₀} :=
λ W₀ W₁, ⟨ sum.elim W₀.β W₁.β ⟩

@[simps] instance : has_add data := { add := addition }

end data

variables {α : Type u₀} (β : α → Type u₁)

/-- `W_type` β as an algebra of its associated polynomial endofunctor -/
def algebra : algebra (endofunctor β) :=
{ A   := W_type β,
  str := W_type.of_sigma }

variables {β} (A : endofunctor.algebra (endofunctor β))

/-- The map in `Type` from the initial algebra `W_type` to any other algebra -/
def lift_f : W_type β → A.A
| (W_type.mk a b) := A.str ⟨ a , λ x, lift_f (b x) ⟩

/-- The map in `endofunctor.algebra` from the initial algebra `W_type` to any other algebra -/
def lift : algebra β ⟶ A := { f := lift_f A }

lemma lift_uniq (f : algebra β ⟶ A) : f = lift A :=
begin
  ext w,
  induction w with a b hw,
  simp only [lift, lift_f],
  convert (congr_fun f.2 ⟨ a , b ⟩).symm,
  funext x,
  exact (hw x).symm,
end

instance (A : endofunctor.algebra (endofunctor β)) : unique (algebra β ⟶ A) :=
{ default := lift A,
  uniq := lift_uniq A }.

/-- A `W_Type` is the initial algebra of its associated polynomial endofunctor -/
def is_initial : limits.is_initial (algebra β) :=
limits.is_initial.of_unique _

end W_type
