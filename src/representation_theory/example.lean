/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.basic
import representation_theory.Rep
import algebra.category.Module.adjunctions

universes u

noncomputable theory

variables (k : Type u) [field k] (G : Type u) [group G]

open category_theory

/-- Turning a `G` action on a type into a representation by linearisation, as a monoidal functor. -/
def Rep.linearisation : monoidal_functor (Action (Type u) (Mon.of G)) (Rep k G) :=
(Module.monoidal_free k).map_Action (Mon.of G)

def Action.of_mul_action (H : Type u) [mul_action G H] : Action (Type u) (Mon.of G) :=
{ V := H,
  ρ :=
  { to_fun := λ (g : G) h, g • h,
    map_one' := by { ext, simp, },
    map_mul' := by { intros, ext, dsimp, simp [mul_smul], refl, }}, }

def Action.left_regular : Action (Type u) (Mon.of G) :=
Action.of_mul_action G G

def Action.diagonal (n : ℕ) := Action.of_mul_action G (fin n → G)

def Action.diagonal_succ (n : ℕ) :
  Action.diagonal G (n+1) ≅ Action.left_regular G ⊗ Action.diagonal G n :=
Action.mk_iso (equiv.pi_fin_succ_above_equiv _ 0).to_iso (λ g, by tidy)

example (n : ℕ) :
  (((Rep.linearisation k G).obj (Action.diagonal G n) : Rep k G) : Type*) = ((fin n → G) →₀ k) :=
rfl

def Rep.left_regular : Rep k G :=
Rep.of ((monoid_algebra.lift k G _).symm (algebra.lmul k (monoid_algebra k G)))

example : (Rep.left_regular k G : Type*) = monoid_algebra k G := rfl

def Rep.linearisation_left_regular :
  (Rep.linearisation k G).obj (Action.left_regular G) ≅ Rep.left_regular k G :=
Action.mk_iso (by refl) (λ g, by { ext v h, dsimp, sorry, })
-- Many simp lemmas are missing, but this sorry shouldn't be hard.

def Rep.linearisation_diagonal_succ (n : ℕ) :
  (Rep.linearisation k G).obj (Action.diagonal G (n+1)) ≅
    Rep.left_regular k G ⊗ (Rep.linearisation k G).obj (Action.diagonal G n) :=
functor.map_iso _ (Action.diagonal_succ G n) ≪≫
  (as_iso ((Rep.linearisation k G).μ _ _)).symm ≪≫ -- The tensorator of `Rep.linearisation`.
  tensor_iso (Rep.linearisation_left_regular k G) (iso.refl _)

instance blah (n : ℕ) : module (monoid_algebra k G) ((fin n → G) →₀ k) :=
representation.as_module_module ((Rep.linearisation k G).obj (Action.diagonal G n)).ρ

example (n : ℕ) :
  ((fin (n+1) → G) →₀ k) ≃ₗ[monoid_algebra k G]
    (tensor_product k (monoid_algebra k G) ((fin n → G) →₀ k)) :=
-- This doesn't quite do it:
/-
```
(Rep.equivalence_Module_monoid_algebra.functor.map_iso
  (Rep.linearisation_diagonal_succ k G n)).to_linear_equiv
```
-/
-- We still need to know what `Rep.equivalence_Module_monoid_algebra.functor`
-- does to tensor products. We would want to use the fact that
-- `Module (monoid_algebra k G)` is monoidal since `monoid_algebra k G` is a hopf algebra.
sorry
