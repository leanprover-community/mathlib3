/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_topology.simplicial_object
import category_theory.abelian.basic
import category_theory.subobject
import algebra.homology.connective_chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits
open opposite

namespace algebraic_topology

variables {C : Type*} [category C] [abelian C]
local attribute [instance] abelian.has_pullbacks

instance : has_images C := by apply_instance

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex
variables (X : simplicial_object C)

/--
The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
def obj_X : Π n : ℕ, subobject (X.obj (op n))
| 0 := ⊤
| (n+1) := finset.univ.inf (λ k : fin (n+1), kernel_subobject (X.δ k.succ))

def obj_d : Π n : ℕ, (obj_X X (n+1) : C) ⟶ (obj_X X n : C)
| 0 := subobject.arrow _ ≫ X.δ (0 : fin 2) ≫ subobject.top_coe_iso_self.inv
| (n+1) :=
begin
  refine subobject.factor_thru _ (subobject.arrow _ ≫ X.δ (0 : fin (n+3))) _,
  refine (subobject.finset_inf_factors _).mpr _,
  rintro i _,
  apply kernel_subobject_factors,
  dsimp [obj_X],
end

def obj : connective_chain_complex C :=
{ X := λ n, (obj_X X n : C), -- the coercion here picks a representative of the subobject
  d := obj_d X,
  d_squared' := sorry, }

end normalized_Moore_complex

variables (C)

def normalized_Moore_complex : (simplicial_object C) ⥤ connective_chain_complex C :=
{ obj := λ X, sorry,
  map := sorry, }

end algebraic_topology
