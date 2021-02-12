import category_theory.abelian.basic
import category_theory.simplicial_object
import algebra.homology.chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits


variables (C : Type u) [category.{v} C] [abelian C]

local attribute [instance] has_zero_object.has_zero

@[derive category]
def connective_chain_complex := { X : chain_complex C // ∀ i : ℤ, i < 0 → X.X i = 0 }

variables {C}

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex

def obj_X_apply (X : simplicial_object C) (i : ℕ) : C := sorry

def obj (X : simplicial_object C) : connective_chain_complex C :=
{ val :=
  { X := λ i, if 0 ≤ i then obj_X_apply X i.to_nat else 0,
    d := sorry, },
  property := sorry, }

end normalized_Moore_complex

def normalized_Moore_complex : simplicial_object C ⥤ connective_chain_complex C :=
{ obj := λ X, sorry,
  map := sorry, }
