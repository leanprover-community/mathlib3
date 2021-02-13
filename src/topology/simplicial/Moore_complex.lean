import category_theory.abelian.basic
import category_theory.simplicial_object
import algebra.category.Module.basic
import algebra.homology.chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits

section
variables (C : Type*) [category C] [has_zero_object C] [has_zero_morphisms C]
local attribute [instance] has_zero_object.has_zero

@[derive category]
def connective_chain_complex := { X : chain_complex C // ∀ i : ℤ, i < 0 → X.X i = 0 }
end

variables {R : Type*} [ring R] -- We could probably do this for an arbitrary abelian category?

local notation `sModule `R := simplicial_object (Module R)

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex

def obj_X_apply (X : sModule R) (i : ℕ) : Module R := sorry

def obj (X : sModule R) : connective_chain_complex (Module R) :=
{ val :=
  { X := λ i, if 0 ≤ i then obj_X_apply X i.to_nat else 0,
    d := sorry, },
  property := sorry, }

end normalized_Moore_complex

variables (R)

def normalized_Moore_complex : sModule R ⥤ connective_chain_complex (Module R) :=
{ obj := λ X, sorry,
  map := sorry, }
