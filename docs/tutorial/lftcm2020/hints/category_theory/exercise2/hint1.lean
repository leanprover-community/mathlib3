import algebra.category.CommRing.basic
import data.polynomial

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
-- We need to build a functor, so let's fill in the data fields with `sorry`
{ obj := sorry,
  map := sorry, }

def CommRing.polynomial : CommRing ⥤ CommRing :=
sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
sorry
