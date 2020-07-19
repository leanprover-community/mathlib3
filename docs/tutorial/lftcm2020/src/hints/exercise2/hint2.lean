import algebra.category.CommRing.basic
import data.polynomial

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
{ obj :=
  begin
    -- The goal is just `Ring ⟶ Ring`, so lets:
    intro R,
    -- To build a bundled `Ring` object, we use `Ring.of X`,
    -- where `X` is some `Type` equipped with a `[ring X]` instance.
    exact Ring.of (polynomial R),
    -- Notice here that we can use `R : Ring` exactly as if it were a `Type`
    -- (there's an automatic coercion), and this type automatically receives a `[ring R]` instance.
  end,
  map := sorry, }

def CommRing.polynomial : CommRing ⥤ CommRing :=
sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
sorry
