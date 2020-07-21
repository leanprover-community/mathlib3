import algebra.category.CommRing.basic
import data.polynomial

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, ring_hom.of (polynomial.map f), }

def CommRing.polynomial : CommRing ⥤ CommRing :=
{ obj := λ R, CommRing.of (polynomial R),
  map := λ R S f, ring_hom.of (polynomial.map f), }

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
{ hom :=
  { app :=
    begin
      -- Let's think about the maths for a bit...
      -- Given a commutative ring, we can either forget that it is commutative and then take polynomials,
      -- or take polynomials and then forget that those are commutative.
      -- The result is exactly the same either way, so let's try:
      intro R,
      exact 𝟙 _, -- this says "use the identity on whatever makes this typecheck!"
      -- 🎉
    end,
    naturality' := sorry, },
  inv :=
  { app := sorry,
    naturality' := sorry },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }.

-- At this point the way forward is clear:
-- * golf that construction to term mode
-- * do the same thing for `inv`!
-- * fill in the proof terms: `by tidy` is quite useful.
-- * check the solutions to see if you managed to golf completely!
