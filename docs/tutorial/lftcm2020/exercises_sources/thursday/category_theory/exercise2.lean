import algebra.category.CommRing.basic
import data.polynomial

/-!
Let's show that taking polynomials over a ring is functor `Ring ⥤ Ring`.
-/

noncomputable theory -- the default implementation of polynomials is noncomputable

-- Just ignore this for now: it's a hack that prevents an annoying problem,
-- and a cleaner fix is on its way to mathlib.
local attribute [irreducible] polynomial.eval₂

/-!
mathlib is undergoing a transition at the moment from using "unbundled" homomorphisms
(e.g. we talk about a bare function `f : R → S`, along with a typeclass `[is_semiring_hom f]`)
to using "bundled" homomorphisms
(e.g. a structure `f : R →+* S`, which has a coercion to a bare function).

The category `Ring` uses bundled homomorphisms (and in future all of mathlib will).
However at present the polynomial library hasn't been updated.

You may find the `ring_hom.of` useful -- this upgrades an unbundled homomorphism
to a bundled homomorphism.
-/

/-!
Hints:
* use `polynomial.map`
-/

def Ring.polynomial : Ring ⥤ Ring :=
sorry

def CommRing.polynomial : CommRing ⥤ CommRing :=
sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
-- Hint: You can do this in two lines, ≤ 33 columns!
sorry


/-!
There are some further hints in
`hints/category_theory/exercise2/`
-/

/-!
Bonus problem:

Why did we set `local attribute [irreducible] polynomial.eval₂`?
What goes wrong without it? Why?
-/


