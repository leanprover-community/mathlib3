import category_theory.monoidal.category
import algebra.category.CommRing.basic

/-!
Let's define the category of monoid objects in a monoidal category.
-/

open category_theory

variables (C : Type*) [category C] [monoidal_category C]

structure Mon_in :=
(X : C)
(ι : 𝟙_ C ⟶ X)
(μ : X ⊗ X ⟶ X)
-- There are three missing axioms here!
-- Use `λ_ X`, `ρ_ X` and `α_ X Y Z` for unitors and associators.
sorry

namespace Mon_in

variables {C}

@[ext]
structure hom (M N : Mon_in C) :=
sorry



instance : category (Mon_in C) :=
sorry

end Mon_in

/-!
Bonus projects (all but the first will be non-trivial with today's mathlib):
* Construct the category of module objects for a fixed monoid object.
* Check that `Mon_in Type ≌ Mon`.
* Check that `Mon_in Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first.)
* Check that `Mon_in AddCommGroup ≌ Ring`.
  (You'll have to hook up the monoidal structure on `AddCommGroup`.
  Currently we have the monoidal structure on `Module R`; perhaps one could specialize to `R = ℤ`
  and transport the monoidal structure across an equivalence? This sounds like some work!)
* Check that `Mon_in (Module R) ≌ Algebra R`.
* Show that if `C` is braided (you'll have to define that first!)
   then `Mon_in C` is naturally monoidal.
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
-/

