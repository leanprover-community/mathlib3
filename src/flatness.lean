import category_theory.abelian.generator
import algebra.module.injective
import adjunction_Ab

universes v

variables (R : Ring.{v})


/-
In this file we prove that `M` has enough injectives.

* `M ⊗ _` preserves injectives of the form `I -> R` where `I` is a f.g. ideal of `R`.

iff

* `M ⊗ _` preserves all injectives `N -> M` for `N`, `M` `R`-modules.
-/

-- There is a cute argument for this provided on Zulip:

/-
By the dependencies included, we can conclude that:

* `M ⊗ _` preserves `I -> R` injectives for all ideals iff it does so for f.g. ones.
  This follows by my work in the original flat_modules repo + a little bit more work
-/

-- TODO: Add the dependencies in here (maybe my next incoming PR)

/-
* We know `R-Mod` has an enough injectives, and hence has an injective coseparator (injective generator?) X
-/

example : category_theory.enough_injectives (Module.{v} R) := infer_instance

#check @category_theory.abelian.has_injective_coseparator (Module.{v} R) _ _ _ _

/-
* Hom( _ , Hom( M , X ) ) < - > Hom ( _ ⊗ M , X ).
* Hom( _ , X ) preserves monos, and reflects monos (because X is an injective cogenerator)
* Hom( M , X ) is injective iff Hom( _ , Hom( M , X ) ) preserves monos
* Hom( _ , Hom( M , X ) ) preserves monos iff Hom ( _ ⊗ M , X ) preserves monos
* Hom ( _ ⊗ M , X ) preserves monos iff _ ⊗ M preserves monos
-/

/-
* We also know that Hom( _ , Hom( M , X ) ) preserves monos of the form `I -> R` by Baer's criterion
-/

#check module.Baer.injective

/-
* So it suffices to check `_ ⊗ M` only on these morphisms to check, and this is was the desired fact.
-/
