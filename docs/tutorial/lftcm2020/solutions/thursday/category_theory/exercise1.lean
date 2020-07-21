import category_theory.isomorphism
import category_theory.yoneda

open category_theory
open opposite

variables {C : Type*} [category C]

/-! Hint 1:
`yoneda` is set up so that `(yoneda.obj X).obj (op Y) = (Y ⟶ X)`
(we need to write `op Y` to explicitly move `Y` to the opposite category).
-/

/-! Hint 2:
If you have a natural isomorphism `α : F ≅ G`, you can access
* the forward natural transformation as `α.hom`
* the backwards natural transformation as `α.inv`
* the component at `X`, as an isomorphism `F.obj X ≅ G.obj X` as `α.app X`.
-/

def iso_of_hom_iso (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
-- sorry
{ hom := (h.app (op X)).hom (𝟙 X),
  inv := (h.symm.app (op Y)).hom (𝟙 Y), }
-- sorry

/-!
There are some further hints in
`hints/category_theory/exercise1/`
-/

-- omit
/-!
Notice that we didn't need to provide proofs for the fields `hom_inv_id'` and `inv_hom_id'`.
These were filled in by automation.
-/
-- omit
