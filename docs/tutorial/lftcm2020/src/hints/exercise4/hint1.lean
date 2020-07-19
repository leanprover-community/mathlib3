import algebra.category.CommRing
import category_theory.yoneda

noncomputable theory

open category_theory
open opposite

/-!
We need to provide a commutative ring, and then an isomorphism between two functors.
-/

def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
⟨CommRing.of (polynomial ℤ),
 { hom := sorry,
   inv := sorry,
   hom_inv_id' := sorry,
   inv_hom_id' := sorry, }⟩
