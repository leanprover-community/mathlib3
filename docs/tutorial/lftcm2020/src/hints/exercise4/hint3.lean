import algebra.category.CommRing
import category_theory.yoneda

noncomputable theory

open category_theory
open opposite
open polynomial

/-!
Now let's give the backwards map.
-/
def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
⟨CommRing.of (polynomial ℤ),
 { hom :=
   { app := λ R r, polynomial.eval₂_ring_hom (algebra_map ℤ R) r,
     naturality' := sorry, },
   inv :=
   { app := λ R f,
     begin
       dsimp at f,
       -- The only possible thing to do is evaluate the ring homomorphism `f` at `X`.
       exact f X,
     end, },
   hom_inv_id' := sorry,
   inv_hom_id' := sorry, }⟩

-- In fact, notice we didn't write a `sorry` for `naturality'` here:
-- automation could do it automatically.

-- What about the remaining `sorry`s?
