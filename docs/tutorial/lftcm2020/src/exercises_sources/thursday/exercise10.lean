import category_theory.limits.shapes.zero
import category_theory.full_subcategory
import algebra.homology.chain_complex
import data.int.basic

/-!
(WARNING: this is an incomplete exercise. It's probably doable from this point,
but it's more of a lesson/warning about dependent type theory hell than an enjoyable activity.)

Let's give a quirky definition of a cochain complex in a category `C` with zero morphisms,
as a functor `F` from `(ℤ, ≤)` to `C`, so that `∀ i, F.map (by tidy : i ≤ i+2) = 0`.

Let's think of this as a full subcategory of all functors `(ℤ, ≤) ⥤ C`,
and realise that natural transformations are exactly chain maps.

Finally let's construct an equivalence of categories with the usual definition of chain cocomplex!
-/

open category_theory
open category_theory.limits

-- Anytime we have a `[preorder α]`, we automatically get a `[category.{v} α]` instance,
-- in which the morphisms `X ⟶ Y` are defined to be `ulift (plift X ≤ Y)`.
-- (We need those annoying `ulift` and `plift` because `X ≤ Y` is a `Prop`,
-- and the morphisms spaces of a category need to be in `Type v` for some `v`.)

namespace exercise

-- We work in the lowest universe, where `ℤ` lives, for convenience.
-- If we wanted to work in higher universes we would need to use `ulift ℤ`.
variables (C : Type) [category.{0} C] [has_zero_morphisms C]

@[derive category]
def complex : Type :=
{ F : ℤ ⥤ C // ∀ i : ℤ, F.map (by tidy : i ⟶ i+2) = 0 }

def exercise : complex C ≌ cochain_complex C :=
sorry



end exercise

