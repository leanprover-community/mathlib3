import category_theory.limits.shapes.zero
import category_theory.full_subcategory
import algebra.homology.chain_complex
import data.int.basic

/-!
Here's a partial solution.
It provides most of the data, but doesn't check required properties.

It starts becoming rough going at about this point,
when you start proving properties of `long_map`.
-/

open category_theory
open category_theory.limits

namespace exercise

variables (C : Type) [category.{0} C] [has_zero_morphisms C]

@[derive category]
def complex : Type :=
{ F : ℤ ⥤ C // ∀ i : ℤ, F.map (by tidy : i ⟶ i+2) = 0 }

def functor : complex C ⥤ cochain_complex C :=
{ obj := λ P,
  { X := P.1.obj,
    d := λ i, P.1.map (by tidy : i ⟶ i+1),
    d_squared' := sorry, },
  map := λ P Q α,
  { f := λ i, α.app i,
    comm' := sorry, } }

def long_map (P : cochain_complex C) (i j : ℤ) : P.X i ⟶ P.X j :=
if h₀ : j = i then
  eq_to_hom (by rw h₀)
else if h₁ : j = i+1 then
  P.d i ≫ eq_to_hom (by {simp [h₁]})
else 0

def inverse : cochain_complex C ⥤ complex C :=
{ obj := λ P,
  { val :=
    { obj := λ i, P.X i,
      map := λ i j p, long_map C P i j,
      map_id' := sorry,
      map_comp' := sorry },
    property := sorry, },
  map := λ P Q f,
  { app := λ i, f.f i,
    naturality' := sorry, },
  map_id' := sorry,
  map_comp' := sorry, }

def exercise : complex C ≌ cochain_complex C :=
{ functor := functor C,
  inverse := inverse C,
  unit_iso := sorry, -- There's still more data to provide here.
  counit_iso := sorry, -- and here.
  functor_unit_iso_comp' := sorry, }

end exercise
