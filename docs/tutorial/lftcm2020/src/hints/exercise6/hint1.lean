import category_theory.limits.shapes.pullbacks

/-!
Thanks to Markus Himmel for suggesting this question.
-/

open category_theory
open category_theory.limits

/-!
Let C be a category, X and Y be objects and f : X ⟶ Y be a morphism. Show that f is an epimorphism
if and only if the diagram

X --f--→ Y
|        |
f        𝟙
|        |
↓        ↓
Y --𝟙--→ Y

is a pushout.
-/

universes v u

variables {C : Type u} [category.{v} C]

def pushout_of_epi {X Y : C} (f : X ⟶ Y) [epi f] :
  is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
begin
  fapply pushout_cocone.is_colimit.mk,
  all_goals { sorry, },
end

theorem epi_of_pushout {X Y : C} (f : X ⟶ Y)
  (is_colim : is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) : epi f :=
{ left_cancellation := λ Z g h hf,
  begin
    let a := pushout_cocone.mk _ _ hf,
    sorry,
  end }
