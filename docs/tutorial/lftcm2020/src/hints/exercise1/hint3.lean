import category_theory.isomorphism
import category_theory.yoneda

open category_theory
open opposite

variables {C : Type*} [category C]

def iso_of_hom_iso_attempt (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom :=
  begin
    apply (h.app (op X)).hom,
    exact 𝟙 X,
    -- If you've haven't done this, you should now learn how to "golf" this proof
    -- into a single line "term mode" proof.
  end,
  inv :=
  begin
    -- It's pretty similar the other way.
    apply (h.app (op Y)).inv,
    sorry
  end, }
