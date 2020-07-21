import category_theory.isomorphism
import category_theory.yoneda

open category_theory
open opposite

variables {C : Type*} [category C]

def iso_of_hom_iso_attempt (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
{ hom :=
  begin
    -- We need to construct a morphism `X ⟶ Y`.
    -- Recall that the components `h.app Z` of our hypothesis are isomorphisms.
    -- We can check exactly what they are (if we've forgotten how `yoneda` works), like this:
    have := h.app,
    dsimp at this,
    -- This says that for any `Z : Cᵒᵖ`, we get an isomorphism from
    -- the morphism space `unop Z ⟶ Z` to the morphism space `unop Z ⟶ Y`.
    -- This suggests we want to use `h.app (op X)`, and apply the forward direction of that
    -- to some element of `unop (op X) ⟶ X` that we have available.
    sorry
  end,
  inv := sorry, }
