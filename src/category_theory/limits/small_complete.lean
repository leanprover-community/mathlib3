/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.products
import set_theory.cardinal

/-!
# Any small complete category is a preorder

We show that any small category which has all (small) limits is a preorder: In particular, we show
that if a small category `C` in universe `u` has products of size `u`, then for any `X Y : C`
there is at most one morphism `X ⟶ Y`.
Note that in Lean, a preorder category is strictly one where the morphisms are in `Prop`, so
we instead show that the homsets are subsingleton.

## References

* https://ncatlab.org/nlab/show/complete+small+category#in_classical_logic

## Tags

small complete, preorder, Freyd
-/

namespace category_theory

open category limits
open_locale cardinal

universe u

variables {C : Type u} [small_category C] [has_products C]

/--
A small category with products is a thin category.

in Lean, a preorder category is one where the morphisms are in Prop, which is weaker than the usual
notion of a preorder/thin category which says that each homset is subsingleton; we show the latter
rather than providing a `preorder C` instance.
-/
instance {X Y : C} : subsingleton (X ⟶ Y) :=
⟨λ r s,
begin
  classical,
  by_contra r_ne_s,
  have z : (2 : cardinal) ≤ #(X ⟶ Y),
  { rw cardinal.two_le_iff,
    exact ⟨_, _, r_ne_s⟩ },
  let md := Σ (Z W : C), Z ⟶ W,
  let α := #md,
  apply not_le_of_lt (cardinal.cantor α),
  let yp : C := ∏ (λ (f : md), Y),
  transitivity (#(X ⟶ yp)),
  { apply le_trans (cardinal.power_le_power_right z),
    rw cardinal.power_def,
    apply le_of_eq,
    rw cardinal.eq,
    refine ⟨⟨pi.lift, λ f k, f ≫ pi.π _ k, _, _⟩⟩,
    { intros f,
      ext k,
      simp },
    { intros f,
      ext,
      simp } },
  { apply cardinal.mk_le_of_injective _,
    { intro f,
      exact ⟨_, _, f⟩ },
    { rintro f g k,
      cases k,
      refl } },
end⟩

end category_theory
