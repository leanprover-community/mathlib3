/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import linear_algebra.span

/-!
# Tannaka duality for rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/

universes u

open category_theory

/--
An ingredient of Tannaka duality for rings:
A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.
-/
def ring_equiv_End_forget₂ (R : Type u) [ring R] :
  R ≃+* End (AdditiveFunctor.of (forget₂ (Module.{u} R) AddCommGroup.{u})) :=
{ to_fun := λ r,
  { app := λ M, by apply distrib_mul_action.to_add_monoid_hom M r,
    naturality' := λ M N f, by { ext, exact (f.map_smul _ _).symm, }, },
  inv_fun := λ φ, φ.app (Module.of R R) (1 : R),
  left_inv := by { intros r, simp, },
  right_inv := begin
    intros φ, ext M x,
    simp only [distrib_mul_action.to_add_monoid_hom_apply],
    have w := add_monoid_hom.congr_fun
      (φ.naturality (Module.as_hom_right (linear_map.to_span_singleton R M x))) (1 : R),
    convert w.symm,
    exact (one_smul _ _).symm,
  end,
  map_add' := by { intros, ext, simp [add_smul], },
  map_mul' := by { intros, ext, simpa using mul_smul _ _ _, }, }
