/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.abelian.exact
import category_theory.preadditive.projective

/-!
# Abelian categories with enough projectives have projective resolutions

When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
-/


noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory.projective

variables {C : Type u} [category.{v} C]

variables [enough_projectives C] [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

namespace resolution

/- We have to jump through some hoops to get `resolution.of` to typecheck! -/
section
variables (O : C → C) (π : Π X, O X ⟶ X)
variables (L : Π {X Y : C} (f : X ⟶ Y), C) (δ : Π {X Y : C} (f : X ⟶ Y), L f ⟶ X)

/-- An auxiliary construction for `resolution.of`. -/
def B' (Z : C) : ℕ → Σ (X Y : C), X ⟶ Y
| 0 := ⟨O Z, Z, π Z⟩
| (n+1) := ⟨L (B' n).2.2, (B' n).1, δ (B' n).2.2⟩

/-- An auxiliary construction for `resolution.of`. -/
def X' (Z : C) (n : ℕ) : C := (B' O π @L @δ Z n).2.1

/-- An auxiliary construction for `resolution.of`. -/
def d' (Z : C) (n : ℕ) : X' O π @L @δ Z (n+1) ⟶ X' O π @L @δ Z n :=
(B' O π @L @δ Z n).2.2

end

variables [enough_projectives C] [abelian C]

/--
In any category with enough projectives,
`projective.resolution.of Z` constructs a projection resolution of the object `Z`.
-/
def of (Z : C) : resolution Z :=
{ X := λ n, X' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.left f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  d := λ n, d' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.left f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  zero := iso.refl _,
  projective := λ n,
  begin
    induction n;
    { dsimp [X', B'],
      apply_instance, },
  end,
  epi := projective.π_epi _,
  exact := λ n, exact_d_f _ }

end resolution


end category_theory.projective
