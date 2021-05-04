/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.abelian.exact
import category_theory.preadditive.projective_resolution

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

namespace category_theory

open category_theory.projective

variables {C : Type u} [category.{v} C]

section
variables [enough_projectives C] [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

end

namespace ProjectiveResolution

/- We have to jump through some hoops to get `ProjectiveResolution.of` to typecheck! -/
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

variables [abelian C]

/--
A repackaging of the data in `ProjectiveResolution`.
This is purely an implementation detail of `ProjectiveResolution.of`.
-/
@[nolint has_inhabited_instance]
structure aux_struct (Z : C) :=
(X : ℕ → C)
(d : Π n, X (n+1) ⟶ X n)
(zero : X 0 ≅ Z)
(projective : ∀ n, category_theory.projective (X (n+1)))
(epi : category_theory.epi (d 0))
(exact : ∀ n, category_theory.exact (d (n+1)) (d n))

/--
Convert an `aux_struct` to a `ProjectiveResolution`.
-/
def of_aux_struct {Z : C} (P : aux_struct Z) : ProjectiveResolution Z :=
let E := (chain_complex.of P.X P.d (λ n, (P.exact n).w)) in
{ complex := chain_complex.truncate.obj E,
  π := E.truncate_to ≫ ((chain_complex.single_0 C).map_iso P.zero).hom,
  projective := P.projective,
  exact₀ := begin
    dsimp [chain_complex.truncate_to, chain_complex.to_single_0_equiv],
    simp only [category_theory.exact_comp_iso, E, chain_complex.of_d],
    exact P.exact 0,
  end,
  exact := λ n, begin
    dsimp [chain_complex.truncate_to, chain_complex.to_single_0_equiv],
    simp only [category_theory.exact_comp_iso, E, chain_complex.of_d],
    exact P.exact (n+1),
  end,
  epi := begin
    dsimp [chain_complex.truncate_to, chain_complex.to_single_0_equiv],
    simp only [chain_complex.of_d],
    haveI := P.epi,
    apply epi_comp,
  end, }

variables [enough_projectives C]

/--
In any category with enough projectives,
`ProjectiveResolution.of Z` constructs a projection resolution of the object `Z`.
-/
@[irreducible] def of (Z : C) : ProjectiveResolution Z :=
ProjectiveResolution.of_aux_struct
{ X := λ n, X' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.syzygies f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  d := λ n, d' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.syzygies f)
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

@[priority 100]
instance (Z : C) : has_projective_resolution Z :=
{ out := ⟨of Z⟩ }

@[priority 100]
instance : has_projective_resolutions C :=
{ out := λ Z, by apply_instance }

end ProjectiveResolution

end category_theory
