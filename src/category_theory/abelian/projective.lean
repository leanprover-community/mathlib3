/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.abelian.exact
import category_theory.preadditive.projective_resolution
import algebra.homology.augment

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

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `projective.syzygies`
applied to the previously constructed morphism,
and the map to the `n`-th object as `projective.d`.
-/

variables [abelian C] [enough_projectives C]

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps]
def of_complex (Z : C) : chain_complex C ℕ :=
chain_complex.mk'
  (projective.over Z) (projective.syzygies (projective.π Z)) (projective.d (projective.π Z))
  (λ ⟨X, Y, f⟩, ⟨projective.syzygies f, projective.d f, (exact_d_f f).w⟩)

/--
In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projection resolution of the object `Z`.
-/
@[irreducible] def of (Z : C) : ProjectiveResolution Z :=
{ complex := of_complex Z,
  π := chain_complex.mk_hom _ _ (projective.π Z) 0
    (by { simp, exact (exact_d_f (projective.π Z)).w.symm, })
    (λ n _, ⟨0, by ext⟩),
  projective := by { rintros (_|_|_|n); apply projective.projective_over, },
  exact₀ := by simpa using exact_d_f (projective.π Z),
  exact := by { rintros (_|n); { simp, apply exact_d_f, }, },
  epi := projective.π_epi Z, }

@[priority 100]
instance (Z : C) : has_projective_resolution Z :=
{ out := ⟨of Z⟩ }

@[priority 100]
instance : has_projective_resolutions C :=
{ out := λ Z, by apply_instance }

end ProjectiveResolution

end category_theory
