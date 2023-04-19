/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.equivalence

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 Tools for compatibilities between Dold-Kan equivalences

The purpose of this file is to introduce tools which will enable the
construction of the Dold-Kan equivalence `simplicial_object C ≌ chain_complex C ℕ`
for a pseudoabelian category `C` from the equivalence
`karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)` and the two
equivalences `simplicial_object C ≅ karoubi (simplicial_object C)` and
`chain_complex C ℕ ≅ karoubi (chain_complex C ℕ)`.

It is certainly possible to get an equivalence `simplicial_object C ≌ chain_complex C ℕ`
using a compositions of the three equivalences above, but then neither the functor
nor the inverse would have good definitional properties. For example, it would be better
if the inverse functor of the equivalence was exactly the functor
`Γ₀ : simplicial_object C ⥤ chain_complex C ℕ` which was constructed in `functor_gamma.lean`.

In this file, given four categories `A`, `A'`, `B`, `B'`, equivalences `eA : A ≅ A'`,
`eB : B ≅ B'`, `e' : A' ≅ B'`, functors `F : A ⥤ B'`, `G : B ⥤ A` equipped with certain
compatibilities, we construct successive equivalences:
- `equivalence₀` from `A` to `B'`, which is the composition of `eA` and `e'`.
- `equivalence₁` from `A` to `B'`, with the same inverse functor as `equivalence₀`,
but whose functor is `F`.
- `equivalence₂` from `A` to `B`, which is the composition of `equivalence₁` and the
inverse of `eB`:
- `equivalence` from `A` to `B`, which has the same functor `F ⋙ eB.inverse` as `equivalence₂`,
but whose inverse functor is `G`.

When extra assumptions are given, we shall also provide simplification lemmas for the
unit and counit isomorphisms of `equivalence`. (TODO)

-/

open category_theory category_theory.category

namespace algebraic_topology

namespace dold_kan

namespace compatibility

variables {A A' B B' : Type*} [category A] [category A'] [category B] [category B']
  (eA : A ≌ A') (eB : B ≌ B') (e' : A' ≌ B')
  {F : A ⥤ B'} (hF : eA.functor ⋙ e'.functor ≅ F)
  {G : B ⥤ A} (hG : eB.functor ⋙ e'.inverse ≅ G ⋙ eA.functor)

/-- A basic equivalence `A ≅ B'` obtained by composing `eA : A ≅ A'` and `e' : A' ≅ B'`. -/
@[simps functor inverse unit_iso_hom_app]
def equivalence₀ : A ≌ B' := eA.trans e'

include hF
variables {eA} {e'}

/-- An intermediate equivalence `A ≅ B'` whose functor is `F` and whose inverse is
`e'.inverse ⋙ eA.inverse`. -/
@[simps functor]
def equivalence₁ : A ≌ B' :=
begin
  letI : is_equivalence F :=
    is_equivalence.of_iso hF (is_equivalence.of_equivalence (equivalence₀ eA e')),
  exact F.as_equivalence,
end

lemma equivalence₁_inverse : (equivalence₁ hF).inverse = e'.inverse ⋙ eA.inverse := rfl

/-- The counit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps]
def equivalence₁_counit_iso :
  (e'.inverse ⋙ eA.inverse) ⋙ F ≅ 𝟭 B' :=
calc (e'.inverse ⋙ eA.inverse) ⋙ F
  ≅ (e'.inverse ⋙ eA.inverse) ⋙ (eA.functor ⋙ e'.functor) : iso_whisker_left _ hF.symm
... ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.functor) ⋙ e'.functor : iso.refl _
... ≅ e'.inverse ⋙ 𝟭 _ ⋙ e'.functor : iso_whisker_left _ (iso_whisker_right eA.counit_iso _)
... ≅ e'.inverse ⋙ e'.functor : iso.refl _
... ≅ 𝟭 B' : e'.counit_iso

lemma equivalence₁_counit_iso_eq : (equivalence₁ hF).counit_iso = equivalence₁_counit_iso hF :=
begin
  ext Y,
  dsimp [equivalence₀, equivalence₁, is_equivalence.inverse, is_equivalence.of_equivalence],
  simp only [equivalence₁_counit_iso_hom_app, category_theory.functor.map_id, comp_id],
end

/-- The unit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps]
def equivalence₁_unit_iso :
  𝟭 A ≅ F ⋙ (e'.inverse ⋙ eA.inverse) :=
calc 𝟭 A ≅ eA.functor ⋙ eA.inverse : eA.unit_iso
... ≅ eA.functor ⋙ 𝟭 A' ⋙ eA.inverse : iso.refl _
... ≅ eA.functor ⋙ (e'.functor ⋙ e'.inverse) ⋙ eA.inverse :
  iso_whisker_left _ (iso_whisker_right e'.unit_iso _)
... ≅ (eA.functor ⋙ e'.functor) ⋙ (e'.inverse ⋙ eA.inverse) : iso.refl _
... ≅ F ⋙ (e'.inverse ⋙ eA.inverse) : iso_whisker_right hF _

lemma equivalence₁_unit_iso_eq : (equivalence₁ hF).unit_iso = equivalence₁_unit_iso hF :=
begin
  ext X,
  dsimp [equivalence₀, equivalence₁, nat_iso.hcomp,
    is_equivalence.of_equivalence],
  simp only [id_comp, assoc, equivalence₁_unit_iso_hom_app],
end

include eB

/-- An intermediate equivalence `A ≅ B` obtained as the composition of `equivalence₁` and
the inverse of `eB : B ≌ B'`. -/
@[simps functor]
def equivalence₂ : A ≌ B := (equivalence₁ hF).trans eB.symm

lemma equivalence₂_inverse : (equivalence₂ eB hF).inverse =
  eB.functor ⋙ e'.inverse ⋙ eA.inverse := rfl

/-- The counit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps]
def equivalence₂_counit_iso :
  (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ (F ⋙ eB.inverse) ≅ 𝟭 B :=
calc (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ (F ⋙ eB.inverse)
  ≅ eB.functor ⋙ (e'.inverse ⋙ eA.inverse ⋙ F) ⋙ eB.inverse : iso.refl _
... ≅ eB.functor ⋙ 𝟭 _ ⋙ eB.inverse :
  iso_whisker_left _ (iso_whisker_right (equivalence₁_counit_iso hF) _)
... ≅ eB.functor ⋙ eB.inverse : iso.refl _
... ≅ 𝟭 B : eB.unit_iso.symm

lemma equivalence₂_counit_iso_eq :
  (equivalence₂ eB hF).counit_iso = equivalence₂_counit_iso eB hF :=
begin
  ext Y',
  dsimp [equivalence₂, iso.refl],
  simp only [equivalence₁_counit_iso_eq, equivalence₂_counit_iso_hom_app,
    equivalence₁_counit_iso_hom_app, functor.map_comp, assoc],
end

/-- The unit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps]
def equivalence₂_unit_iso :
  𝟭 A ≅ (F ⋙ eB.inverse) ⋙ (eB.functor ⋙ e'.inverse ⋙ eA.inverse) :=
calc 𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse : equivalence₁_unit_iso hF
... ≅ F ⋙ 𝟭 B' ⋙ (e'.inverse ⋙ eA.inverse) : iso.refl _
... ≅ F ⋙ (eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :
  iso_whisker_left _ (iso_whisker_right eB.counit_iso.symm _)
... ≅ (F ⋙ eB.inverse) ⋙ (eB.functor ⋙ e'.inverse ⋙ eA.inverse) : iso.refl _

lemma equivalence₂_unit_iso_eq :
  (equivalence₂ eB hF).unit_iso = equivalence₂_unit_iso eB hF :=
begin
  ext X,
  dsimp [equivalence₂],
  simpa only [equivalence₂_unit_iso_hom_app, equivalence₁_unit_iso_eq,
    equivalence₁_unit_iso_hom_app, assoc, nat_iso.cancel_nat_iso_hom_left],
end

variable {eB}
include hG

/-- The equivalence `A ≅ B` whose functor is `F ⋙ eB.inverse` and
whose inverse is `G : B ≅ A`. -/
@[simps inverse]
def equivalence : A ≌ B :=
begin
  letI : is_equivalence G := begin
    refine is_equivalence.of_iso _ (is_equivalence.of_equivalence (equivalence₂ eB hF).symm),
    calc eB.functor ⋙ e'.inverse ⋙ eA.inverse
      ≅ (eB.functor ⋙ e'.inverse) ⋙ eA.inverse : iso.refl _
    ... ≅ (G ⋙ eA.functor) ⋙ eA.inverse : iso_whisker_right hG _
    ... ≅ G ⋙ 𝟭 A : iso_whisker_left _ eA.unit_iso.symm
    ... ≅ G : functor.right_unitor G,
  end,
  exact G.as_equivalence.symm,
end

lemma equivalence_functor : (equivalence hF hG).functor = F ⋙ eB.inverse := rfl

end compatibility

end dold_kan

end algebraic_topology
