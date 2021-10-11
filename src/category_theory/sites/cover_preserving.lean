/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.flat_functors

/-!
# Cover-preserving functors between sites.

We define cover-preserving functors between sites as functors that push covering sieves to
covering sieves. A cover-preserving and flat functor `u : F ⥤ D` then pulls sheaves on `D`
back to sheaves on `C` via `u.op ⋙ -`. This functor has a left adjoint `Lan u.op` that
preserves finite limits (`category_theory.Lan_preserves_finite_limit_of_flat`).
This pair of functors is also known as a *morphism of sites* in the literature.

## Main definitions

* `category_theory.sites.cover_preserving`: a functor between sites is cover-preserving if it
pushes covering sieves to covering sieves

## Main results

- `category_theory.sites.whiskering_left_is_sheaf_of_cover_preserving`: If `G : C ⥤ D` is
cover-preserving, then `u ⋙ -` (`uᵖ`) as a functor `(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves
maps sheaves to sheaves.

## Future work

- For a continuous functor to pull sheaves back to sheaves, it suffices for the functor to be
`covering_flat`. A good reference to this is probably [shulman2012sheaves]

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WW

-/

universes v₁ v₂ u₁ u₂
noncomputable theory

open category_theory
open opposite
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.limits

namespace category_theory
section cover_preserving
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)
variables {L : grothendieck_topology E}

/--
A functor `u : (C, J) ⥤ (D, K)` between sites is called to have the cover-preserving property
if for all covering sieves `R` in `C`, `R.pushforward_functor u` is a covering sieve in `D`.
-/
@[nolint has_inhabited_instance]
structure cover_preserving (u : C ⥤ D) :=
(cover_preserve : ∀ {U : C} {S : sieve U} (hS : S ∈ J U), S.functor_pushforward u ∈ K (u.obj U))

/-- The identity functor on a site is cover-preserving. -/
def id_cover_preserving : cover_preserving J J (𝟭 _) := ⟨λ U S hS, by simpa using hS⟩

variables (J) (K)

/-- The composition of two cover-preserving functors is cover-preserving. -/
def comp_cover_preserving {u} (hu : cover_preserving J K u) {v} (hv : cover_preserving K L v) :
  cover_preserving J L (u ⋙ v) := ⟨λ U S hS,
begin
  rw sieve.functor_pushforward_comp,
  exact hv.cover_preserve (hu.cover_preserve hS)
end⟩

end cover_preserving

variables {C D : Type u₁} [category.{v₁} C] [category.{v₁} D]
variables {A : Type u₂} [category.{v₁} A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}

/--
If `u` is cover-preserving, then `u.op ⋙ _` pulls sheaves back to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00WW,
but without the condition that `C` or `D` has pullbacks.
-/
theorem pullback_is_sheaf_of_cover_preserving {u : C ⥤ D} [representably_flat u]
  (hu : cover_preserving J K u) (ℱ : Sheaf K A) :
  presheaf.is_sheaf J (((whiskering_left _ _ _).obj u.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  change family_of_elements (u.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) ⇑S at x,
  let H := ℱ.2 X _ (hu.cover_preserve hS),
  split, swap,
  { apply H.amalgamate (x.functor_pushforward u),
    exact hx.functor_pushforward u },
  split,
  { intros V f hf,
    convert H.is_amalgamation (hx.functor_pushforward u)
      (u.map f) (image_mem_functor_pushforward u S hf),
    rw functor_pushforward_apply_map u hx },
  { intros y hy,
    refine H.is_separated_for _ y _ _ (H.is_amalgamation (hx.functor_pushforward u)),
    rintros V f ⟨Z, f', g', h, rfl⟩,
    erw family_of_elements.comp_of_compatible (S.functor_pushforward u)
      (hx.functor_pushforward u) (image_mem_functor_pushforward u S h) g',
    simpa [functor_pushforward_apply_map u hx h, ←hy f' h], }
end

end category_theory
