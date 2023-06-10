/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import category_theory.preadditive.injective
import algebra.homology.single

/-!
# Injective resolutions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a cochain map `I.ι` from cochain complex consisting just of `Z` in degree zero to `C`,
so that the augmented cochain complex is exact.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

open injective

variables [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of injective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

Except in situations where you want to provide a particular injective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `injective_resolution Z`: the `ℕ`-indexed cochain complex
  (equipped with `injective` and `exact` instances)
* `injective_resolution.ι Z`: the cochain map from  `(single C _ 0).obj Z` to
  `injective_resolution Z` (all the components are equipped with `mono` instances,
  and when the category is `abelian` we will show `ι` is a quasi-iso).
-/
@[nolint has_nonempty_instance]
structure InjectiveResolution (Z : C) :=
(cocomplex : cochain_complex C ℕ)
(ι: ((cochain_complex.single₀ C).obj Z) ⟶ cocomplex)
(injective : ∀ n, injective (cocomplex.X n) . tactic.apply_instance)
(exact₀ : exact (ι.f 0) (cocomplex.d 0 1) . tactic.apply_instance)
(exact : ∀ n, exact (cocomplex.d n (n+1)) (cocomplex.d (n+1) (n+2)) . tactic.apply_instance)
(mono : mono (ι.f 0) . tactic.apply_instance)

attribute [instance] InjectiveResolution.injective InjectiveResolution.mono

/-- An object admits a injective resolution. -/
class has_injective_resolution (Z : C) : Prop :=
(out [] : nonempty (InjectiveResolution Z))

section
variables (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[enough_injectives C]` and `[abelian C]`. -/
class has_injective_resolutions : Prop :=
(out : ∀ Z : C, has_injective_resolution Z)

attribute [instance, priority 100] has_injective_resolutions.out

end

namespace InjectiveResolution

@[simp] lemma ι_f_succ {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
  I.ι.f (n+1) = 0 :=
begin
  apply zero_of_source_iso_zero,
  dsimp, refl,
end

@[simp] lemma ι_f_zero_comp_complex_d {Z : C} (I : InjectiveResolution Z) :
  I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 :=
I.exact₀.w

@[simp] lemma complex_d_comp {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
  I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 :=
(I.exact _).w

instance {Z : C} (I : InjectiveResolution Z) (n : ℕ) : category_theory.mono (I.ι.f n) :=
by cases n; apply_instance

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
def self (Z : C) [category_theory.injective Z] : InjectiveResolution Z :=
{ cocomplex := (cochain_complex.single₀ C).obj Z,
  ι := 𝟙 ((cochain_complex.single₀ C).obj Z),
  injective := λ n, begin
    cases n;
    { dsimp, apply_instance },
  end,
  exact₀ := by { dsimp, exact exact_epi_zero _ },
  exact := λ n, by { dsimp, exact exact_of_zero _ _ },
  mono := by { dsimp, apply_instance, }, }

end InjectiveResolution

end category_theory
