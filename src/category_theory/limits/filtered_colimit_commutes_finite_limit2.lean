/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.colimit_limit2
import category_theory.limits.shapes.finite_limits

/-!
# Filtered colimits commute with finite limits.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimit_limit_to_limit_colimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/

universes v₁ v₂ u₁ u₂ u₃

open category_theory
open category_theory.category
open category_theory.limits.types
open category_theory.limits.types.filtered_colimit

namespace category_theory.limits

variables {J : Type u₁} {K : Type u₂} [category.{v₁} J] [category.{v₂} K]

variables (F : J ⥤ K ⥤ Type u₃)

variables {cj : Π (j : J), cone (F.obj j)}
variables {ck : Π (k : K), cocone (F.flip.obj k)}
variables (tj : Π (j : J), is_limit (cj j))
variables (tk : Π (k : K), is_colimit (ck k))
variables {c₁ : cocone (cones_to_functor tj)} (t₁ : is_colimit c₁)
variables {c₂ : cone (cocones_to_functor tk)} (t₂ : is_limit c₂)

variables [fin_category J]
variables [is_filtered K]

section

def filtered_colimit_finite_limit_iso : c₁.X ≅ c₂.X :=
{ hom := colimit_to_limit tj tk t₁ t₂,
  inv := sorry }

end

end category_theory.limits
