/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/

import category_theory.abelian.exact
import category_theory.preadditive.injective
import category_theory.preadditive.yoneda.limits
import category_theory.preadditive.yoneda.injective

/-!
# Injective objects in abelian categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* Objects in an abelian categories are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.injective
open opposite

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C] [abelian C]

/-- The preadditive Yoneda functor on `J` preserves colimits if `J` is injective. -/
def preserves_finite_colimits_preadditive_yoneda_obj_of_injective (J : C)
  [hP : injective J] : preserves_finite_colimits (preadditive_yoneda_obj J) :=
begin
  letI := (injective_iff_preserves_epimorphisms_preadditive_yoneda_obj' J).mp hP,
  apply functor.preserves_finite_colimits_of_preserves_epis_and_kernels,
end

/-- An object is injective if its preadditive Yoneda functor preserves finite colimits. -/
lemma injective_of_preserves_finite_colimits_preadditive_yoneda_obj (J : C)
  [hP : preserves_finite_colimits (preadditive_yoneda_obj J)] : injective J :=
begin
  rw injective_iff_preserves_epimorphisms_preadditive_yoneda_obj',
  apply_instance
end

end category_theory
