/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.subobject.factor_thru
import category_theory.subobject.well_powered
import category_theory.limits.comma
import category_theory.limits.constructions.epi_mono
import category_theory.limits.preserves.finite
import category_theory.limits.shapes.finite_limits

/-!
# Subobject in comma categories
-/

open category_theory.limits

universes v u₁ u₂

namespace category_theory
variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]

namespace structured_arrow
variables {S : D} {T : C ⥤ D}

def subobject_equiv [has_limits C] [preserves_limits T] (A : structured_arrow S T) :
  subobject A ≃o { P : subobject ((proj _ _).obj A) // ∃ q, q ≫ T.map P.arrow = A.hom } :=
{ to_fun :=
  begin
    apply subobject.indu
    --refine ⟨(subobject.lift (proj S T)).obj P, _⟩,

  end,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_rel_iff' := _ }


end structured_arrow

end category_theory
