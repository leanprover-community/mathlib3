/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yury Kudryashov
-/
import data.rel category_theory.types

/-!
The category of types with binary relations as morphisms.
-/

namespace category_theory

universe u

/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def Rel := Type u

/-- The category of types with binary relations as morphisms. -/
-- We must work in `Type u` rather than `Sort u`, because
-- `X → Y → Prop` is in `Sort (max u 1)`.
instance Rel.category : large_category Rel.{u} :=
{ hom := rel,
  comp := @rel.comp,
  id := @eq,
  comp_id' := @rel.comp_right_id,
  id_comp' := @rel.comp_left_id,
  assoc' := @rel.comp_assoc }

def graph'_functor : Type u ⥤ Rel.{u} :=
{ obj := id,
  map := @function.graph',
  map_id' := @function.graph'_id,
  map_comp' := @function.graph'_comp }

instance graph'_functor_faithful : faithful graph'_functor :=
⟨@function.graph'_inj⟩

end category_theory
