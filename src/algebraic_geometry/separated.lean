/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import algebraic_geometry.pullbacks
import algebraic_geometry.closed_immersion

/-!
# Separated Morphisms

A morphism between schemes `f : X ⟶ Y` is separated iff the digonal morphism `X ⟶ X ×[Y] X` is
a closed immersion.

-/


namespace algebraic_geometry
open topological_space category_theory opposite
open category_theory.limits

/-- A morphism of schemes `f : X ⟶ Y` is separated iff the digonal morphism `X ⟶ X ×[Y] X` is a
closed immersion.-/
def is_separated_morphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
is_closed_immersion (pullback.lift (𝟙 _) (𝟙 _) rfl : X ⟶ pullback f f)

end algebraic_geometry
