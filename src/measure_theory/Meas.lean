/- Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Basic setup for measurable spaces.
-/

import topology.Top.basic
import measure_theory.borel_space

open category_theory
universes u v

@[reducible] def Meas : Type (u+1) := bundled measurable_space

instance (x : Meas) : measurable_space x := x.str

namespace Meas

instance : concrete_category @measurable := ⟨@measurable_id, @measurable.comp⟩

def of (X : Type u) [measurable_space X] : Meas := ⟨X⟩

-- -- If `measurable` were a class, we would summon instances:
-- local attribute [class] measurable
-- instance {X Y : Meas} (f : X ⟶ Y) : measurable (f : X → Y) := f.2
end Meas

def Borel : Top ⥤ Meas :=
concrete_functor @measure_theory.borel @measure_theory.measurable_of_continuous
