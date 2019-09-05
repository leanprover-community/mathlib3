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

namespace Meas

instance (X : Meas) : measurable_space X := X.str

def of (α : Type u) [measurable_space α] : Meas := ⟨α⟩

instance unbundled_hom : unbundled_hom @measurable := ⟨@measurable_id, @measurable.comp⟩

end Meas

instance Top.has_forget_to_Meas : has_forget Top.{u} Meas.{u} :=
bundled_hom.mk_has_forget
  @measure_theory.borel
  (λ X Y f, ⟨f.1, measure_theory.measurable_of_continuous f.2⟩)
  (by intros; refl)

@[reducible] def Borel : Top.{u} ⥤ Meas.{u} := forget₂ Top.{u} Meas.{u}
