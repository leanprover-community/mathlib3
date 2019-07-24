/- Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Basic setup for measurable spaces.
-/

import topology.Top.basic
import measure_theory.giry_monad
import category_theory.monad.algebra

noncomputable theory

open category_theory measure_theory
universes u v

@[reducible] def Meas : Type (u+1) := bundled measurable_space

namespace Meas

instance (x : Meas) : measurable_space x := x.str

instance : concrete_category @measurable := ⟨@measurable_id, @measurable.comp⟩

def of (X : Type u) [measurable_space X] : Meas := ⟨X⟩

-- -- If `measurable` were a class, we would summon instances:
-- local attribute [class] measurable
-- instance {X Y : Meas} (f : X ⟶ Y) : measurable (f : X → Y) := f.2

def Measure : Meas ⥤ Meas :=
{ obj      := λX, ⟨@measure_theory.measure X.1 X.2⟩,
  map      := λX Y f, ⟨measure.map f, measure.measurable_map f f.2⟩,
  map_id'  := assume ⟨α, I⟩, subtype.eq $ funext $ assume μ, @measure.map_id α I μ,
  map_comp':=
    assume X Y Z ⟨f, hf⟩ ⟨g, hg⟩, subtype.eq $ funext $ assume μ, (measure.map_map hg hf).symm }

instance : category_theory.monad Measure.{u} :=
{ η :=
  { app         := λX, ⟨@measure.dirac X.1 X.2, measure.measurable_dirac⟩,
    naturality' :=
      assume X Y ⟨f, hf⟩, subtype.eq $ funext $ assume a, (measure.map_dirac hf a).symm },
  μ :=
  { app         := λX, ⟨@measure.join X.1 X.2, measure.measurable_join⟩,
    naturality' :=
      assume X Y ⟨f, hf⟩, subtype.eq $ funext $ assume μ, measure.join_map_map hf μ },
  assoc' := assume ⟨α, I⟩, subtype.eq $ funext $ assume μ, @measure.join_map_join α I μ,
  left_unit' := assume ⟨α, I⟩, subtype.eq $ funext $ assume μ, @measure.join_dirac α I μ,
  right_unit' := assume ⟨α, I⟩, subtype.eq $ funext $ assume μ, @measure.join_map_dirac α I μ }

def Integral : monad.algebra Measure :=
{ A      := @category_theory.bundled.mk _ ennreal (borel ennreal),
  a      := ⟨ λm:measure ennreal, m.integral id, measure.measurable_integral _ measurable_id ⟩,
  unit'  := subtype.eq $ funext $ assume r:ennreal, measure.integral_dirac _ measurable_id,
  assoc' := subtype.eq $ funext $ assume μ : measure (measure ennreal),
    show μ.join.integral id = measure.integral (μ.map (λm:measure ennreal, m.integral id)) id, from
    begin
      rw [measure.integral_join measurable_id, measure.integral_map measurable_id],
      refl,
      exact measure.measurable_integral _ measurable_id
    end }

end Meas

def Borel : Top ⥤ Meas :=
concrete_functor @measure_theory.borel @measure_theory.measurable_of_continuous
