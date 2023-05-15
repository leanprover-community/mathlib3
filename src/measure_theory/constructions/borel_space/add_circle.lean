import topology.instances.add_circle
import measure_theory.constructions.borel_space.basic

noncomputable theory

instance add_circle.measurable_space {a : ℝ} : measurable_space (add_circle a) :=
borel (add_circle a)

instance add_circle.borel_space {a : ℝ} : borel_space (add_circle a) := ⟨rfl⟩

@[measurability] protected lemma add_circle.measurable_mk' {a : ℝ} :
  measurable (coe : ℝ → add_circle a) :=
continuous.measurable $ add_circle.continuous_mk' a
