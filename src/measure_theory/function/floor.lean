import measure_theory.constructions.borel_space
import measure_theory.group.basic

/-!
-/

open set measure_theory measure_theory.measure

section floor_ring

variables {R : Type*} [linear_ordered_ring R] [floor_ring R] [topological_space R]
  [order_topology R] [measurable_space R]

lemma measurable_floor [opens_measurable_space R] :
  measurable (int.floor : R → ℤ) :=
measurable_to_encodable $ λ x, by simpa only [int.preimage_floor_singleton]
  using measurable_set_Ico

@[measurability] lemma measurable.floor {α} [measurable_space α] [opens_measurable_space R]
  {f : α → R} (hf : measurable f) : measurable (λ x, ⌊f x⌋) :=
measurable_floor.comp hf

@[measurability] lemma measurable_ceil [opens_measurable_space R] :
  measurable (int.ceil : R → ℤ) :=
measurable_to_encodable $ λ x,
  by simpa only [int.preimage_ceil_singleton] using measurable_set_Ioc

@[measurability] lemma measurable_fract [borel_space R] : measurable (int.fract : R → R) :=
begin
  intros s hs,
  rw int.preimage_fract,
  exact measurable_set.Union (λ z, measurable_id.sub_const _ (hs.inter measurable_set_Ico))
end
