import number_theory.number_field.canonical_embedding

section log_embedding

open number_field number_field.infinite_place

variables (K : Type*) [field K]

open additive

noncomputable def log_embedding : Kˣ → (infinite_place K → ℝ) := λ x w, real.log (w x)

lemma log_embedding.map_one :
  log_embedding K 1 = 0 :=
by simpa only [log_embedding, infinite_place.map_one, real.log_one, units.coe_one]

lemma log_embedding.map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, infinite_place.map_mul, real.log_mul, units.coe_mul, ne.def,
  infinite_place.eq_zero, units.ne_zero, not_false_iff]

end log_embedding
