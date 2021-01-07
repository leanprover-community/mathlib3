import ring_theory.localization

section fraction_map

variables {R K L : Type*} [integral_domain R] [field K]
variables (f : fraction_map R K)

lemma fraction_map.map_ne_zero {x : R} (hx : x ≠ 0) : f.to_map x ≠ 0 :=
mt (f.to_map.injective_iff.mp (fraction_map.injective f) _) hx

end fraction_map
