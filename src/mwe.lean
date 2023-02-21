import number_theory.number_field.norm

open_locale number_field

section toto

open finite_dimensional number_field ring_of_integers

variables {L : Type*} (K : Type*) [field K] [field L] [algebra K L]

instance : algebra (𝓞 K) (𝓞 L) := ring_of_integers_algebra _ _

lemma toto {x : 𝓞 K} [is_scalar_tower (𝓞 K) K L]  [is_separable K L] [finite_dimensional K L] :
  norm K (algebra_map (𝓞 K) (𝓞 L) x) = x ^ (finrank K L) :=
begin
  have : function.injective (algebra_map (𝓞 K) (𝓞 L)) := sorry,
  apply (function.injective.eq_iff this).mp,
  have : function.injective (coe : (𝓞 L) → L) := sorry,
  apply (function.injective.eq_iff this).mp,
  rw coe_algebra_map_norm,
  rw (_ : ↑((algebra_map ↥(𝓞 K) ↥(𝓞 L)) x) = (algebra_map K L x)),
  rw algebra.norm_algebra_map,
  refl,
  refl,
end

end toto

section norm

namespace algebra

variables (R S T : Type*) [comm_ring R] [comm_ring S] [ring T] [algebra R S] [algebra S T]
  [algebra R T] [is_scalar_tower R S T]

lemma norm_composition (x : T) :
  norm R (norm S x) = norm R x :=
begin
  sorry
end

end algebra

namespace ring_of_integers

variables {L : Type*} (F K : Type*) [field K] [field L] [field F]
  [algebra K L] [algebra F K] [algebra F L] [is_scalar_tower F K L]
  [is_separable F K] [finite_dimensional F K] [is_separable K L]
  [finite_dimensional K L] [is_separable F L] [finite_dimensional F L]

lemma norm_composition (x : 𝓞 L) :
  norm F (norm K x) = norm F x :=
begin
  sorry
end

end ring_of_integers

end norm
