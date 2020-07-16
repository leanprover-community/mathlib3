import data.polynomial
import data.zmod.basic

namespace polynomial
variables {R S : Type*} [semiring R] [integral_domain S] (φ : R →+* S)

lemma is_unit_of_is_unit_leading_coeff_of_is_unit_map
  (f : polynomial R) (hf : is_unit (leading_coeff f)) (H : is_unit (map φ f)) :
  is_unit f :=
begin
  have dz := degree_eq_zero_of_is_unit H,
  rw degree_map_eq_of_leading_coeff_ne_zero at dz,
  { rw eq_C_of_degree_eq_zero dz,
    apply is_unit.map',
    convert hf,
    rw (degree_eq_iff_nat_degree_eq _).1 dz,
    rintro rfl,
    simpa using H, },
  { intro h,
    have u : is_unit (φ f.leading_coeff) := is_unit.map' _ hf,
    rw h at u,
    simpa using u, }
end

lemma irreducible_of_irreducible_mod_prime (f : polynomial ℤ) (p : ℕ) [fact p.prime]
  (h_mon : monic f) (h_irr : irreducible (map (int.cast_ring_hom (zmod p)) f)) :
  irreducible f :=
begin
  fsplit,
  { intro h,
    exact h_irr.1 (is_unit.map' (map (int.cast_ring_hom (zmod p))) h), },
  { intros a b h,

    have q := (leading_coeff_mul a b).symm,
    rw ←h at q,
    dsimp [monic] at h_mon,
    rw h_mon at q,
    have au : is_unit a.leading_coeff := is_unit_of_mul_eq_one _ _ q,
    rw mul_comm at q,
    have bu : is_unit b.leading_coeff := is_unit_of_mul_eq_one _ _ q,
    clear q h_mon,

    have h' := congr_arg (map (int.cast_ring_hom (zmod p))) h,
    simp only [map_mul] at h',
    cases h_irr.2 _ _ h' with w w,
    { left,
      exact is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ au w, },
    { right,
      exact is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ bu w, }, }
end

end polynomial
