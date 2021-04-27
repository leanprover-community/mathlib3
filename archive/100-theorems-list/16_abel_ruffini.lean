import field_theory.abel_ruffini

open polynomial polynomial.gal

lemma nat_degree_poly (a : ℕ) (b : ℤ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).nat_degree = 5 :=
begin
  have h05 : 0 < 5 := nat.zero_lt_bit1 2,
  have h15 : 1 < 5 := one_lt_bit1.mpr zero_lt_two,
  apply le_antisymm,
  { rw nat_degree_le_iff_coeff_eq_zero,
    intros n hn,
    rw [coeff_add, coeff_sub, coeff_X_pow, if_neg (ne_of_gt hn),
        coeff_C_mul, coeff_X, if_neg (ne_of_lt (h15.trans hn)), mul_zero,
        coeff_C, if_neg (ne_of_gt (h05.trans hn)), sub_zero, add_zero] },
  { apply le_nat_degree_of_ne_zero,
    rw [coeff_add, coeff_sub, coeff_X_pow, if_pos rfl,
        coeff_C_mul, coeff_X, if_neg (ne_of_lt h15), mul_zero,
        coeff_C, if_neg (ne_of_gt h05), sub_zero, add_zero],
    exact one_ne_zero },
end

lemma leading_coeff_poly (a : ℕ) (b : ℤ) :
  (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).leading_coeff = 1 :=
by rw [leading_coeff, nat_degree_poly, coeff_add, coeff_sub, coeff_X_pow_self,
  coeff_C_mul, coeff_X, if_neg (nat.one_ne_bit1 two_ne_zero), mul_zero, sub_zero,
  coeff_C, if_neg (nat.bit1_ne_zero 2), add_zero]

lemma monic_poly (a : ℕ) (b : ℤ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).monic :=
leading_coeff_poly a b

--todo: rewrite proof using above lemmas
lemma irreducible_poly (a : ℕ) (b : ℤ) (p : ℕ)
  (hp : p.prime) (hpa : p ∣ a) (hpb : ↑p ∣ b) (hp2b : ¬ (↑p ^ 2 ∣ b)) :
  irreducible (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ) :=
begin
  have h05 : 0 < 5 := nat.zero_lt_bit1 2,
  have h15 : 1 < 5 := one_lt_bit1.mpr zero_lt_two,
  let q : polynomial ℚ := X ^ 5 - C ↑a * X + C ↑b,
  change irreducible q,
  let r : polynomial ℤ := X ^ 5 - C ↑a * X + C b,
  have r_map : r.map (int.cast_ring_hom ℚ) = q,
  { rw [map_add, map_sub, map_mul, map_pow, map_X, map_C, map_C],
    refl },
  have r_nat_degree : r.nat_degree = 5,
  { rw [←nat_degree_map' _ r, r_map, nat_degree_poly],
    exact int.cast_injective },
  have r_leading_coeff : r.leading_coeff = 1,
  { rw [leading_coeff, r_nat_degree, coeff_add, coeff_sub, coeff_X_pow_self, coeff_C_mul, coeff_X,
        if_neg (ne_of_lt h15), mul_zero, sub_zero, coeff_C, if_neg (ne_of_gt h05), add_zero] },
  have r_monic : r.monic := r_leading_coeff,
  have r_primitive : r.is_primitive := r_monic.is_primitive,
  have r_degree : r.degree = ↑5 := by rw [degree_eq_nat_degree r_monic.ne_zero, r_nat_degree],
  rw [←r_map, ←is_primitive.int.irreducible_iff_irreducible_map_cast r_primitive],
  apply irreducible_of_eisenstein_criterion,
  { rwa [ideal.span_singleton_prime (int.coe_nat_ne_zero.mpr hp.ne_zero),
      int.prime_iff_nat_abs_prime] },
  { rw [r_leading_coeff, ideal.mem_span_singleton],
    exact λ h, hp.ne_one (int.coe_nat_inj ((int.eq_one_of_dvd_one (int.coe_nat_nonneg p)) h)) },
  { intros n hn,
    rw ideal.mem_span_singleton,
    rw [r_degree, with_bot.coe_lt_coe] at hn,
    interval_cases n with hn,
    all_goals { rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] },
    all_goals { norm_num },
    { exact hpb },
    { exact int.coe_nat_dvd.mpr hpa } },
  { rw [r_degree, ←with_bot.coe_zero, with_bot.coe_lt_coe],
    norm_num },
  { rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C],
    norm_num,
    rwa [pow_two, ideal.span_singleton_mul_span_singleton, ←pow_two, ideal.mem_span_singleton] },
  { exact is_primitive_iff_is_unit_of_C_dvd.mp r_primitive },
end

lemma complex_roots_poly (a : ℕ) (b : ℤ) (hab : abs b < a) :
  fintype.card ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).root_set ℝ) = 3 :=
begin
  apply le_antisymm,
  sorry,
  sorry,
end

lemma gal_poly (a : ℕ) (b : ℤ) (p : ℕ) (hab : abs b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : ↑p ∣ b) (hp2b : ¬ (↑p ^ 2 ∣ b)) :
  function.bijective (gal_action_hom (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ) ℂ) :=
begin
  let q : polynomial ℚ := X ^ 5 - C ↑a * X + C ↑b,
  change function.bijective (gal_action_hom q ℂ),
  have q_irred : irreducible q := irreducible_poly a b p hp hpa hpb hp2b,
  apply gal_action_hom_bijective_of_prime_degree q_irred,
  { rw nat_degree_poly,
    norm_num },
  { have h1 : fintype.card (q.root_set ℂ) = 5,
    { simp_rw [root_set_def, fintype.card_coe],
      rw [multiset.to_finset_card_of_nodup, ←nat_degree_eq_card_roots, nat_degree_poly],
      { exact is_alg_closed.splits_codomain q },
      { exact nodup_roots ((separable_map _).mpr q_irred.separable) } },
    have h2 : fintype.card (q.root_set ℝ) = 3,
    { exact complex_roots_poly a b hab },
    rw [h1, h2] },
end

theorem tada (x : ℂ) (a : ℕ) (b : ℤ) (p : ℕ) (hab : abs b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : ↑p ∣ b) (hp2b : ¬ (↑p ^ 2 ∣ b))
  (hx : aeval x (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  apply solvable_by_rad.is_solvable_contrapositive (irreducible_poly a b p hp hpa hpb hp2b)
    (monic_poly a b) hx,
end
