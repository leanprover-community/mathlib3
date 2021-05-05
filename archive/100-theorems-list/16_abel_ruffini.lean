import field_theory.abel_ruffini
import analysis.calculus.local_extr

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
  have r_primitive : r.is_primitive := monic.is_primitive r_leading_coeff,
  have r_degree : r.degree = ↑5 := by rw [degree_eq_nat_degree r_primitive.ne_zero, r_nat_degree],
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

lemma tada_aux {α : Type*} [linear_order α] {s t : finset α}
  (h : ∀ x y ∈ s, x < y → ∃ z ∈ t, x < z ∧ z < y) : s.card ≤ t.card + 1 :=
begin
  sorry,
end

lemma tada {F : Type*} [field F] [algebra F ℝ] (p : polynomial F) :
  fintype.card (p.root_set ℝ) ≤ fintype.card (p.derivative.root_set ℝ) + 1 :=
begin
  haveI : char_zero F := char_zero_of_inj_zero
    (λ n hn, by rwa [←(algebra_map F ℝ).injective.eq_iff, ring_hom.map_nat_cast,
      ring_hom.map_zero, nat.cast_eq_zero] at hn ),
  by_cases hp : p = 0,
  { simp_rw [hp, derivative_zero, root_set_zero, set.empty_card'],
    exact zero_le_one },
  by_cases hp' : p.derivative = 0,
  { rw eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_derivative_eq_zero hp'),
    simp_rw [root_set_def, map_C, roots_C, multiset.to_finset_zero, finset.coe_empty,
      set.empty_card', zero_le] },
  simp_rw [root_set_def, fintype.card_coe],
  refine tada_aux (λ x y hx hy hxy, _),
  rw [←finset.mem_coe, ←root_set_def, mem_root_set hp] at hx hy,
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero (λ x : ℝ, aeval x p) hxy
    p.continuous_aeval.continuous_on (hx.trans hy.symm),
  refine ⟨z, _, hz1⟩,
  rw [←finset.mem_coe, ←root_set_def, mem_root_set hp', ←hz2],
  simp_rw [aeval_def, ←eval_map, ←derivative_map],
  exact (p.map (algebra_map F ℝ)).deriv.symm,
end

lemma real_roots_poly (a : ℕ) (b : ℤ) (hab : abs b < a) :
  fintype.card ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).root_set ℝ) = 3 :=
begin
  apply le_antisymm,
  { rw [←one_mul (X ^ 5), ←C_1],
    refine (tada _).trans (nat.succ_le_succ ((tada _).trans (nat.succ_le_succ _))),
    simp_rw [derivative_add, derivative_sub, derivative_C_mul_X_pow, derivative_C_mul,
      derivative_X, derivative_one, mul_zero, sub_zero, derivative_C, derivative_zero, add_zero],
    rw [fintype.card_le_one_iff_subsingleton, set.subsingleton_coe],
    rw (show C ((1 : ℚ) * ↑5 * ↑(5 - 1)) * X ^ (5 - 1 - 1) = C ↑20 * X ^ 3, by norm_num),
    suffices : (_ : polynomial ℚ).root_set ℝ = {0},
    { rw this,
      exact set.subsingleton_singleton },
    ext x,
    rw [set.mem_singleton_iff, mem_root_set, aeval_mul, aeval_C, ring_hom.map_nat_cast,
        aeval_X_pow, mul_eq_zero, pow_eq_zero_iff, or_iff_right_iff_imp],
    { exact λ h, false.elim (not_not_intro h (by norm_num)) },
    { exact zero_lt_three },
    { rw [mul_ne_zero_iff, ne, ne, C_eq_zero, pow_eq_zero_iff],
      { exact ⟨by norm_num, X_ne_zero⟩ },
      { exact zero_lt_three } } },
  { sorry },
end

lemma complex_roots_poly (a : ℕ) (b : ℤ) (h : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).separable) :
  fintype.card ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ).root_set ℂ) = 5 :=
begin
  simp_rw [root_set_def, fintype.card_coe],
  rw [multiset.to_finset_card_of_nodup, ←nat_degree_eq_card_roots, nat_degree_poly],
  { exact is_alg_closed.splits_codomain _ },
  { exact nodup_roots ((separable_map _).mpr h) },
end

local attribute [instance] splits_ℚ_ℂ

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
  { rw [real_roots_poly a b hab, complex_roots_poly a b q_irred.separable] },
end

theorem not_solvable_poly (x : ℂ) (a : ℕ) (b : ℤ) (p : ℕ) (hab : abs b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : ↑p ∣ b) (hp2b : ¬ (↑p ^ 2 ∣ b))
  (hx : aeval x (X ^ 5 - C ↑a * X + C ↑b : polynomial ℚ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  apply solvable_by_rad.is_solvable_contrapositive (irreducible_poly a b p hp hpa hpb hp2b) hx,
  introI h,
  have key := solvable_of_surjective (gal_poly a b p hab hp hpa hpb hp2b).2,
  sorry,
end

theorem not_solvable_poly' (x : ℂ) (hx : aeval x (X ^ 5 - 4 * X + 2 : polynomial ℚ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  apply not_solvable_poly x 4 2 2,
  { norm_num },
  { norm_num },
  { norm_num },
  { norm_num },
  { norm_num },
  { rw [C_eq_nat_cast, C_eq_int_cast, ←hx],
    norm_cast },
end
