import field_theory.abel_ruffini
import analysis.calculus.local_extr

open polynomial polynomial.gal

lemma tada_aux {α : Type*} [linear_order α] {s t : finset α}
  (h : ∀ x y ∈ s, x < y → ∃ z ∈ t, x < z ∧ z < y) : s.card ≤ t.card + 1 :=
begin
  have h0 : ∀ i : fin (s.card - 1), ↑i < (s.sort (≤)).length,
  { intro i,
    rw finset.length_sort,
    exact lt_of_lt_of_le i.2 s.card.pred_le },
  have h1 : ∀ i : fin (s.card - 1), ↑i + 1 < (s.sort (≤)).length,
  { intro i,
    rw [finset.length_sort, ←nat.lt_sub_right_iff_add_lt],
    exact i.2 },
  have p := λ i : fin (s.card - 1), h ((s.sort (≤)).nth_le i (h0 i))
    ((s.sort (≤)).nth_le (i + 1) (h1 i))
    ((finset.mem_sort (≤)).mp (list.nth_le_mem _ _ (h0 i)))
    ((finset.mem_sort (≤)).mp (list.nth_le_mem _ _ (h1 i)))
    (s.sort_sorted_lt.rel_nth_le_of_lt (h0 i) (h1 i) (nat.lt_succ_self i)),
  let f : fin (s.card - 1) → (t : set α) :=
  λ i, ⟨classical.some (p i), (exists_prop.mp (classical.some_spec (p i))).1⟩,
  have hf : ∀ i j : fin (s.card - 1), i < j → f i < f j :=
  λ i j hij, subtype.coe_lt_coe.mp ((exists_prop.mp (classical.some_spec (p i))).2.2.trans
    (lt_of_le_of_lt ((s.sort_sorted (≤)).rel_nth_le_of_le (h1 i) (h0 j) (nat.succ_le_iff.mpr hij))
    (exists_prop.mp (classical.some_spec (p j))).2.1)),
  have key := fintype.card_le_of_embedding (function.embedding.mk f (λ i j hij, le_antisymm
    (not_lt.mp (mt (hf j i) (not_lt.mpr (le_of_eq hij))))
    (not_lt.mp (mt (hf i j) (not_lt.mpr (ge_of_eq hij)))))),
  rwa [fintype.card_fin, fintype.card_coe, nat.sub_le_right_iff_le_add] at key,
end

lemma tada {F : Type*} [field F] [algebra F ℝ] (p : polynomial F) :
  fintype.card (p.root_set ℝ) ≤ fintype.card (p.derivative.root_set ℝ) + 1 :=
begin
  haveI : char_zero F := char_zero_of_inj_zero
    (λ n hn, by rwa [←(algebra_map F ℝ).injective.eq_iff, ring_hom.map_nat_cast,
      ring_hom.map_zero, nat.cast_eq_zero] at hn),
  by_cases hp : p = 0,
  { simp_rw [hp, derivative_zero, root_set_zero, set.empty_card', zero_le_one] },
  by_cases hp' : p.derivative = 0,
  { rw eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_derivative_eq_zero hp'),
    simp_rw [root_set_C, set.empty_card', zero_le] },
  simp_rw [root_set_def, fintype.card_coe],
  refine tada_aux (λ x y hx hy hxy, _),
  rw [←finset.mem_coe, ←root_set_def, mem_root_set hp] at hx hy,
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero (λ x : ℝ, aeval x p) hxy
    p.continuous_aeval.continuous_on (hx.trans hy.symm),
  refine ⟨z, _, hz1⟩,
  rw [←finset.mem_coe, ←root_set_def, mem_root_set hp', ←hz2],
  simp_rw [aeval_def, ←eval_map, polynomial.deriv, derivative_map],
end

local attribute [instance] splits_ℚ_ℂ

lemma nat_degree_polynomial (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).nat_degree = 5 :=
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

lemma degree_polynomial (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).degree = ↑5 :=
(degree_eq_iff_nat_degree_eq_of_pos (nat.zero_lt_bit1 2)).mpr (nat_degree_polynomial a b)

lemma monic_polynomial (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).leading_coeff = 1 :=
by rw [leading_coeff, nat_degree_polynomial, coeff_add, coeff_sub, coeff_X_pow_self, coeff_C,
  if_neg ((nat.zero_ne_bit1 2).symm), add_zero, ←pow_one (X : polynomial ℤ), coeff_C_mul_X,
  if_neg (nat.one_ne_bit1 two_ne_zero).symm, sub_zero]

lemma primitive_polynomial (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).is_primitive :=
polynomial.monic.is_primitive (monic_polynomial a b)

lemma irreducible_polynomial (a b p : ℕ) (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b)
  (hp2b : ¬ (p ^ 2 ∣ b)) :
  irreducible (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ) :=
begin
  let q := (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ),
  apply irreducible_of_eisenstein_criterion,
  { rwa [ideal.span_singleton_prime (int.coe_nat_ne_zero.mpr hp.ne_zero),
      int.prime_iff_nat_abs_prime] },
  { rw [monic_polynomial, ideal.mem_span_singleton, ←int.coe_nat_one, int.coe_nat_dvd, nat.dvd_one],
    exact hp.ne_one },
  { intros n hn,
    rw ideal.mem_span_singleton,
    rw [degree_polynomial, with_bot.coe_lt_coe] at hn,
    interval_cases n with hn,
    all_goals { rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] },
    all_goals { norm_num },
    { exact int.coe_nat_dvd.mpr hpb },
    { exact int.coe_nat_dvd.mpr hpa } },
  { rw [degree_polynomial, ←with_bot.coe_zero, with_bot.coe_lt_coe],
    norm_num },
  { rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C],
    norm_num,
    rwa [pow_two, ideal.span_singleton_mul_span_singleton, ←pow_two, ideal.mem_span_singleton,
      ←int.coe_nat_pow, int.coe_nat_dvd] },
  { exact primitive_polynomial a b },
end

lemma irreducible_polynomial' (a b p : ℕ) (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b)
  (hp2b : ¬ (p ^ 2 ∣ b)) :
  irreducible ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (int.cast_ring_hom ℚ)) :=
begin
  let q := (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ),
  have q_nat_degree : q.nat_degree = 5,
  { exact nat_degree_polynomial a b },
  have q_degree : q.degree = ↑5,
  { exact (degree_eq_iff_nat_degree_eq_of_pos (nat.zero_lt_bit1 2)).mpr q_nat_degree },
  have q_monic : q.leading_coeff = 1,
  { rw [leading_coeff, q_nat_degree, coeff_add, coeff_sub, coeff_X_pow_self, coeff_C,
        if_neg ((nat.zero_ne_bit1 2).symm), add_zero, ←pow_one (X : polynomial ℤ), coeff_C_mul_X,
        if_neg (nat.one_ne_bit1 two_ne_zero).symm, sub_zero] },
  have q_primitive : q.is_primitive,
  { exact polynomial.monic.is_primitive q_monic },
  rw ← is_primitive.int.irreducible_iff_irreducible_map_cast q_primitive,
  exact irreducible_polynomial a b p hp hpa hpb hp2b,
end

lemma real_roots_polynomial_le (a b : ℕ) :
  fintype.card (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).root_set ℝ) ≤ 3 :=
begin
  rw [←one_mul (X ^ 5), ←C_1],
  refine (tada _).trans (nat.succ_le_succ ((tada _).trans (nat.succ_le_succ _))),
  rw [derivative_map, derivative_map, derivative_add, derivative_add, derivative_sub,
      derivative_sub, derivative_C_mul_X_pow, derivative_C_mul_X_pow, derivative_C_mul,
      derivative_C_mul, derivative_X, derivative_one, mul_zero, sub_zero, derivative_C,
      derivative_zero, add_zero, map_mul, map_pow, map_C, map_X,
      fintype.card_le_one_iff_subsingleton, set.subsingleton_coe, root_set_C_mul_X_pow],
  { exact set.subsingleton_singleton },
  { exact ne_of_gt zero_lt_three },
  { norm_num },
end

lemma real_roots_polynomial_ge (a b : ℕ) (hab : b < a) :
  2 ≤ fintype.card (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).root_set ℝ) :=
begin
  let q := (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ),
  have q_ne_zero : q ≠ 0,
  { sorry },
  let f : ℝ → ℝ := λ x, aeval x q,
  suffices : ∃ x y : ℝ, x ≠ y ∧ f x = 0 ∧ f y = 0,
  { obtain ⟨x, y, hxy, hx, hy⟩ := this,
    have key : ↑({x, y} : finset ℝ) ⊆ q.root_set ℝ,
    { rw [finset.coe_insert, finset.coe_singleton, set.insert_subset, set.singleton_subset_iff],
      exact ⟨by rwa mem_root_set q_ne_zero, by rwa mem_root_set q_ne_zero⟩ },
    replace key := fintype.card_le_of_embedding (set.embedding_of_subset _ _ key),
    rwa [fintype.card_coe, finset.card_insert_of_not_mem, finset.card_singleton] at key,
    rwa finset.mem_singleton },
  have f_cont : continuous f := polynomial.continuous_aeval _,
  have f_def : ∀ x : ℝ, f x = x ^ 5 - a * x + b := by simp [f],
  have hx : f 0 ≥ 0,
  { sorry },
  have hy : f (1 : ℝ) ≤ 0,
  { sorry },
  have hz : f a ≥ 0,
  { sorry },
  sorry,
end

lemma complex_roots_polynomial (a b : ℕ)
  (h : ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).separable) :
  fintype.card (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).root_set ℂ) = 5 :=
begin
  simp_rw [root_set_def, fintype.card_coe],
  rw [multiset.to_finset_card_of_nodup, splits_iff_card_roots.mp _,
      nat_degree_map', nat_degree_map', nat_degree_polynomial],
  { exact (algebra_map ℤ ℚ).injective_iff.mpr
      (λ a ha, int.cast_inj.mp (ha.trans ((algebra_map ℤ ℚ).map_zero).symm)) },--injective
  { exact (algebra_map ℚ ℂ).injective },
  { exact is_alg_closed.splits_codomain _ },
  { exact nodup_roots h.map },
end

lemma gal_polynomial (a b : ℕ) (hab : b < a)
  (q_irred : irreducible (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ))
  (q_irred' : irreducible ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ))) :
  function.bijective
    (gal_action_hom (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ))) ℂ) :=
begin
  apply gal_action_hom_bijective_of_prime_degree' q_irred',
  { rw [nat_degree_map', nat_degree_polynomial],
    norm_num,
    exact (algebra_map ℤ ℚ).injective_iff.mpr
      (λ a ha, int.cast_inj.mp (ha.trans ((algebra_map ℤ ℚ).map_zero).symm)) },--injective
  { rw [complex_roots_polynomial a b q_irred'.separable, nat.succ_le_succ_iff],
    exact (real_roots_polynomial_le a b).trans (nat.le_succ 3) },
  { simp_rw [complex_roots_polynomial a b q_irred'.separable, nat.succ_le_succ_iff],
    exact real_roots_polynomial_ge a b hab },
end

theorem not_solvable_poly_aux (x : ℂ) (a b p : ℕ) (hab : b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬ (p ^ 2 ∣ b))
  (hx : aeval x (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  let q := (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ),
  have q_irred : irreducible q,
  { exact irreducible_polynomial a b p hp hpa hpb hp2b },
  let r := q.map (algebra_map ℤ ℚ),
  have r_irred : irreducible r,
  { exact irreducible_polynomial' a b p hp hpa hpb hp2b },
  have r_aeval : aeval x r = 0,
  { rwa [aeval_map] },
  apply solvable_by_rad.is_solvable_contrapositive r_irred r_aeval,
  introI h,
  refine equiv.perm.not_solvable _ (le_of_eq _)
    (solvable_of_surjective (gal_polynomial a b hab q_irred r_irred).2),
  rw [cardinal.fintype_card, complex_roots_polynomial a b r_irred.separable],
  rw [nat.cast_bit1, nat.cast_bit0, nat.cast_one],
end

theorem not_solvable_poly (x : ℂ) (a : ℕ) (b : ℤ) (p : ℕ) (hab : abs b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : ↑p ∣ b) (hp2b : ¬ (↑p ^ 2 ∣ b))
  (hx : aeval x (X ^ 5 - C ↑a * X + C b : polynomial ℤ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  let y := x * b.sign,
  suffices : ¬ is_solvable_by_rad ℚ y,
  { exact λ h, this (is_solvable_by_rad.mul x b.sign h ((congr_arg (is_solvable_by_rad ℚ)
      (ring_hom.map_int_cast (algebra_map ℚ ℂ) b.sign)).mp (is_solvable_by_rad.base b.sign))) },
  refine not_solvable_poly_aux y a b.nat_abs p _ hp hpa _ _ _,
  { rwa [←int.coe_nat_lt, ←int.abs_eq_nat_abs] },
  { rwa [←int.coe_nat_dvd, int.dvd_nat_abs] },
  { rwa [←int.coe_nat_dvd, int.dvd_nat_abs, int.coe_nat_pow] },
  { rw [aeval_add, alg_hom.map_sub, aeval_mul, aeval_C, aeval_C, aeval_X, aeval_X_pow] at hx ⊢,
    rw [←int.mul_sign, mul_pow, ←mul_assoc, ring_hom.map_mul, ring_hom.eq_int_cast _ b.sign],
    suffices : (b.sign : ℂ) ^ 5 = b.sign,
    { rw [this, ←sub_mul, ←add_mul, hx, zero_mul] },
    sorry },
end

theorem not_solvable_poly' (x : ℂ) (hx : aeval x (X ^ 5 - 4 * X + 2 : polynomial ℤ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  apply not_solvable_poly x 4 2 2,
  { norm_num },
  { norm_num },
  { norm_num },
  { norm_num },
  { norm_num },
  { rw ← hx,
    simp },
end
