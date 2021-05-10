/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import field_theory.abel_ruffini
import analysis.calculus.local_extr
/-!
Construction of an algebraic number that is not solvable by radicals.

The main ingredients are:
 * `solvable_by_rad.is_solvable'` in `field_theory/abel_ruffini` :
  an irreducible polynomial with an `is_solvable_by_rad` root has solvable Galois group
 * `gal_action_hom_bijective_of_prime_degree'` in `field_theory/polynomial_galois_group` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group
 * `equiv.perm.not_solvable` in `group_theory/solvable` : the symmetric group is not solvable

Then all that remains is the construction of a specific polynomial satisfying the conditions of
  `gal_action_hom_bijective_of_prime_degree'`, which is done in this file.

-/

open polynomial polynomial.gal

local attribute [instance] splits_ℚ_ℂ

lemma nat_degree_poly (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).nat_degree = 5 :=
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

lemma degree_poly (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).degree = ↑5 :=
(degree_eq_iff_nat_degree_eq_of_pos (nat.zero_lt_bit1 2)).mpr (nat_degree_poly a b)

lemma monic_poly (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).leading_coeff = 1 :=
by rw [leading_coeff, nat_degree_poly, coeff_add, coeff_sub, coeff_X_pow_self, coeff_C,
  if_neg ((nat.zero_ne_bit1 2).symm), add_zero, ←pow_one (X : polynomial ℤ), coeff_C_mul_X,
  if_neg (nat.one_ne_bit1 two_ne_zero).symm, sub_zero]

lemma primitive_poly (a b : ℕ) : (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).is_primitive :=
polynomial.monic.is_primitive (monic_poly a b)

lemma irreducible_poly (a b p : ℕ) (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b)
  (hp2b : ¬ (p ^ 2 ∣ b)) :
  irreducible (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ) :=
begin
  apply irreducible_of_eisenstein_criterion,
  { rwa [ideal.span_singleton_prime (int.coe_nat_ne_zero.mpr hp.ne_zero),
      int.prime_iff_nat_abs_prime] },
  { rw [monic_poly, ideal.mem_span_singleton, ←int.coe_nat_one, int.coe_nat_dvd, nat.dvd_one],
    exact hp.ne_one },
  { intros n hn,
    rw ideal.mem_span_singleton,
    rw [degree_poly, with_bot.coe_lt_coe] at hn,
    interval_cases n with hn,
    all_goals { rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] },
    all_goals { norm_num },
    { exact int.coe_nat_dvd.mpr hpb },
    { exact int.coe_nat_dvd.mpr hpa } },
  { rw [degree_poly, ←with_bot.coe_zero, with_bot.coe_lt_coe],
    norm_num },
  { rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C],
    norm_num,
    rwa [pow_two, ideal.span_singleton_mul_span_singleton, ←pow_two, ideal.mem_span_singleton,
      ←int.coe_nat_pow, int.coe_nat_dvd] },
  { exact primitive_poly a b },
end

lemma irreducible_poly' (a b p : ℕ) (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b)
  (hp2b : ¬ (p ^ 2 ∣ b)) :
  irreducible ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (int.cast_ring_hom ℚ)) :=
(is_primitive.int.irreducible_iff_irreducible_map_cast (polynomial.monic.is_primitive
  (monic_poly a b))).mp (irreducible_poly a b p hp hpa hpb hp2b)

lemma real_roots_poly_le (a b : ℕ) :
  fintype.card (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).root_set ℝ) ≤ 3 :=
begin
  rw [←one_mul (X ^ 5), ←C_1],
  refine (card_root_set_le_derivative _).trans
    (nat.succ_le_succ ((card_root_set_le_derivative _).trans (nat.succ_le_succ _))),
  rw [derivative_map, derivative_map, derivative_add, derivative_add, derivative_sub,
      derivative_sub, derivative_C_mul_X_pow, derivative_C_mul_X_pow, derivative_C_mul,
      derivative_C_mul, derivative_X, derivative_one, mul_zero, sub_zero, derivative_C,
      derivative_zero, add_zero, map_mul, map_pow, map_C, map_X,
      fintype.card_le_one_iff_subsingleton, set.subsingleton_coe, root_set_C_mul_X_pow],
  { exact set.subsingleton_singleton },
  { exact ne_of_gt zero_lt_three },
  { norm_num },
end

lemma real_roots_poly_ge_aux' (a b : ℕ) (hab : b < a) : a ^ 2 + b ≤ a ^ 5 :=
begin
  refine le_trans ((nat.add_le_add_iff_le_right 1 _ _).mp _) (nat.pow_le_pow_of_le_right
    (nat.one_le_of_lt hab) (bit1_le_bit1.mpr one_le_two)),
  rw [add_assoc],
  apply (add_le_add (le_refl (a ^ 2)) (nat.succ_le_iff.mpr hab)).trans,
  suffices : ∀ c : ℤ, 0 ≤ c → c ^ 2 + c ≤ c ^ 3 + 1,
  { specialize this a (int.coe_nat_nonneg a),
    norm_cast at this,
    exact this },
  intros c hc,
  rw [←sub_nonneg, show c ^ 3 + 1 - (c ^ 2 + c) = (c - 1) ^ 2 * (c + 1), by ring],
  exact mul_nonneg (pow_two_nonneg _) (add_nonneg hc zero_le_one),
end

lemma real_roots_poly_ge_aux (a b : ℕ) (hab : b < a) (f : ℝ → ℝ) (f_cont : continuous f)
  (f_def : ∀ x : ℝ, f x = x ^ 5 - a * x + b) : ∃ x y : ℝ, x ≠ y ∧ f x = 0 ∧ f y = 0 :=
begin
  have h0 : f 0 ≥ 0,
  { rw [f_def, zero_pow (nat.zero_lt_bit1 2), mul_zero, sub_zero, zero_add],
    exact nat.cast_nonneg b },
  by_cases hb : b + 1 < a,
  { have h1 : f 1 < 0,
    { rw [f_def, one_pow, mul_one, add_comm, add_sub, sub_lt_zero],
      norm_cast,
      exact hb },
    have ha : f a ≥ 0,
    { rw [f_def, ←pow_two],
      exact add_nonneg (sub_nonneg.mpr (pow_le_pow (nat.one_le_cast.mpr (nat.one_le_of_lt hab))
        (nat.bit0_le_bit1_iff.mpr one_le_two))) (nat.cast_nonneg b) },
    obtain ⟨x, hx1, hx2⟩ := intermediate_value_Ico' (show (0 : ℝ) ≤ 1, from zero_le_one)
      f_cont.continuous_on (set.mem_Ioc.mpr ⟨h1, h0⟩),
    obtain ⟨y, hy1, hy2⟩ := intermediate_value_Ioc (show (1 : ℝ) ≤ a, from nat.one_le_cast.mpr
      (nat.one_le_of_lt hab)) f_cont.continuous_on (set.mem_Ioc.mpr ⟨h1, ha⟩),
    exact ⟨x, y, ne_of_lt (hx1.2.trans hy1.1), hx2, hy2⟩ },
  { replace hb : a = b + 1 := le_antisymm (not_lt.mp hb) (nat.succ_le_iff.mpr hab),
    have hy2 : f 1 = 0,
    { rw [f_def, one_pow, mul_one, add_comm, add_sub, sub_eq_zero],
      norm_cast,
      exact hb.symm },
    have ha : f (-a) ≤ 0,
    { rw [f_def, neg_pow_bit1, ←neg_mul_eq_mul_neg, sub_neg_eq_add, ←pow_two, add_assoc,
          neg_add_eq_sub, sub_nonpos],
      norm_cast,
      exact real_roots_poly_ge_aux' a b hab },
    obtain ⟨x, hx1, hx2⟩ := intermediate_value_Icc (show -(a : ℝ) ≤ 0, from neg_nonpos.mpr
      (nat.cast_nonneg a)) f_cont.continuous_on (set.mem_Icc.mpr ⟨ha, h0⟩),
    exact ⟨x, 1, ne_of_lt (lt_of_le_of_lt hx1.2 zero_lt_one), hx2, hy2⟩ },
end

lemma real_roots_poly_ge (a b : ℕ) (hab : b < a) :
  2 ≤ fintype.card (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).root_set ℝ) :=
begin
  let q := (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ),
  have q_ne_zero : q ≠ 0 := map_monic_ne_zero (monic_poly a b),
  let f : ℝ → ℝ := λ x, aeval x q,
  have f_cont : continuous f := polynomial.continuous_aeval _,
  have f_def : ∀ x : ℝ, f x = x ^ 5 - a * x + b := by simp [f],
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_poly_ge_aux a b hab f f_cont f_def,
  have key : ↑({x, y} : finset ℝ) ⊆ q.root_set ℝ,
  { rw [finset.coe_insert, finset.coe_singleton, set.insert_subset, set.singleton_subset_iff],
    exact ⟨by rwa mem_root_set q_ne_zero, by rwa mem_root_set q_ne_zero⟩ },
  replace key := fintype.card_le_of_embedding (set.embedding_of_subset _ _ key),
  rwa [fintype.card_coe, finset.card_insert_of_not_mem, finset.card_singleton] at key,
  rwa finset.mem_singleton,
end

lemma complex_roots_poly (a b : ℕ)
  (h : ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).separable) :
  fintype.card (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ)).root_set ℂ) = 5 :=
begin
  simp_rw [root_set_def, fintype.card_coe],
  rw [multiset.to_finset_card_of_nodup, splits_iff_card_roots.mp _,
      nat_degree_map', nat_degree_map', nat_degree_poly],
  { exact (algebra_map ℤ ℚ).injective_iff.mpr
      (λ a ha, int.cast_inj.mp (ha.trans ((algebra_map ℤ ℚ).map_zero).symm)) },
  { exact (algebra_map ℚ ℂ).injective },
  { exact is_alg_closed.splits_codomain _ },
  { exact nodup_roots h.map },
end

lemma gal_poly (a b : ℕ) (hab : b < a)
  (q_irred : irreducible (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ))
  (q_irred' : irreducible ((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ))) :
  function.bijective
    (gal_action_hom (((X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ).map (algebra_map ℤ ℚ))) ℂ) :=
begin
  apply gal_action_hom_bijective_of_prime_degree' q_irred',
  { rw [nat_degree_map', nat_degree_poly],
    norm_num,
    exact (algebra_map ℤ ℚ).injective_iff.mpr
      (λ a ha, int.cast_inj.mp (ha.trans ((algebra_map ℤ ℚ).map_zero).symm)) },
  { rw [complex_roots_poly a b q_irred'.separable, nat.succ_le_succ_iff],
    exact (real_roots_poly_le a b).trans (nat.le_succ 3) },
  { simp_rw [complex_roots_poly a b q_irred'.separable, nat.succ_le_succ_iff],
    exact real_roots_poly_ge a b hab },
end

theorem not_solvable_poly (x : ℂ) (a b p : ℕ) (hab : b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬ (p ^ 2 ∣ b))
  (hx : aeval x (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  let q := (X ^ 5 - C ↑a * X + C ↑b : polynomial ℤ),
  have q_irred : irreducible q,
  { exact irreducible_poly a b p hp hpa hpb hp2b },
  let r := q.map (algebra_map ℤ ℚ),
  have r_irred : irreducible r,
  { exact irreducible_poly' a b p hp hpa hpb hp2b },
  have r_aeval : aeval x r = 0,
  { rwa [aeval_map] },
  apply mt (solvable_by_rad.is_solvable' r_irred r_aeval),
  introI h,
  refine equiv.perm.not_solvable _ (le_of_eq _)
    (solvable_of_surjective (gal_poly a b hab q_irred r_irred).2),
  rw [cardinal.fintype_card, complex_roots_poly a b r_irred.separable],
  rw [nat.cast_bit1, nat.cast_bit0, nat.cast_one],
end

/-- Generalization of `not_solvable_poly` to allow a negative constant term -/
theorem not_solvable_poly' (x : ℂ) (a : ℕ) (b : ℤ) (p : ℕ) (hab : abs b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : ↑p ∣ b) (hp2b : ¬ (↑p ^ 2 ∣ b))
  (hx : aeval x (X ^ 5 - C ↑a * X + C b : polynomial ℤ) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
begin
  let y := x * b.sign,
  suffices : ¬ is_solvable_by_rad ℚ y,
  { exact λ h, this (is_solvable_by_rad.mul x b.sign h ((congr_arg (is_solvable_by_rad ℚ)
      (ring_hom.map_int_cast (algebra_map ℚ ℂ) b.sign)).mp (is_solvable_by_rad.base b.sign))) },
  refine not_solvable_poly y a b.nat_abs p _ hp hpa _ _ _,
  { rwa [←int.coe_nat_lt, ←int.abs_eq_nat_abs] },
  { rwa [←int.coe_nat_dvd, int.dvd_nat_abs] },
  { rwa [←int.coe_nat_dvd, int.dvd_nat_abs, int.coe_nat_pow] },
  { rw [aeval_add, alg_hom.map_sub, aeval_mul, aeval_C, aeval_C, aeval_X, aeval_X_pow] at hx ⊢,
    rw [←int.mul_sign, mul_pow, ←mul_assoc, ring_hom.map_mul, ring_hom.eq_int_cast _ b.sign],
    rw [←int.cast_pow, int.sign_pow_bit1, ←sub_mul, ←add_mul, hx, zero_mul] },
end

theorem not_solvable_poly'' (x : ℂ) (hx : aeval x (X ^ 5 - 4 * X + 2 : polynomial ℤ) = 0) :
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

theorem exists_not_solvable_by_rad : ∃ x : ℂ, is_algebraic ℚ x ∧ ¬ is_solvable_by_rad ℚ x :=
begin
  let p : polynomial ℤ := X ^ 5 - 4 * X + 2,
  have hp : (p.map (algebra_map ℤ ℚ)).nat_degree ≠ 0,
  { intro h,
    have key := congr_arg (eval 1) (eq_C_of_nat_degree_eq_zero h),
    simp_rw [coeff_zero_eq_eval_zero, eval_C, eval_map, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_bit0, eval₂_one] at key,
    norm_num at key },
  obtain ⟨x, hx⟩ := exists_root_of_splits (algebra_map ℚ ℂ)
    (is_alg_closed.splits_codomain (p.map (algebra_map ℤ ℚ))) _,
  refine ⟨x, ⟨p.map (algebra_map ℤ ℚ), _, hx⟩, _⟩,
  { exact λ h, hp ((congr_arg nat_degree h).trans nat_degree_zero) },
  { exact not_solvable_poly'' x (by rwa [eval₂_map, ←is_scalar_tower.algebra_map_eq] at hx) },
  { exact hp ∘ nat_degree_eq_of_degree_eq_some },
end
