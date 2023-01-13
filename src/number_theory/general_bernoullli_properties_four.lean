import number_theory.general_bernoullli_number_properties_three

variables {p d : nat} (m : nat) [fact (0 < d)] [fact (nat.prime p)]
  {R : Type*} [normed_comm_ring R] {s : ℕ} {ψ : dirichlet_character R s}

open_locale big_operators
open filter dirichlet_character ring_hom

variables (p d R)
lemma helper_12 [algebra ℚ R] {k : ℕ} (hk : 1 < k) (x y : ℕ) :
  (algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k) * (algebra_map ℚ R)
  (polynomial.eval (↑(y.succ) / ↑(d * p ^ x : ℕ)) (polynomial.bernoulli k)) =
  ((y + 1 : ℕ) : R)^k + ((algebra_map ℚ R) (bernoulli 1 * (k : ℚ))) * ((d * p^x : ℕ) : R) *
  ((y + 1 : ℕ) : R)^k.pred + (d * p^x : ℕ) * (∑ (x_1 : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  (((y + 1 : ℕ) : ℚ) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred)) :=
begin
  rw [←(algebra_map ℚ R).map_mul, polynomial.bernoulli_def, polynomial.eval_finset_sum,
    finset.mul_sum],
  simp only [polynomial.eval_monomial, div_pow, nat.cast_succ],
  simp_rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _, mul_assoc],
  rw [finset.sum_range_succ_comm, div_mul_cancel _],
  { rw (algebra_map ℚ R).map_add,
    conv_lhs { congr, skip, rw ← nat.succ_pred_eq_of_pos (pos_of_gt hk),
      rw finset.sum_range_succ_comm, },
    rw [div_mul_comm, (algebra_map ℚ R).map_add, add_assoc],
    congr,
    { simp only [nat.choose_self, map_nat_cast, one_mul, map_add, nat.sub_self, bernoulli_zero,
        map_pow, map_one, nat.cast_one], },
    { rw [nat.choose_succ_self_right, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos (pos_of_gt hk),
        nat.pred_eq_sub_one, div_eq_mul_inv,
        ←pow_sub₀ ((d * p^x : ℕ) : ℚ) (nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0)) (nat.sub_le k 1)],
      rw [nat.sub_sub_self (le_of_lt hk), pow_one, ←mul_assoc, (algebra_map ℚ R).map_mul],
      simp only [map_nat_cast, map_add, map_pow, map_one, map_mul], },
    { rw [map_sum, pow_succ'],
      conv_lhs { apply_congr, skip, rw [←mul_assoc, ←mul_assoc, ←mul_assoc,
        (algebra_map ℚ R).map_mul], },
      rw [←finset.sum_mul, mul_comm, map_nat_cast],
      conv_rhs { congr, skip, apply_congr, skip, rw [←mul_assoc, ←mul_assoc], }, }, },
  { norm_cast,
    refine pow_ne_zero _ (nat.ne_zero_of_lt' 0), },
end

variables {p d R}
lemma helper_13 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R]
  (m : ℕ) [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hψ₁ : ψ.conductor ∣ d * p^m) (hψ₂ : ψ.is_primitive)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  (λ (n : ℕ), (1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (i : ℕ) in finset.range (d * p ^ n),
  (asso_dirichlet_character ψ) ↑i * ↑i ^ k - general_bernoulli_number ψ k) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character ψ) ↑(x_1.succ) * ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x) *
  ↑(1 + x_1) ^ (k - 1)) + (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred, (asso_dirichlet_character ψ) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) • ((asso_dirichlet_character ψ.asso_primitive_character)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k))))) :=
begin
  rw [eventually_eq, eventually_at_top],
  refine ⟨m, λ x hx, _⟩,
  have h1 : d * p^m ∣ d * p^x := (nat.mul_dvd_mul_iff_left (fact.out _)).2 (pow_dvd_pow _ hx),
  have poss : 0 < d * p^x := fact.out _,
  have ne_zero : ((d * p^x : ℕ) : ℚ) ≠ 0 := nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
  have coe_sub : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ),
  { change int.of_nat k - 1 = int.of_nat (k - 1),
    rw [int.of_nat_sub (le_of_lt hk), int.of_nat_one], },
  have : ∀ x : ℕ, asso_dirichlet_character ψ.asso_primitive_character x =
    asso_dirichlet_character ψ x := asso_dirichlet_character_equiv _ _ hψ₂,
  have f1 : ψ.asso_primitive_character.conductor = ψ.conductor,
  { rw mul_eq_asso_pri_char, },
  have f2 : ∀ (a : ℕ) (x : R), (1 / a : ℚ) • x = (1 / a : ℚ_[p]) • x,
  { intros a x, rw ←is_scalar_tower.algebra_map_smul ℚ_[p] (1 / a : ℚ) x, congr,
    simp only [one_div], rw ring_hom.map_inv, rw map_nat_cast, },
  rw general_bernoulli_number.eq_sum_bernoulli_of_conductor_dvd _ k (dvd_trans hψ₁ h1),
  conv_lhs { conv { congr, skip, rw [coe_sub, zpow_coe_nat, ← one_mul
    ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ (k - 1))), ← (algebra_map ℚ R).map_one,
    ←one_div_mul_cancel ne_zero, (algebra_map ℚ R).map_mul, mul_assoc _ _ ((algebra_map ℚ R)
    (((d * p ^ x : ℕ) : ℚ) ^ (k - 1))), ←(algebra_map ℚ R).map_mul, ←pow_succ,
    nat.sub_add_cancel (le_of_lt hk), mul_assoc, algebra.algebra_map_eq_smul_one, smul_mul_assoc,
    one_mul, finset.mul_sum],
    congr, skip, apply_congr, skip,
    rw [mul_comm ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k)) _, mul_assoc,
      mul_comm _ ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k))], },
    rw finset.range_eq_Ico,
    conv { rw [finset.sum_eq_sum_Ico_succ_bot poss, nat.cast_zero, nat.cast_zero,
      zero_pow (pos_of_gt hk), mul_zero, zero_add, ←nat.sub_add_cancel (nat.succ_le_iff.2 poss),
      ←finset.sum_Ico_add, finset.sum_Ico_succ_top (nat.zero_le _) _, ←finset.range_eq_Ico,
      ←nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos poss], }, },
  conv { congr, conv { congr, skip, congr, skip, congr, conv { apply_congr, skip,
    rw [nat.pred_add_one_eq_self poss, helper_12 p d R hk x _, add_assoc, mul_add, this _,
      add_comm _ 1],
    conv { congr, congr, rw [nat.succ_eq_add_one, add_comm x_1 1], }, }, }, },
  rw [finset.sum_add_distrib, f2, ←smul_sub, ←sub_sub, ←sub_sub, sub_self, zero_sub, ←neg_add',
    smul_neg, nat.pred_add_one_eq_self poss, ←smul_add, ←smul_add],
  congr,
  simp_rw mul_add, rw finset.sum_add_distrib,
  congr,
end

lemma lim_even_character' [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] {k : ℕ}
  [algebra ℚ R] [norm_one_class R] [fact (0 < m)] (hk : 1 < k) (hp : 2 < p)
  (hψ₁ : ψ.conductor ∣ d * p^m) (hψ₂ : ψ.is_primitive)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ n, (1/((d * p^n : ℕ) : ℚ_[p])) • ∑ i in finset.range (d * p^n),
  ((asso_dirichlet_character ψ) i * i^k) ) (@filter.at_top ℕ _)
  (nhds (general_bernoulli_number ψ k)) :=
begin
  rw ←tendsto_sub_nhds_zero_iff,
  apply (filter.tendsto_congr' (helper_13 m hk hψ₁ hψ₂ na)).2 _,
  conv { congr, skip, skip, rw ←neg_zero, rw ←add_zero (0 : R),
    conv { congr, congr, congr, rw ←add_zero (0 : R), }, },
  apply tendsto.neg,
  refine tendsto.add (tendsto.add _ _) _,
  sorry,
  sorry,
  { apply (tendsto_congr' _).2 tendsto_const_nhds,
    rw [eventually_eq, eventually_at_top],
    refine ⟨m, λ x hx, _⟩,
    rw asso_dirichlet_character_eq_zero _ _,
    sorry,
    { apply not_is_unit_of_not_is_unit_dvd _ (dvd_trans (conductor_dvd ψ) _),
      rw hψ, },
    have f1 : (asso_dirichlet_character ψ.asso_primitive_character) ↑(d * p ^ x) = 0,
    { rw asso_dirichlet_character_eq_zero _ _, },
    sorry, },
end
