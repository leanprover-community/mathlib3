import number_theory.general_bernoullli_number_properties_two
import number_theory.bernoulli_polynomials
import number_theory.general_bernoullli_number

variables {p d : nat} (m : nat) [fact (0 < d)] [fact (nat.prime p)]
  {R : Type*} [normed_comm_ring R] {χ : dirichlet_character R (d * p^m)}

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

lemma div_smul_eq_div_smul [algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] (a : ℕ)
  (x : R) : (1 / a : ℚ) • x = (1 / a : ℚ_[p]) • x :=
begin
  rw ←is_scalar_tower.algebra_map_smul ℚ_[p] (1 / a : ℚ) x,
  congr,
  simp only [one_div],
  rw [ring_hom.map_inv, map_nat_cast],
end

lemma helper_14 [algebra ℚ R] [algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R] (a : ℚ) (r : R) :
  a • r = (algebra_map ℚ ℚ_[p]) a • r := by { simp }

variables {p d R}

lemma mul_eq_asso_pri_char {n : ℕ} (χ : dirichlet_character R n) :
  χ.asso_primitive_character.conductor = χ.conductor :=
(is_primitive_def χ.asso_primitive_character).1 (asso_primitive_character_is_primitive χ)

lemma nat.pred_add_one_eq_self {n : ℕ} (hn : 0 < n) : n.pred + 1 = n := nat.succ_pred_eq_of_pos hn

lemma asso_dirichlet_character_equiv {S : Type*} [comm_monoid_with_zero S]
  (ψ : dirichlet_character S m) (h : is_primitive ψ) (a : ℕ) :
  asso_dirichlet_character ψ.asso_primitive_character a = asso_dirichlet_character ψ a :=
begin
  by_cases h' : is_unit (a : zmod m),
  { conv_rhs { rw factors_through_spec ψ (factors_through_conductor ψ), },
    rw change_level_asso_dirichlet_character_eq' _ _ h',
    apply congr,
    { congr, },
    { rw zmod.cast_nat_cast _,
      swap, { refine zmod.char_p _, },
      { apply conductor_dvd _, }, }, },
  { repeat { rw asso_dirichlet_character_eq_zero, },
    { assumption, },
    rw (is_primitive_def _).1 h, apply h', },
end

-- note that this works for any dirichlet character which is primitive and whose conductor divides d * p^m
lemma helper_13 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) : (λ (n : ℕ), (1 / ((d * p ^ n : ℕ) : ℚ_[p])) •
  ∑ (i : ℕ) in finset.range (d * p ^ n), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R^k))) ↑i * ↑i ^ k - general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p' p R ^ k)) k) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(x_1.succ) *
  ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x) * ↑(1 + x_1) ^ (k - 1)) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k))))) :=
begin
  rw [eventually_eq, eventually_at_top],
  refine ⟨m, λ x hx, _⟩,
  have h1 : lcm (d * p^m) p ∣ d * p^x := (@helper_4 p d _ _ m _).symm ▸ (nat.mul_dvd_mul_iff_left (fact.out _)).2 (pow_dvd_pow _ hx),
  have poss : 0 < d * p^x := fact.out _,
  have ne_zero : ((d * p^x : ℕ) : ℚ) ≠ 0 := nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
  have coe_sub : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ),
  { change int.of_nat k - 1 = int.of_nat (k - 1),
    rw [int.of_nat_sub (le_of_lt hk), int.of_nat_one], },
  have : ∀ x : ℕ, asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character x =
    asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k)) x :=
  asso_dirichlet_character_equiv _ _ (is_primitive_mul _ _),
  have f1 : (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character.conductor =
    (χ.mul (teichmuller_character_mod_p' p R ^ k)).conductor,
  { rw mul_eq_asso_pri_char, },
  rw general_bernoulli_number.eq_sum_bernoulli_of_conductor_dvd _ k (dvd_trans (conductor_dvd _)
    (dvd_trans (conductor_dvd _) h1)),
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
  rw [finset.sum_add_distrib, div_smul_eq_div_smul p R, ←smul_sub, ←sub_sub, ←sub_sub, sub_self,
    zero_sub, ←neg_add', smul_neg, nat.pred_add_one_eq_self poss, ←smul_add, ←smul_add],
  congr,
  simp_rw mul_add, rw finset.sum_add_distrib,
  congr,
end

variables (p d R)
lemma norm_mul_pow_pos' [nontrivial R] [algebra ℚ_[p] R] (x : ℕ) : 0 < ∥((d * p^x : ℕ) : R)∥ :=
norm_pos_iff.2 (nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0))

lemma norm_le_one' [normed_algebra ℚ_[p] R][norm_one_class R] (n : ℕ) : ∥(n : R)∥ ≤ 1 :=
begin
  rw norm_coe_nat_eq_norm_ring_hom_map p,
  apply padic_int.norm_le_one,
end

lemma nat_cast_mul_prime_pow_tendsto_zero [normed_algebra ℚ_[p] R] [norm_one_class R] :
  tendsto (λ x : nat, ((d * p^x : nat) : R)) at_top (nhds 0) :=
begin
  have : |(1 / p : ℝ)| < 1,
  { rw [←inv_eq_one_div, ←padic_norm_e.norm_p, abs_norm_eq_norm],
    apply padic_norm_e.norm_p_lt_one, },
  have f1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 this,
  conv at f1 { congr, funext, rw [pow_zero, one_mul, ←inv_eq_one_div, ←zpow_coe_nat, inv_zpow,
    ←zpow_neg, ←padic_int.norm_p_pow], },
  conv { congr, funext, rw nat.cast_mul, skip, skip, rw ←mul_zero (d : R), },
  refine tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.2 _),
  convert f1,
  ext,
  rw [←nat.cast_pow, norm_coe_nat_eq_norm_ring_hom_map p R],
  simp,
end

variables {p d R}
lemma helper_15 [nontrivial R] [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (x y : ℕ) : ∥(∑ (x_1 : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  (((y + 1 : ℕ) : ℚ) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred))∥ ≤
  ∥((d * p^x : ℕ) : R)∥ * (⨆ (x_1 : zmod k.pred), (∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
  ↑(k.pred.succ.choose x_1.val) )∥)) :=
begin
  have le : k.pred = k.pred - 1 + 1,
  { rw [nat.sub_add_cancel _, nat.pred_eq_sub_one], apply nat.le_pred_of_lt hk, },
  haveI : fact (0 < k.pred) := fact_iff.2 (nat.lt_pred_iff.2 hk),
  refine le_trans (na _ _) (csupr_le (λ z, _)),
  conv { congr, congr, find (↑(d * p ^ x) ^ k.pred) { rw [le, pow_add, pow_one], },
    rw [←mul_assoc, (algebra_map ℚ R).map_mul, mul_assoc _ _ (↑(d * p ^ x) ^ (k.pred - 1)),
      div_mul_comm], },
  rw mul_comm,
  apply le_trans (norm_mul_le _ _) _,
  rw [←mul_one_div, ←inv_eq_one_div, ←pow_sub₀ ((d * p^x : ℕ) : ℚ)
    (nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0)) (nat.le_pred_of_lt (zmod.val_lt z)),
    ring_hom.map_mul, ←nat.cast_pow, ←nat.cast_pow, ←nat.cast_mul, map_nat_cast,
    mul_le_mul_left (norm_mul_pow_pos' p d R x), map_nat_cast],
  refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul le_rfl (norm_le_one' p R _)
    (norm_nonneg _) (norm_nonneg _)) _),
  rw mul_one,
  refine le_cSup (set.finite.bdd_above (set.finite_range _)) ⟨z, _⟩,
  simp only,
end

lemma lim_even_character' [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]
  [fact (0 < m)] {k : ℕ} [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [norm_one_class R] (hk : 1 < k)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ n, (1/((d * p^n : ℕ) : ℚ_[p])) • ∑ i in finset.range (d * p^n),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) i * i^k) )
  (@filter.at_top ℕ _) (nhds (general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p' p R ^ k)) k)) :=
begin
  refine tendsto_sub_nhds_zero_iff.1 ((filter.tendsto_congr' (helper_13 m hk)).2 _),
  conv { congr, skip, skip, rw ←neg_zero, rw ←add_zero (0 : R),
    conv { congr, congr, congr, rw ←add_zero (0 : R), }, },
  refine tendsto.neg (tendsto.add (tendsto.add _ _) _),
  { conv { congr, funext, conv { congr, skip, apply_congr, skip,
      rw [mul_comm ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x)) _, ←mul_assoc], },
      rw [←finset.sum_mul, mul_comm _ ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x)),
       ←smul_mul_assoc, mul_comm ((algebra_map ℚ R) (bernoulli 1 * ↑k)) ↑(d * p ^ x),
       ←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _,
       one_div_smul_self R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ←smul_eq_mul,
       algebra_map_smul, helper_14 p R], skip, skip,
       rw ←@smul_zero ℚ_[p] R _ _ _ ((algebra_map ℚ ℚ_[p]) (bernoulli 1 * ↑k)), },
    refine tendsto.const_smul _ _,
    convert (tendsto_congr' _).2 (sum_even_character m hk hχ hp na),
    rw [eventually_eq, eventually_at_top],
    refine ⟨m, λ x hx, _⟩,
    have poss : 0 < d * p^x := fact.out _,
    simp_rw [add_comm 1 _, nat.succ_eq_add_one],
    rw [finset.range_eq_Ico, finset.sum_Ico_add' (λ x : ℕ, (asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p' p R ^ k))) ↑x * ↑x ^ (k - 1)) 0 (d * p^x).pred 1,
      finset.sum_eq_sum_Ico_succ_bot poss, @nat.cast_zero R _ _, zero_pow (nat.sub_pos_of_lt hk),
      mul_zero, zero_add, zero_add, nat.pred_add_one_eq_self poss], },
  { rw metric.tendsto_at_top,
    intros ε hε,
    obtain ⟨N, h⟩ := metric.tendsto_at_top.1 (tendsto.const_mul ((⨆ (x_1 : zmod (k.sub 0).pred),
      ∥(algebra_map ℚ R) (bernoulli ((k.sub 0).pred.succ - x_1.val) *
      ↑((k.sub 0).pred.succ.choose x_1.val))∥) *
      (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) (tendsto_iff_norm_tendsto_zero.1
      (nat_cast_mul_prime_pow_tendsto_zero p d R))) (ε/2) (half_pos hε),
    simp_rw [sub_zero, mul_zero _, dist_zero_right _, real.norm_eq_abs] at h,
    refine ⟨N, λ  x hx, _⟩,
    rw dist_eq_norm, rw sub_zero,
    conv { congr, congr, conv { congr, skip,
      conv { apply_congr, skip, rw [←mul_assoc, mul_comm ((asso_dirichlet_character (χ.mul
        (teichmuller_character_mod_p' p R ^ k))) ↑(x_1.succ)) _, mul_assoc, add_comm 1 x_1], },
      rw ←finset.mul_sum, },
      rw [←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _, one_div_smul_self R
        (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul], },
    refine lt_of_le_of_lt (na _ _) (lt_of_le_of_lt (cSup_le (set.range_nonempty _) (λ b hb, _))
      (half_lt_self hε)),
    cases hb with y hy,
    rw ←hy,
    simp only,
    refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul
      (le_of_lt (dirichlet_character.lt_bound _ _)) (helper_15 na hk _ _) (norm_nonneg _)
      (le_of_lt (bound_pos _))) (le_of_lt _)),
    rw [mul_comm, mul_assoc, mul_comm],
    apply lt_of_abs_lt (h x hx),  },
  { apply (tendsto_congr' _).2 tendsto_const_nhds,
    rw [eventually_eq, eventually_at_top],
    refine ⟨m, λ x hx, _⟩,
    -- there is another way to do this, but we will use this later on anyway
    rw asso_dirichlet_character_eq_zero _ _,
    { rw [zero_mul, smul_zero], },
    { -- probably make this a separate lemma
      convert not_is_unit_zero,
      sorry,
      sorry, }, },
end
