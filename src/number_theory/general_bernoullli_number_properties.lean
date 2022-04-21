import number_theory.spl_value
import number_theory.weight_space -- to make zmod a topo space, not needed ow

variables (d p m : nat) [fact (0 < d)] [fact (nat.prime p)] {n : ℕ}
  {R : Type*} [normed_comm_ring R] (χ : dirichlet_character R (d * p^m))

open_locale big_operators
local attribute [instance] zmod.topological_space

instance (α : Type*) [topological_space α] [discrete_topology α] : discrete_topology αᵒᵖ :=
discrete_topology_induced opposite.unop_injective

lemma embed_product_injective (α : Type*) [monoid α] :
  function.injective (embed_product α) :=
λ a₁ a₂ h, by { rw embed_product at h,
simp only [prod.mk.inj_iff, opposite.op_inj_iff, monoid_hom.coe_mk] at h, rw [units.ext_iff, h.1], }

/-- Lke disc_top_units but includes k = 0. -/
lemma disc_top_units' (k : ℕ) : discrete_topology (units (zmod k)) :=
begin
  convert @discrete_topology_induced _ _ _ _ _ (embed_product_injective _),
  apply @prod.discrete_topology _ _ infer_instance infer_instance infer_instance infer_instance,
  { apply_instance, },
  { apply_instance, },
end

open dirichlet_character

lemma dirichlet_character.continuous {R : Type*} [monoid R] [topological_space R]
  {n : ℕ} (χ : dirichlet_character R n) : continuous χ :=
begin
  convert continuous_of_discrete_topology,
  exact disc_top_units' _,
end

lemma dirichlet_character.asso_dirichlet_character_continuous
  {R : Type*} [monoid_with_zero R] [topological_space R] {n : ℕ} (χ : dirichlet_character R n) :
  continuous (asso_dirichlet_character χ) :=
begin
  convert continuous_of_discrete_topology,
  apply_instance,
end

/-lemma dirichlet_character.bounded
  {R : Type*} [monoid R] [normed_group R] {n : ℕ} [fact (0 < n)]
  (χ : dirichlet_character R n) : ∃ M : ℝ,
  ∥ ( ⟨χ, dirichlet_character.continuous χ⟩ : C(units (zmod n), units R)) ∥ < M := -/

lemma dirichlet_character.asso_dirichlet_character_bounded
  {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ} [fact (0 < n)]
  (χ : dirichlet_character R n) : ∃ M : ℝ,
  ∥ (⟨asso_dirichlet_character χ,
    dirichlet_character.asso_dirichlet_character_continuous χ⟩ : C(zmod n, R)) ∥ < M :=
begin
  refine ⟨(⨆ i : zmod n, ∥asso_dirichlet_character χ i∥) + 1, _⟩,
  apply lt_of_le_of_lt _ (lt_add_one _),
  { convert le_refl _, rw continuous_map.norm_eq_supr_norm,
    simp only [continuous_map.coe_mk], },
  { apply_instance, },
end

lemma dirichlet_character.mul_eval_coprime {R : Type*} [comm_monoid_with_zero R]
  {n m : ℕ} [fact (0 < n)] (χ : dirichlet_character R n) (ψ : dirichlet_character R m)
  {a : ℤ} (ha : is_coprime a (m * n)) :
  asso_dirichlet_character (dirichlet_character.mul χ ψ) a =
  asso_dirichlet_character χ a * (asso_dirichlet_character ψ a) :=
begin
  rw mul,
  have h1 := factors_through_spec _ (factors_through_conductor (χ.mul ψ)),
  rw ←change_level_asso_dirichlet_character_eq'
    (χ.change_level _ * ψ.change_level _).asso_primitive_character _ _,
  rw asso_primitive_character,
  rw asso_dirichlet_character_eq_char' _,
  sorry
end

lemma dirichlet_character.asso_dirichlet_character_eval_mul_sub
  {R : Type*} [monoid_with_zero R] {n : ℕ} (χ : dirichlet_character R n) (k x : ℕ) :
  asso_dirichlet_character χ (k * n - x) = asso_dirichlet_character χ (-1) *
  (asso_dirichlet_character χ x) :=
by { rw [zmod.nat_cast_self, mul_zero, zero_sub, neg_eq_neg_one_mul, monoid_hom.map_mul], }

lemma dirichlet_character.asso_dirichlet_character_eval_mul_sub'
  {R : Type*} [monoid_with_zero R] {n k : ℕ} (χ : dirichlet_character R n) (hk : n ∣ k) (x : ℕ) :
  asso_dirichlet_character χ (k - x) = asso_dirichlet_character χ (-1) *
  (asso_dirichlet_character χ x) :=
by { have : (k : zmod n) = 0,
      { rw [←zmod.nat_cast_mod, nat.mod_eq_zero_of_dvd hk, nat.cast_zero], },
      rw [this, zero_sub, neg_eq_neg_one_mul, monoid_hom.map_mul], }

abbreviation lev {R : Type*} [monoid R] {n : ℕ} (χ : dirichlet_character R n) : ℕ := n

lemma dirichlet_character.lev_mul_dvd {R : Type*} [comm_monoid_with_zero R] {n k : ℕ}
  (χ : dirichlet_character R n) (ψ : dirichlet_character R k) :
  lev (mul χ ψ) ∣ lcm n k := dvd_trans (conductor_dvd _) dvd_rfl

/-lemma dirichlet_character.asso_dirichlet_character_pow {R : Type*} [monoid_with_zero R] {n k : ℕ}
  (χ : dirichlet_character R n) :
  asso_dirichlet_character (χ^k) = (asso_dirichlet_character χ)^k := sorry-/

lemma nat.add_sub_pred (n : ℕ) : n + (n - 1) = 2 * n - 1 := sorry

instance : has_pow (dirichlet_character R n) ℕ := monoid.has_pow

lemma teichmuller_character_mod_p_change_level_pow (k : ℕ)
  (χ : dirichlet_character R n) (a : units (zmod n)) :
  ((χ: monoid_hom (units (zmod n)) (units R))^k) a = (χ a)^k :=
begin
  exact eq.refl ((χ ^ k) a),
end

lemma teichmuller_character.is_odd_or_is_even :
  (((teichmuller_character p)) (-1 : units (ℤ_[p])) ) = -1 ∨
  (((teichmuller_character p)) (-1 : units (ℤ_[p])) ) = 1 :=
begin
  suffices : ((teichmuller_character p) (-1))^2 = 1,
  { conv_rhs at this { rw ←one_pow 2 },
    rw ←sub_eq_zero at this,
    rw [sq_sub_sq, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this,
    cases this,
    { left, rw this, },
    { right,
      simp only [this, units.coe_one], }, },
  { rw [←monoid_hom.map_pow, ←monoid_hom.map_one (teichmuller_character p)],
    congr, rw units.ext_iff,
    simp only [units.coe_one, units.coe_neg_one, nat.neg_one_sq, units.coe_pow], },
end

lemma teichmuller_character_mod_p_eval_neg_one --[no_zero_divisors R] [semi_normed_algebra ℚ_[p] R]
  (hp : 2 < p) : (((teichmuller_character_mod_p p)) (-1) ) = -1 :=
begin
  cases is_odd_or_is_even (teichmuller_character_mod_p p),
  { exact h, },
  { rw [is_even, ←monoid_hom.map_one (teichmuller_character_mod_p p)] at h,
    have := teichmuller_character_mod_p_injective p,
    specialize this h,
    rw [eq_comm, ←units.eq_iff, units.coe_one, units.coe_neg_one, eq_neg_iff_add_eq_zero,
     ←nat.cast_one, ←nat.cast_add, zmod.nat_coe_zmod_eq_zero_iff_dvd,
     nat.dvd_prime (nat.prime_two)] at this,
    exfalso, cases this,
    { apply nat.prime.ne_one (fact.out _) this, },
    { apply ne_of_lt hp this.symm, }, },
end

lemma neg_one_pow_eq_neg_one (hp : 2 < p) : (-1 : units R)^(p - 2) = -1 :=
begin
  rw ←units.eq_iff,
  simp only [units.coe_neg_one, units.coe_pow],
  rw neg_one_pow_eq_pow_mod_two,
  cases nat.prime.eq_two_or_odd _,
  swap 4, { apply fact.out _, assumption, },
  { exfalso, apply ne_of_gt hp h, },
  { have : (p - 2) % 2 = 1,
    { rw [←nat.mod_eq_sub_mod (le_of_lt hp), h], },
    rw [this, pow_one], },
end

lemma teichmuller_character_mod_p_change_level_eval_neg_one --[normed_comm_ring R]
  [no_zero_divisors R] [semi_normed_algebra ℚ_[p] R]
  (hinj : function.injective (algebra_map ℚ_[p] R)) [fact (0 < m)] (hp : 2 < p) (k : ℕ) :
  (((teichmuller_character_mod_p_change_level p d R m)) (-1 : units (zmod (d * p^m))) ) =
  (-1 : units R) :=
begin
  cases is_odd_or_is_even (teichmuller_character_mod_p_change_level p d R m),
  { exact h, },
  { exfalso,
    have := teichmuller_character_mod_p_injective p,
    rw is_even at h,
    delta teichmuller_character_mod_p_change_level at h,
    rw change_level at h,
    simp only [ring_hom.to_monoid_hom_eq_coe, function.comp_app, monoid_hom.coe_comp] at h,
    suffices : ((units.map ↑((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom)).comp
      (teichmuller_character_mod_p p) ^ (p - 2)) (-1) = 1,
    swap, convert h,
    { rw units.map,
      simp only [one_inv, monoid_hom.mk'_apply, ring_hom.coe_monoid_hom, units.coe_neg_one,
        units.val_eq_coe, units.inv_eq_coe_inv, zmod.cast_hom_apply, units.neg_inv],
      have : ((-1 : zmod (d * p^m)) : zmod p) = -1,
      { rw zmod.cast_neg _,
        swap 3, { apply zmod.char_p _, },
        rw zmod.cast_one _,
        swap, { apply zmod.char_p _, },
        any_goals { apply dvd_mul_of_dvd_right (dvd_pow dvd_rfl
            (ne_zero_of_lt _)) _, exact 0, apply fact.out, }, },
      simp_rw [this], tauto, },
    rw teichmuller_character_mod_p_change_level_pow at this,
    rw monoid_hom.comp_apply at this,
    rw teichmuller_character_mod_p_eval_neg_one p hp at this,
    suffices neg_one_pow : (-1 : units R)^(p - 2) = 1,
    { haveI : char_zero R := (ring_hom.char_zero_iff hinj).1 infer_instance,
      apply @nat.cast_add_one_ne_zero R _ _ _ 1,
      rw neg_one_pow_eq_neg_one p hp at neg_one_pow,
      rw ←eq_neg_iff_add_eq_zero, rw nat.cast_one,
      rw ←units.eq_iff at neg_one_pow, rw units.coe_one at neg_one_pow,
      rw units.coe_neg_one at neg_one_pow, rw neg_one_pow, },
    { convert this, rw units.map,
      rw ←units.eq_iff,
      simp, }, },
end

#exit
lemma sum_eq_neg_sum_add_dvd (hχ : χ.is_even) [semi_normed_algebra ℚ_[p] R] [fact (0 < n)]
  [fact (0 < m)] (k : ℕ) (hk : 1 ≤ k) :
  ∑ (i : ℕ) in finset.range (d * p ^ m).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i * ↑i ^ (k - 1) =
  -1 * ∑ (x : ℕ) in finset.range (d * p ^ m + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑x *
  ↑x ^ (k - 1) + ↑(d * p ^ m) * ∑ (x : ℕ) in finset.range (d * p ^ m + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑x *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ m) ^ x_1 * ((-1) * ↑x) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p_change_level
  p d R m ^ k)) ∣ d * p^m,
  { convert dirichlet_character.lev_mul_dvd _ _, rw [lcm_eq_nat_lcm, nat.lcm_self], },
  conv_lhs { rw ←finset.sum_flip, apply_congr, skip, rw nat.cast_sub (finset.mem_range_succ_iff.1 H),
    rw dirichlet_character.asso_dirichlet_character_eval_mul_sub' _ lev_mul_dvd,
    conv { congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H), sub_eq_add_neg,
    add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
    nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
    congr, skip, apply_congr, skip, rw pow_succ, rw mul_assoc ↑(d * p^m) _,
    rw mul_assoc ↑(d * p^m) _, },
    rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^m) _,
      mul_comm _ ↑(d * p^m), mul_assoc ↑(d * p^m) _ _], },
  rw finset.sum_add_distrib, rw ←finset.mul_sum, rw ←finset.mul_sum,
  apply congr_arg2 _ (congr_arg2 _ _ rfl) rfl,
  rw ←int.cast_one, rw ←int.cast_neg,
  rw dirichlet_character.mul_eval_coprime _ _ (is_coprime.neg_left is_coprime_one_left),
  rw int.cast_neg, rw int.cast_one,
  rw asso_even_dirichlet_character_eval_neg_one _ hχ, rw one_mul,
  rw asso_dirichlet_character_eq_char' _ (is_unit.neg (is_unit_one)),
  convert_to (-1 : R)^k * (-1)^(k -1) = -1,
  { apply congr_arg2 _ _ rfl,
    sorry, },
  { rw ←pow_add, rw nat.add_sub_pred, rw nat.neg_one_pow_of_odd _, rw nat.odd_iff, sorry, },
end

lemma sum_odd_char [semi_normed_algebra ℚ_[p] R] [fact (0 < n)] [fact (0 < m)] (k : ℕ) :
  ∃ y, ∑ i in finset.range (d * p^m), ((asso_dirichlet_character (dirichlet_character.mul χ
    ((teichmuller_character_mod_p_change_level p d R m)^k))) i * i^(k - 1)) =
    (d * p^m) * y ∧ ∥y∥ ≤ 1 :=
begin
  have f1 : ∑ (i : ℕ) in finset.range (d * p ^ m),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R
    m ^ k))) ↑i * ↑i ^ (k - 1) =
  ∑ (i : ℕ) in finset.range (d * p ^ m).succ, (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i * ↑i ^ (k - 1)
   - ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑(d * p^m) *
  ↑(d * p^m) ^ (k - 1)),
  { rw [finset.sum_range_succ, add_sub_cancel], },
  rw f1,
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p_change_level
    p d R m ^ k)) ∣ d * p^m, sorry,
  have f2 : ∑ (i : ℕ) in
  finset.range (d * p ^ m).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i * ↑i ^ (k - 1) =
  - ∑ (i : ℕ) in finset.range (d * p ^ m).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i * ↑i ^ (k - 1),
  have : ∑ (i : ℕ) in finset.range (d * p ^ m).succ,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R
  m ^ k))) ↑i * ↑i ^ (k - 1) = (-1)^k * ∑ (i : ℕ) in finset.range (d * p ^ m).succ,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R
  m ^ k))) ↑i * ↑(d * p^m - i) ^ (k - 1),
  { rw ←finset.sum_flip,
    conv_lhs { apply_congr, skip, rw nat.cast_sub (finset.mem_range_succ_iff.1 H),
      rw dirichlet_character.asso_dirichlet_character_eval_mul_sub' _ lev_mul_dvd,
      conv { congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H), sub_eq_add_neg,
      add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
      nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
      congr, skip, apply_congr, skip, rw pow_succ, rw mul_assoc ↑(d * p^m) _,
      rw mul_assoc ↑(d * p^m) _, },
      rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^m) _,
       mul_comm _ ↑(d * p^m), mul_assoc ↑(d * p^m) _ _], }, --conv { congr, skip, congr, skip, rw ←finset.mul_sum, }, },
    rw finset.sum_add_distrib, rw ←finset.mul_sum, rw ←finset.mul_sum,
    sorry, },
  sorry,
end

lemma sum_odd_character [semi_normed_algebra ℚ_[p] R] [fact (0 < n)] (k : ℕ) :
  filter.tendsto (λ m, ∑ i in finset.range (d * p^m), ((asso_dirichlet_character
  (dirichlet_character.mul χ ((teichmuller_character_mod_p_change_level p d R (d * p^m))^k)))
  i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0) :=
begin
  rw metric.tendsto_at_top,
  intros ε hε,
  refine ⟨_, λ x hx, _⟩,
  swap,
  rw dist_eq_norm, rw sub_zero,
  cases sum_odd_char d p m χ k,
  sorry,
  sorry,
  sorry,
  sorry,
end
