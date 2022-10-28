import number_theory.dirichlet_character_properties
import number_theory.teich_char

lemma units.coe_map_of_dvd {a b : ℕ} (h : a ∣ b) (x : units (zmod b)) :
  is_unit (x : zmod a) :=
begin
  change is_unit ((x : zmod b) : zmod a),
  rw ←zmod.cast_hom_apply (x : zmod b),
  swap 3, { refine zmod.char_p _, },
  swap, { apply h, },
  rw [←ring_hom.coe_monoid_hom, ←units.coe_map],
  apply units.is_unit,
end

lemma is_unit_of_is_coprime {a b : ℕ} (h : a ∣ b) {x : ℕ} (hx : is_coprime (x : ℤ) b) :
  is_unit (x : zmod a) :=
begin
  rw nat.is_coprime_iff_coprime at hx,
  set y := zmod.unit_of_coprime _ hx,
  convert_to is_unit ((y : zmod b) : zmod a),
  { rw ←zmod.cast_nat_cast h x, congr, refine zmod.char_p _, },
    { change is_unit (y : zmod a),
      apply units.coe_map_of_dvd h _, },
end

open dirichlet_character

lemma dirichlet_character.mul_eval_coprime {R : Type*} [comm_monoid_with_zero R]
  {n m : ℕ} [fact (0 < n)] (χ : dirichlet_character R n) (ψ : dirichlet_character R m)
  {a : ℕ} (ha : is_coprime (a : ℤ) ((n * m : ℕ) : ℤ)) :
  asso_dirichlet_character (dirichlet_character.mul χ ψ) a =
  asso_dirichlet_character χ a * (asso_dirichlet_character ψ a) :=
begin
  rw mul,
  have : ((a : zmod (lcm n m)) : zmod (χ.change_level (dvd_lcm_left n m) *
    ψ.change_level (dvd_lcm_right n m)).conductor) = a,
  { rw zmod.cast_nat_cast _ _,
    swap, { refine zmod.char_p _, },
    apply conductor_dvd, },
  rw ← this,
  have dvd : lcm n m ∣ n * m,
  { rw lcm_dvd_iff, refine ⟨(dvd_mul_right _ _), (dvd_mul_left _ _)⟩, },
  rw ←change_level_asso_dirichlet_character_eq' _ (conductor_dvd _) (is_unit_of_is_coprime dvd ha),
  { convert_to asso_dirichlet_character ((χ.change_level (dvd_lcm_left n m) *
      ψ.change_level (dvd_lcm_right n m))) (a : zmod (lcm n m)) = _,
    { delta asso_primitive_character,
      rw ← (factors_through_spec _ (factors_through_conductor (χ.change_level (dvd_lcm_left n m) *
        ψ.change_level (dvd_lcm_right n m)))), },
    rw asso_dirichlet_character_mul,
    rw monoid_hom.mul_apply, congr,
    { rw change_level_asso_dirichlet_character_eq' _ _ (is_unit_of_is_coprime dvd ha),
      { rw zmod.cast_nat_cast (dvd_lcm_left _ _),
        refine zmod.char_p _, }, },
    { rw change_level_asso_dirichlet_character_eq' _ _ (is_unit_of_is_coprime dvd ha),
      { rw zmod.cast_nat_cast (dvd_lcm_right _ _),
        refine zmod.char_p _, }, }, },
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

--lemma zmod.neg_one_eq_sub {n : ℕ} (hn : 0 < n) : ((n - 1 : ℕ) : zmod n) = ((-1 : ℤ) : zmod n) := sorry

lemma dirichlet_character.mul_eval_coprime' {R : Type*} [comm_monoid_with_zero R]
  {n m : ℕ} [fact (0 < n)] [fact (0 < m)] (χ : dirichlet_character R n)
  (ψ : dirichlet_character R m) :
  --{a : ℤ} (ha : is_coprime a ((n * m : ℕ) : ℤ)) :
  asso_dirichlet_character (dirichlet_character.mul χ ψ) (-1 : ℤ) =
  asso_dirichlet_character χ (-1) * (asso_dirichlet_character ψ (-1)) :=
begin
  have lev_dvd : lev (χ.mul ψ) ∣ n * m,
  { apply dvd_trans (conductor_dvd _) (lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)), },
  have one_le : 1 ≤ n * m,
  { rw nat.succ_le_iff, apply nat.mul_pos (fact.out _) (fact.out _),
    any_goals { assumption, }, },
  have f1 : ((-1 : ℤ) : zmod (lev (χ.mul ψ))) = ↑((n * m - 1) : ℕ),
  { rw nat.cast_sub one_le,
    rw ←zmod.nat_coe_zmod_eq_zero_iff_dvd at lev_dvd,
    rw lev_dvd,
    simp only [zero_sub, int.cast_one, nat.cast_one, int.cast_neg], },
  rw f1,
  rw dirichlet_character.mul_eval_coprime,
  have f2 : ((-1 : ℤ) : zmod n) = ↑((n * m - 1) : ℕ),
  { rw nat.cast_sub one_le,
    simp only [zero_sub, int.cast_one, zmod.nat_cast_self, nat.cast_one, nat.cast_mul,
      int.cast_neg, zero_mul], },
  have f3 : ((-1 : ℤ) : zmod m) = ↑((n * m - 1) : ℕ),
  { rw nat.cast_sub one_le,
    simp only [zero_sub, int.cast_one, zmod.nat_cast_self, nat.cast_one, nat.cast_mul,
      int.cast_neg, mul_zero], },
  rw ←f2, rw ←f3, congr, norm_cast, norm_cast,
  { rw nat.is_coprime_iff_coprime,
    by_contradiction,
    obtain ⟨p, h1, h2, h3⟩ := nat.prime.not_coprime_iff_dvd.1 h,
    rw ←zmod.nat_coe_zmod_eq_zero_iff_dvd at h2,
    rw ←zmod.nat_coe_zmod_eq_zero_iff_dvd at h3,
    rw nat.cast_sub _ at h2,
    { rw h3 at h2,
      rw zero_sub at h2,
      rw nat.cast_one at h2,
      rw neg_eq_zero at h2,
      haveI : nontrivial (zmod p), apply zmod.nontrivial _,
      { apply fact_iff.2 (nat.prime.one_lt h1), },
      { apply zero_ne_one h2.symm, }, },
    rw nat.succ_le_iff, apply nat.mul_pos (fact.out _) (fact.out _),
    any_goals { assumption, }, },
end
-- follows for all a : ℤ from this

lemma nat.add_sub_pred (n : ℕ) : n + (n - 1) = 2 * n - 1 :=
begin
  cases n,
  { refl, },
  { rw ←nat.add_sub_assoc (nat.succ_le_succ (nat.zero_le _)), rw nat.succ_mul, rw one_mul, },
end

variables (d p m : nat) [fact (0 < d)] [fact (nat.prime p)]
  {R : Type*} [normed_comm_ring R] (χ : dirichlet_character R (d * p^m))

instance {n : ℕ} : has_pow (dirichlet_character R n) ℕ := monoid.has_pow

lemma teichmuller_character_mod_p_change_level_pow {n : ℕ} (k : ℕ)
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
    simp only [units.coe_one, units.coe_neg_one, neg_one_sq, units.coe_pow], },
end

lemma teichmuller_character_mod_p_eval_neg_one --[no_zero_divisors R] [normed_algebra ℚ_[p] R]
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

example [normed_algebra ℚ_[p] R] [nontrivial R] : function.injective (algebra_map ℚ_[p] R) :=
(algebra_map ℚ_[p] R).injective

lemma teichmuller_character_mod_p_change_level_eval_neg_one
  [no_zero_divisors R] [normed_algebra ℚ_[p] R] [nontrivial R] (hp : (2 < p))
--  (hinj : function.injective (algebra_map ℚ_[p] R))
  [fact (0 < m)] :
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
      (teichmuller_character_mod_p p)⁻¹) (-1) = 1,
    swap, convert h,
    { rw units.map,
      simp only [monoid_hom.mk'_apply, ring_hom.coe_monoid_hom, units.coe_neg_one,
        units.val_eq_coe, units.inv_eq_coe_inv, zmod.cast_hom_apply, inv_neg', inv_one], -- units.neg_inv
      have : ((-1 : zmod (d * p^m)) : zmod p) = -1,
      { rw zmod.cast_neg _,
        swap 3, { apply zmod.char_p _, },
        rw zmod.cast_one _,
        swap, { apply zmod.char_p _, },
        any_goals { apply dvd_mul_of_dvd_right, apply dvd_pow dvd_rfl (ne_zero_of_lt _),
           exact 0, apply fact.out, }, },
      simp_rw [this], refl, },
    rw monoid_hom.comp_apply at this,
    simp only [monoid_hom.inv_apply, map_inv, inv_eq_one] at this,
    rw teichmuller_character_mod_p_eval_neg_one p hp at this,
    rw ← units.eq_iff at this,
    rw units.coe_map at this,
    simp only [units.coe_neg_one, ring_hom.coe_monoid_hom, map_neg, map_one, units.coe_one] at this,
    haveI : char_zero R := (ring_hom.char_zero_iff ((algebra_map ℚ_[p] R).injective)).1 infer_instance,
    apply @nat.cast_add_one_ne_zero R _ _ _ 1,
    rw ←eq_neg_iff_add_eq_zero, rw nat.cast_one, rw this, },
end
.

lemma teichmuller_character_mod_p_change_level_pow_eval_neg_one
  (k : ℕ) (hp : 2 < p) [normed_algebra ℚ_[p] R] [nontrivial R] [no_zero_divisors R]
  [fact (0 < m)] : ((teichmuller_character_mod_p_change_level p d R m ^ k) is_unit_one.neg.unit) =
  (-1) ^ k :=
begin
  convert_to ((teichmuller_character_mod_p_change_level p d R m) is_unit_one.neg.unit)^k = (-1) ^ k,
  congr',
  convert teichmuller_character_mod_p_change_level_eval_neg_one d p m hp using 1,
  { congr', rw [←units.eq_iff, is_unit.unit_spec],
    simp only [units.coe_neg_one], },
  any_goals { apply_instance, },
end

lemma nat.two_mul_sub_one_mod_two_eq_one {k : ℕ} (hk : 1 ≤ k) : (2 * k - 1) % 2 = 1 :=
begin
  have : 2 * k - 1 = 2 * k + 1 - 2,
  { norm_num, },
  rw this, rw ← nat.mod_eq_sub_mod _,
  { rw ←nat.odd_iff, refine ⟨k, rfl⟩, },
  { apply nat.succ_le_succ (one_le_mul one_le_two hk), },
end

open_locale big_operators
--set_option pp.proofs true
lemma sum_eq_neg_sum_add_dvd (hχ : χ.is_even) [normed_algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) (k : ℕ) (hk : 1 ≤ k) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i * ↑i ^ (k - 1) =
  -1 * ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑y *
  ↑y ^ (k - 1) + ↑(d * p ^ x) * ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑y *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p_change_level
  p d R m ^ k)) ∣ d * p^m,
  { convert dirichlet_character.lev_mul_dvd _ _, rw [lcm_eq_nat_lcm, nat.lcm_self], },
  rw ←finset.sum_flip,
  conv_lhs { apply_congr, skip, rw nat.cast_sub (finset.mem_range_succ_iff.1 H),
    rw dirichlet_character.asso_dirichlet_character_eval_mul_sub' _ (dvd_trans lev_mul_dvd
      (mul_dvd_mul dvd_rfl (pow_dvd_pow _ hx))),
    conv { congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H), sub_eq_add_neg,
    add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
    nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
    congr, skip, apply_congr, skip, rw pow_succ, rw mul_assoc ↑(d * p^x) _,
    rw mul_assoc ↑(d * p^x) _, },
    rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^x) _,
      mul_comm _ ↑(d * p^x), mul_assoc ↑(d * p^x) _ _], },
  rw finset.sum_add_distrib, rw ←finset.mul_sum, rw ←finset.mul_sum,
  apply congr_arg2 _ (congr_arg2 _ _ _) rfl,
--  apply congr_arg2 _ (congr_arg2 _ _ rfl) rfl,
  { rw ←int.cast_one, rw ←int.cast_neg,
  --rw ←zmod.neg_one_eq_sub _,
    rw dirichlet_character.mul_eval_coprime' _ _,
  --  rw zmod.neg_one_eq_sub _,
    --rw int.cast_neg, rw int.cast_one,
    rw asso_even_dirichlet_character_eval_neg_one _ hχ, rw one_mul,
    rw asso_dirichlet_character_eq_char' _ (is_unit.neg (is_unit_one)),
    convert_to (-1 : R)^k * (-1)^(k -1) = -1,
    { apply congr_arg2 _ _ rfl,
      rw teichmuller_character_mod_p_change_level_pow_eval_neg_one d p m k hp,
      simp only [units.coe_neg_one, units.coe_pow],
      any_goals { apply_instance, }, },
    { rw ←pow_add, rw nat.add_sub_pred, rw odd.neg_one_pow _, rw nat.odd_iff,
      rw nat.two_mul_sub_one_mod_two_eq_one hk, },
    any_goals { apply fact_iff.2 (mul_prime_pow_pos p d m), }, },
  { rw ←finset.sum_flip, },
end

lemma nat.pow_eq_mul_pow_sub (k : ℕ) (hk : 1 < k) :
  (d * p^m)^(k - 1) = (d * p^m) * (d * p^m)^(k - 2) :=
begin
  conv_rhs { congr, rw ←pow_one (d * p^m), },
  rw ←pow_add, congr, rw add_comm,
  conv_rhs { rw nat.sub_succ, rw ←nat.succ_eq_add_one,
    rw nat.succ_pred_eq_of_pos (lt_tsub_iff_right.2 _), skip,
    apply_congr hk, },
end

lemma asso_dc [normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ)
  (hχ : χ.change_level (dvd_lcm_left _ _) *
    (teichmuller_character_mod_p_change_level p d R m ^ k).change_level (dvd_lcm_right _ _) ≠ 1) :
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)))
  ↑(d * p ^ m) = 0 :=
begin
  have dvd : lev (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)) ∣ d * p^m,
  { convert dirichlet_character.lev_mul_dvd _ _,
    rw lcm_eq_nat_lcm, rw nat.lcm_self, },
  rw ←zmod.nat_coe_zmod_eq_zero_iff_dvd at dvd,
  rw dvd,
  rw asso_dirichlet_character_eq_zero _,
  simp only [is_unit_zero_iff],
  convert zero_ne_one,
  apply zmod.nontrivial _,
  apply fact_iff.2 _,
  rw nat.one_lt_iff_ne_zero_and_ne_one,
  refine ⟨λ h, _, λ h, _⟩,
  { rw conductor_eq_zero_iff_level_eq_zero at h, rw lcm_eq_nat_lcm at h,
    rw nat.lcm_self at h, apply ne_zero_of_lt (mul_prime_pow_pos p d m) h, },
  { rw ← conductor_eq_one_iff _ at h,
    apply hχ h,
    rw lcm_eq_nat_lcm, rw nat.lcm_self, apply (mul_prime_pow_pos p d m), },
end

--instance {R : Type*} [normed_comm_ring R] [normed_algebra ℚ_[p] R] : norm_one_class R :=
--by {fconstructor, convert normed_algebra.norm_one ℚ_[p] R, }

example {R : Type*} [comm_ring R] {a b c : R} : a * (b * c) = b * (a * c) := by refine mul_left_comm a b c

lemma norm_sum_le_smul {k : ℕ} [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] [norm_one_class R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {x : ℕ} (hx : m ≤ x) :
  ∥∑ (y : ℕ) in finset.range (d * p ^ x + 1), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ((-1) * ↑y) *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))∥ ≤ --(d * p ^ x + 1) •
    (dirichlet_character.bound
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)) * (k - 1)) :=
begin
  have : ∀ y ∈ finset.range (d * p ^ x + 1),
  ∥(asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)))
    ((-1) * ↑y) * ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^
    (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1)) ∥ ≤ (dirichlet_character.bound
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) * (k - 1),
  { intros l hl,
    apply le_trans (norm_mul_le _ _) _,
    --rw ← mul_one ((χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound),
    apply mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) _ (norm_nonneg _)
      (le_of_lt (dirichlet_character.bound_pos _)),
    { simp_rw [mul_pow], simp_rw [mul_left_comm], simp_rw [mul_assoc],
      apply le_trans (norm_sum_le _ _) _,
      have : ∀ a ∈ finset.range (k - 1), ∥(-1 : R) ^ (k - 1 - (a + 1)) * (↑(d * p ^ x) ^ a *
        (↑l ^ (k - 1 - (a + 1)) * ↑((k - 1).choose (a + 1))))∥ ≤ 1,
      { intros a ha,
        apply le_trans (norm_mul_le _ _) _,
        have : (((d * p ^ x) ^ a * (l ^ (k - 1 - (a + 1)) * (k - 1).choose (a + 1)) : ℕ) : R) =
          (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ((d * p ^ x) ^ a *
          (l ^ (k - 1 - (a + 1)) * (k - 1).choose (a + 1)) : ℤ_[p])),
        { simp only [map_nat_cast, ring_hom.map_pow, nat.cast_mul, nat.cast_pow,
            ring_hom.map_mul], },
        cases neg_one_pow_eq_or R (k - 1 - (a + 1)),
        { rw h, rw norm_one_class.norm_one, rw one_mul,
          rw ← nat.cast_pow, rw ← nat.cast_pow, rw ← nat.cast_mul, rw ← nat.cast_mul,
          rw this, rw norm_algebra_map,  rw norm_one_class.norm_one, --norm_algebra_map_eq,
          rw mul_one,
          apply padic_int.norm_le_one, },
        { rw h, rw norm_neg, rw norm_one_class.norm_one, rw one_mul,
          rw ← nat.cast_pow, rw ← nat.cast_pow, rw ← nat.cast_mul, rw ← nat.cast_mul,
          rw this, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one, --rw norm_algebra_map_eq,
          apply padic_int.norm_le_one, }, },
      { convert le_trans (finset.sum_le_sum this) _,
        rw finset.sum_const, rw finset.card_range, rw nat.smul_one_eq_coe,
        rw nat.cast_sub (le_of_lt hk), rw nat.cast_one, }, }, },
  { apply le_trans (na _ _) _,
    apply cSup_le _ (λ b hb, _),
    { apply set.range_nonempty _, simp only [nonempty_of_inhabited], },
    { cases hb with y hy,
      simp only at hy,
      rw ← hy,
      apply this y.val _,
      rw finset.mem_range,
      apply zmod.val_lt _, apply fact_iff.2 (nat.succ_pos _), }, },
/-    rw (csupr_le_iff' _),
    convert le_trans ((csupr_le_iff' _).2 this) _,
    apply le_trans (norm_sum_le _ _) _,
    convert le_trans (finset.sum_le_sum this) _,
    rw finset.sum_const,
    rw finset.card_range, }, -/
end

instance wut [nontrivial R] [normed_algebra ℚ_[p] R] : char_zero R :=
(ring_hom.char_zero_iff ((algebra_map ℚ_[p] R).injective)).1 infer_instance

lemma sum_odd_char [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
  --[fact (0 < n)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {x : ℕ} (hx : m ≤ x) :
  ∃ y, (2 : R) * ∑ i in finset.range (d * p^x), ((asso_dirichlet_character (dirichlet_character.mul χ
    ((teichmuller_character_mod_p_change_level p d R m)^k))) i * i^(k - 1)) =
    ↑(d * p^x) * y ∧ ∥y∥ ≤ --(d * p ^ x + 1) •
    ((χ.mul
    (teichmuller_character_mod_p_change_level p d R m ^ k)).bound * (↑k - 1)) +
    ∥(((d * p ^ x : ℕ) : R) ^ (k - 2)) * (1 + 1)∥ * (χ.mul
    (teichmuller_character_mod_p_change_level p d R m ^ k)).bound :=
begin
  have f1 : ∑ (i : ℕ) in finset.range (d * p ^ x),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R
    m ^ k))) ↑i * ↑i ^ (k - 1) =
  ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑i * ↑i ^ (k - 1)
   - ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑(d * p^x) *
  ↑(d * p^x) ^ (k - 1)),
  { rw [finset.sum_range_succ, add_sub_cancel], },
  rw f1,
  clear f1,
  rw mul_sub, rw mul_comm _ (↑(d * p ^ x) ^ (k - 1)),
  rw ←mul_assoc _ (↑(d * p ^ x) ^ (k - 1)) _, rw mul_comm _ (↑(d * p ^ x) ^ (k - 1)),
  rw mul_assoc _ (2 : R) _, rw ←nat.cast_pow,
  conv { congr, funext, rw sub_eq_iff_eq_add, rw nat.pow_eq_mul_pow_sub d p x k hk,
    rw nat.cast_mul (d * p^x) _, rw mul_assoc ↑(d * p^x) _ _,
    conv { congr, rw ←mul_add ↑(d * p^x) _ _, }, },
  have two_eq_one_add_one : (2 : R) = (1 : R) + (1 : R) := rfl,
  rw two_eq_one_add_one, rw add_mul, rw one_mul,
  conv { congr, funext, conv { congr, to_lhs, congr, skip,
    rw sum_eq_neg_sum_add_dvd d p m _ hχ hp k (le_of_lt hk) hx, }, },
  rw ←neg_eq_neg_one_mul, rw ←add_assoc, rw ←sub_eq_add_neg,
  conv { congr, funext, rw sub_self _, rw zero_add, },
  refine ⟨_, _, _⟩,
  { exact ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) (-1) *
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑y *
    ∑ (x_1 : ℕ) in finset.range (k - 1),
    ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1))) -
    ↑((d * p ^ x) ^ (k - 2)) * ((1 + 1) * (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑(d * p ^ x)), },
  { rw sub_add_cancel, },
  { apply le_trans (norm_sub_le _ _) _,
    conv { congr, congr, congr, apply_congr, skip, rw ← mul_assoc, rw ←monoid_hom.map_mul, },
    apply le_trans (add_le_add (norm_sum_le_smul d p m _ na hk hχ hp hx) (le_refl _)) _,
    rw ← mul_assoc,
    apply le_trans (add_le_add (le_refl _) (norm_mul_le _ _)) _,
    apply le_trans (add_le_add (le_refl _) ((mul_le_mul_left _).2
      (le_of_lt (dirichlet_character.lt_bound _ _)))) _,
    { rw lt_iff_le_and_ne,
      refine ⟨norm_nonneg _, λ h, _⟩,
      rw eq_comm at h, rw norm_eq_zero at h,
      rw mul_eq_zero at h, cases h,
      { rw nat.cast_eq_zero at h, apply pow_ne_zero _ _ h,
        apply ne_zero_of_lt (mul_prime_pow_pos p d _), },
      { rw ← eq_neg_iff_add_eq_zero at h,
        apply zero_ne_one ((self_eq_neg R R).1 h).symm, }, },
    { rw nat.cast_pow, }, },
end

lemma two_mul_eq_inv_two_smul [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]
  (a b : R) (h : (2 : R) * a = b) : a = (2 : ℚ_[p])⁻¹ • b :=
begin
  symmetry,
  rw inv_smul_eq_iff₀ _,
  { rw ← h,
    convert_to _ = ((algebra_map ℚ_[p] R) 2) * a,
    { rw [algebra.algebra_map_eq_smul_one, smul_mul_assoc, one_mul], },
    simp only [h, ring_hom.map_bit0, ring_hom.map_one], },
  { apply two_ne_zero', },
end

lemma coe_eq_ring_hom_map [normed_algebra ℚ_[p] R] (y : ℕ) :
  (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (y : ℤ_[p])) = ((y : ℕ) : R) :=
by { simp }

lemma norm_coe_eq_ring_hom_map [normed_algebra ℚ_[p] R]  [norm_one_class R] (y : ℕ) :
  ∥((y : ℕ) : R)∥ = ∥padic_int.coe.ring_hom (y : ℤ_[p])∥ :=
by { rw [← coe_eq_ring_hom_map p, norm_algebra_map, norm_one_class.norm_one, mul_one], }

lemma norm_mul_pow_le_one_div_pow [normed_algebra ℚ_[p] R] [norm_one_class R] (y : ℕ) :
  ∥((d * p^y : ℕ) : R)∥ ≤ 1 / p^y :=
begin
  rw nat.cast_mul,
  apply le_trans (norm_mul_le _ _) _,
  rw ← one_mul (1 / (p : ℝ)^y),
  apply mul_le_mul _ _ (norm_nonneg _) zero_le_one,
  { rw norm_coe_eq_ring_hom_map p, apply padic_int.norm_le_one, apply_instance, apply_instance, },
  { --simp, rw padic_int.norm_int_le_pow_iff_dvd,
    apply le_of_eq, rw norm_coe_eq_ring_hom_map p,
    simp only [one_div, map_nat_cast, norm_pow, ring_hom.map_pow, inv_pow,
      nat.cast_pow, padic_norm_e.norm_p],
    apply_instance,  apply_instance, },
end

lemma norm_mul_two_le_one {k : ℕ} [normed_algebra ℚ_[p] R] [norm_one_class R] (hk : 1 < k) (hp : 2 < p)
  (y : ℕ) : ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥ ≤ 1 :=
begin
  rw ← nat.cast_pow,
  have : (((d * p ^ y) ^ (k - 2) : ℕ) : R) * (1 + 1 : R) = (algebra_map ℚ_[p] R)
     (padic_int.coe.ring_hom (((d * p ^ y) ^ (k - 2) : ℤ_[p]) * (2 : ℤ_[p]))),
  { symmetry,
    simp only [map_nat_cast, ring_hom.map_bit0, ring_hom.map_pow, ring_hom.map_one,
      nat.cast_mul, nat.cast_pow, ring_hom.map_mul],
    refl, },
  rw [this], rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one, -- rw norm_algebra_map_eq,
  apply padic_int.norm_le_one _,
end

lemma sub_add_norm_nonneg {k : ℕ} [normed_algebra ℚ_[p] R] (hk : 1 < k) (y : ℕ) :
  0 ≤ (k : ℝ) - 1 + ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥ :=
begin
  apply add_nonneg _ (norm_nonneg _),
  rw [le_sub_iff_add_le, zero_add], norm_cast,
  apply le_of_lt hk,
end

lemma norm_two_mul_le {k : ℕ} [normed_algebra ℚ_[p] R] [norm_one_class R] (hk : 1 < k) (hp : 2 < p) (y : ℕ) :
  ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥) ≤ k :=
begin
  rw ← one_mul ↑k, apply mul_le_mul,
  { apply le_of_eq, rw norm_inv,
    rw inv_eq_one,
    have : ((2 : ℕ) : ℚ_[p]) = (2 : ℚ_[p]), norm_cast,
    rw ← this, rw ← rat.cast_coe_nat,
    rw padic_norm_e.eq_padic_norm,
    rw padic_norm.padic_norm_of_prime_of_ne (λ h, _),
    { rw rat.cast_one, },
    { assumption, },
    { apply nat.prime.fact, },
    { apply ne_of_gt _,
      apply h, apply_instance,
      apply hp, }, },
  { rw one_mul,
    apply le_trans (add_le_add le_rfl (norm_mul_two_le_one d p hk hp _)) _,
    { apply_instance, }, --why is this a problem?
    { apply_instance, },
    rw sub_add_cancel, },
  { rw one_mul, convert sub_add_norm_nonneg d p hk y,
    { apply_instance, }, },
  { linarith, },
end

lemma exists_mul_mul_mul_lt {k : ℕ} (ε : ℝ)
  (χ : dirichlet_character R (d * p ^ m)) [nontrivial R] [no_zero_divisors R]
  [normed_algebra ℚ_[p] R] [norm_one_class R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (hε : ε > 0) :  ∃ x : ℕ,
  ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ x : ℕ) : R) ^ (k - 2) * (1 + 1)∥) *
  (∥(((d * p ^ x) : ℕ) : R)∥ * (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ k)).bound) < ε :=
begin
  have one_div_lt_one : 1 / (p : ℝ) < 1,
  { rw one_div_lt _ _,
    { rw one_div_one, norm_cast, apply nat.prime.one_lt, apply fact.out, },
    { norm_cast, apply nat.prime.pos, apply fact.out, },
    { norm_num, }, },
  have pos' : 0 < ↑k * (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound,
  { apply mul_pos _ (dirichlet_character.bound_pos _), norm_cast,
    apply lt_trans zero_lt_one hk, },
  have pos : 0 < ε / (↑k * (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound),
  { apply div_pos hε pos', },
  refine ⟨classical.some (exists_pow_lt_of_lt_one pos one_div_lt_one), _⟩,
  apply lt_of_le_of_lt (mul_le_mul (norm_two_mul_le d p hk hp _) le_rfl (mul_nonneg (norm_nonneg _)
    (le_of_lt (dirichlet_character.bound_pos _))) (nat.cast_nonneg _)) _,
  { apply_instance, },
  { apply_instance, },
  rw mul_left_comm,
  apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow d p _) le_rfl (le_of_lt pos') _) _,
  { apply_instance, },
  { apply_instance, },
  { rw ← one_div_pow, apply pow_nonneg _ _,
    apply div_nonneg _ _,
    any_goals { norm_cast, apply nat.zero_le _, }, },
  { rw ← one_div_pow,
    have := classical.some_spec (exists_pow_lt_of_lt_one pos one_div_lt_one),
    apply lt_of_lt_of_le (mul_lt_mul this le_rfl pos' (div_nonneg (le_of_lt hε) (le_of_lt pos'))) _,
    rw div_mul_eq_mul_div, rw mul_div_assoc, rw div_self (λ h, _),
    { rw mul_one, },
    { rw mul_eq_zero at h, cases h,
      { norm_cast at h, rw h at hk, simp only [not_lt_zero'] at hk, apply hk, },
      { have := (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound_pos,
        rw h at this,
        simp only [lt_self_iff_false] at this,
        exact this, }, }, },
end

lemma norm_mul_eq [normed_algebra ℚ_[p] R] [norm_one_class R] (x y : ℕ) :
  ∥(x * y : R)∥ = ∥(x : R)∥ * ∥(y : R)∥ :=
begin
  rw ← nat.cast_mul, rw norm_coe_eq_ring_hom_map p,
  rw nat.cast_mul, rw ring_hom.map_mul,
  rw padic_norm_e.mul,
  rw ← norm_coe_eq_ring_hom_map p, rw ← norm_coe_eq_ring_hom_map p,
  any_goals { apply_instance, },
end

lemma norm_pow_eq [normed_algebra ℚ_[p] R]  [norm_one_class R] (x n : ℕ) :
  ∥(x ^ n : R)∥ = ∥(x : R)∥^n :=
begin
  rw ← nat.cast_pow, rw norm_coe_eq_ring_hom_map p,
  rw nat.cast_pow, rw ring_hom.map_pow, rw norm_pow,
  rw ← norm_coe_eq_ring_hom_map p,
  any_goals { apply_instance, },
end

lemma norm_le_of_ge [normed_algebra ℚ_[p] R] [norm_one_class R] {x y : ℕ} (h : x ≤ y) :
  ∥((d * p^y : ℕ) : R)∥ ≤ ∥((d * p^x : ℕ) : R)∥ :=
begin
  repeat { rw nat.cast_mul, rw norm_mul_eq p, },
  { apply mul_le_mul le_rfl _ (norm_nonneg _) (norm_nonneg _),
    rw norm_coe_eq_ring_hom_map p, rw norm_coe_eq_ring_hom_map p,
    simp only [map_nat_cast, norm_pow, ring_hom.map_pow, inv_pow,
      nat.cast_pow, padic_norm_e.norm_p],
    rw inv_le_inv _ _,
    apply pow_le_pow _ h,
    { norm_cast, apply le_of_lt (nat.prime.one_lt _), apply fact.out, },
    any_goals { norm_cast, apply pow_pos _ _, apply nat.prime.pos _, apply fact.out, },
    any_goals { apply_instance, }, },
  any_goals { apply_instance, },
end
