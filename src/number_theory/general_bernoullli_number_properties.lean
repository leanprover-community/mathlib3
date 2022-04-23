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

lemma asso_dirichlet_character_zero_range {R : Type*} [monoid_with_zero R] [normed_group R]
  (χ : dirichlet_character R 0) : (set.range (λ (i : zmod 0), ∥(asso_dirichlet_character χ) i∥)) =
    {∥asso_dirichlet_character χ 0∥, ∥asso_dirichlet_character χ 1∥,
      ∥asso_dirichlet_character χ (-1)∥} :=
begin
  ext,
  simp only [set.mem_insert_iff, set.mem_range, set.mem_singleton_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { cases h with y hy,
    by_cases is_unit y,
    { suffices h' : y = 1 ∨ y = -1,
      { cases h',
        { rw h' at hy,
          change ∥(asso_dirichlet_character χ) 1∥ = x at hy,
          right, left, rw ←hy, },
        { rw h' at hy,
          change ∥(asso_dirichlet_character χ) (-1)∥ = x at hy,
          right, right, rw hy, }, },
      { have := int.units_eq_one_or (is_unit.unit h),
        cases this,
        { left, rw ←units.eq_iff at this, rw is_unit.unit_spec at this, rw units.coe_one at this,
          rw this, },
        { right, rw ←units.eq_iff at this, rw is_unit.unit_spec at this,
          rw units.coe_neg_one at this, rw this, }, }, },
    rw asso_dirichlet_character_eq_zero _ at hy,
    left, rw ←hy, rw asso_dirichlet_character_eq_zero _,
    apply @not_is_unit_zero _ _ _, change nontrivial ℤ, apply_instance,
    { apply h, }, },
  { cases h,
    { refine ⟨0, _⟩, rw h, },
    { cases h,
      { rw h, refine ⟨1, rfl⟩, },
      { rw h, refine ⟨-1, rfl⟩, }, }, },
end

lemma asso_dirichlet_character_zero_range_fin {R : Type*} [monoid_with_zero R] [normed_group R]
  (χ : dirichlet_character R 0) :
  (set.range (λ (i : zmod 0), ∥(asso_dirichlet_character χ) i∥)).finite :=
begin
  rw asso_dirichlet_character_zero_range,
  simp only [set.finite_singleton, set.finite.insert],
end

noncomputable instance dirichlet_character.zero {R : Type*} [monoid_with_zero R] [normed_group R]
  (χ : dirichlet_character R 0) :
  fintype (set.range (λ (i : zmod 0), ∥(asso_dirichlet_character χ) i∥)) :=
begin
  rw asso_dirichlet_character_zero_range,
  apply set.fintype_insert (∥asso_dirichlet_character χ 0∥)
  { ∥asso_dirichlet_character χ 1∥, ∥asso_dirichlet_character χ (-1)∥},
end

lemma asso_dirichlet_character_range_fin {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) :
  (set.range (λ (i : zmod n), ∥(asso_dirichlet_character χ) i∥)).finite :=
begin
  cases n, -- big improvement over by_cases n!
  { apply asso_dirichlet_character_zero_range_fin _, },
  { haveI : fact (0 < n.succ) := fact_iff.2 (nat.succ_pos _),
    exact set.finite_range (λ (i : zmod n.succ), ∥(asso_dirichlet_character χ) i∥), },
end

lemma asso_dirichlet_character_range_bdd_above {R : Type*} [monoid_with_zero R] [normed_group R]
  {n : ℕ} (χ : dirichlet_character R n) :
  bdd_above (set.range (λ (i : zmod n), ∥(asso_dirichlet_character χ) i∥)) :=
begin
  apply set.finite.bdd_above _,
  { apply_instance, },
  { apply asso_dirichlet_character_range_fin, },
end

lemma dirichlet_character.asso_dirichlet_character_bounded'
  {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ} --[fact (0 < n)]
  (χ : dirichlet_character R n) : ∃ M : ℝ, (∀ a, ∥asso_dirichlet_character χ a∥ < M) ∧ 0 ≤ M :=
begin
  refine ⟨(⨆ i : zmod n, ∥asso_dirichlet_character χ i∥) + 1, λ a, _, _⟩,
  { apply lt_of_le_of_lt _ (lt_add_one _),
    { apply le_cSup _ _,
      { apply asso_dirichlet_character_range_bdd_above, },
      { refine ⟨a, rfl⟩, }, },
    { apply_instance, }, },
  { apply add_nonneg _ _,
    { apply_instance, },
    { apply le_csupr_of_le _ _,
      swap 3, { exact 1, },
      { apply norm_nonneg _, },
      { apply asso_dirichlet_character_range_bdd_above, }, },
    { norm_num, }, },
end

noncomputable abbreviation dirichlet_character.bound {R : Type*} [monoid_with_zero R]
  [normed_group R] {n : ℕ} (χ : dirichlet_character R n) : ℝ :=
classical.some (dirichlet_character.asso_dirichlet_character_bounded' χ)

lemma dirichlet_character.bound_spec {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) (a : zmod n) :
  ∥asso_dirichlet_character χ a∥ < dirichlet_character.bound χ :=
(classical.some_spec (dirichlet_character.asso_dirichlet_character_bounded' χ)).1 a

lemma dirichlet_character.bound_nonneg {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) : 0 ≤ dirichlet_character.bound χ :=
(classical.some_spec (dirichlet_character.asso_dirichlet_character_bounded' χ)).2

lemma units.coe_map_of_dvd {a b : ℕ} (h : a ∣ b) (x : units (zmod b)) : --(hx : is_unit x) :
  is_unit (x : zmod a) :=
begin
  change is_unit ((x : zmod b) : zmod a),
  rw ←zmod.cast_hom_apply (x : zmod b),
  swap 3, { refine zmod.char_p _, },
  swap, { apply h, },
  rw ←ring_hom.coe_monoid_hom,
  rw ←units.coe_map, apply units.is_unit,
end

lemma is_unit_coe {a b : ℕ} (h : a ∣ b) {x : ℕ} (hx : is_coprime (x : ℤ) b) :
  is_unit (x : zmod a) :=
begin
  rw nat.is_coprime_iff_coprime at hx,
  set y := zmod.unit_of_coprime _ hx,
  convert_to is_unit ((y : zmod b) : zmod a),
  { rw ←zmod.cast_nat_cast h x, congr, refine zmod.char_p _, },
    { change is_unit (y : zmod a),
      apply units.coe_map_of_dvd h _, },
end

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
  rw ←change_level_asso_dirichlet_character_eq' _ (conductor_dvd _) (is_unit_coe dvd ha),
  { convert_to asso_dirichlet_character ((χ.change_level (dvd_lcm_left n m) *
      ψ.change_level (dvd_lcm_right n m))) (a : zmod (lcm n m)) = _,
    { delta asso_primitive_character,
      rw ← (factors_through_spec _ (factors_through_conductor (χ.change_level (dvd_lcm_left n m) *
        ψ.change_level (dvd_lcm_right n m)))), },
    rw asso_dirichlet_character_mul,
    rw monoid_hom.mul_apply, congr,
    { rw change_level_asso_dirichlet_character_eq' _ _ (is_unit_coe dvd ha),
      { rw zmod.cast_nat_cast (dvd_lcm_left _ _),
        refine zmod.char_p _, }, },
    { rw change_level_asso_dirichlet_character_eq' _ _ (is_unit_coe dvd ha),
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

example [semi_normed_algebra ℚ_[p] R] [nontrivial R] : function.injective (algebra_map ℚ_[p] R) :=
(algebra_map ℚ_[p] R).injective

@[simp] lemma teichmuller_character_mod_p_change_level_eval_neg_one --[normed_comm_ring R]
  [no_zero_divisors R] [semi_normed_algebra ℚ_[p] R] [nontrivial R] (hp : (2 < p))
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
    { haveI : char_zero R :=
        (ring_hom.char_zero_iff ((algebra_map ℚ_[p] R).injective)).1 infer_instance,
      apply @nat.cast_add_one_ne_zero R _ _ _ 1,
      rw neg_one_pow_eq_neg_one p hp at neg_one_pow,
      rw ←eq_neg_iff_add_eq_zero, rw nat.cast_one,
      rw ←units.eq_iff at neg_one_pow, rw units.coe_one at neg_one_pow,
      rw units.coe_neg_one at neg_one_pow, rw neg_one_pow, },
    { convert this, rw units.map,
      rw ←units.eq_iff,
      simp, }, },
end
.

lemma teichmuller_character_mod_p_change_level_pow_eval_neg_one
  (k : ℕ) (hp : 2 < p) [semi_normed_algebra ℚ_[p] R] [nontrivial R] [no_zero_divisors R]
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

--set_option pp.proofs true
lemma sum_eq_neg_sum_add_dvd (hχ : χ.is_even) [semi_normed_algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) (k : ℕ) (hk : 1 ≤ k) :
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
  { rw ←pow_add, rw nat.add_sub_pred, rw nat.neg_one_pow_of_odd _, rw nat.odd_iff,
    rw nat.two_mul_sub_one_mod_two_eq_one hk, },
  any_goals { apply fact_iff.2 (mul_prime_pow_pos p d m), },
end

lemma nat.pow_eq_mul_pow_sub (k : ℕ) (hk : 1 < k) :
  (d * p^m)^(k - 1) = (d * p^m) * (d * p^m)^(k - 2) :=
begin
  conv_rhs { congr, rw ←pow_one (d * p^m), },
  rw ←pow_add, congr, rw add_comm,
  conv_rhs { rw nat.sub_succ, rw ←nat.succ_eq_add_one,
    rw nat.succ_pred_eq_of_pos (nat.lt_sub_right_iff_add_lt.2 _), skip,
    apply_congr hk, },
end

lemma asso_dc [semi_normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ)
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

--instance {R : Type*} [normed_comm_ring R] [semi_normed_algebra ℚ_[p] R] : norm_one_class R :=
--by {fconstructor, convert normed_algebra.norm_one ℚ_[p] R, }

example {R : Type*} [comm_ring R] {a b c : R} : a * (b * c) = b * (a * c) := by refine mul_left_comm a b c

lemma norm_sum_le_smul {k : ℕ} [nontrivial R] [no_zero_divisors R] [semi_normed_algebra ℚ_[p] R]
  [fact (0 < m)] (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) :
  ∥∑ (x : ℕ) in finset.range (d * p ^ m + 1), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ((-1) * ↑x) *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ m) ^ x_1 * ((-1) * ↑x) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))∥ ≤ (d * p ^ m + 1) • (dirichlet_character.bound
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)) * (k - 1)) :=
begin
  have : ∀ x ∈ finset.range (d * p ^ m + 1),
  ∥(asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)))
    ((-1) * ↑x) * ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ m) ^ x_1 * ((-1) * ↑x) ^
    (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1)) ∥ ≤ (dirichlet_character.bound
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) * (k - 1),
  { intros x hx,
    apply le_trans (norm_mul_le _ _) _,
    --rw ← mul_one ((χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k)).bound),
    apply mul_le_mul (le_of_lt (dirichlet_character.bound_spec _ _)) _ (norm_nonneg _)
      (dirichlet_character.bound_nonneg _),
    { simp_rw [mul_pow], simp_rw [mul_left_comm], simp_rw [mul_assoc],
      apply le_trans (norm_sum_le _ _) _,
      have : ∀ a ∈ finset.range (k - 1), ∥(-1 : R) ^ (k - 1 - (a + 1)) * (↑(d * p ^ m) ^ a *
        (↑x ^ (k - 1 - (a + 1)) * ↑((k - 1).choose (a + 1))))∥ ≤ 1,
      { intros a ha,
        apply le_trans (norm_mul_le _ _) _,
        have : (((d * p ^ m) ^ a * (x ^ (k - 1 - (a + 1)) * (k - 1).choose (a + 1)) : ℕ) : R) =
          (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ((d * p ^ m) ^ a *
          (x ^ (k - 1 - (a + 1)) * (k - 1).choose (a + 1)) : ℤ_[p])),
        { simp only [ring_hom.map_nat_cast, ring_hom.map_pow, nat.cast_mul, nat.cast_pow,
            ring_hom.map_mul], },
        cases neg_one_pow_eq_or R (k - 1 - (a + 1)),
        { rw h, rw normed_algebra.norm_one ℚ_[p] R, rw one_mul,
          rw ← nat.cast_pow, rw ← nat.cast_pow, rw ← nat.cast_mul, rw ← nat.cast_mul,
          rw this, rw norm_algebra_map_eq, apply padic_int.norm_le_one, },
        { rw h, rw norm_neg, rw normed_algebra.norm_one ℚ_[p] R, rw one_mul,
          rw ← nat.cast_pow, rw ← nat.cast_pow, rw ← nat.cast_mul, rw ← nat.cast_mul,
          rw this, rw norm_algebra_map_eq, apply padic_int.norm_le_one, }, },
      { convert le_trans (finset.sum_le_sum this) _,
        rw finset.sum_const, rw finset.card_range, rw nat.smul_one_eq_coe,
        rw nat.cast_sub (le_of_lt hk), rw nat.cast_one, }, }, },
  { apply le_trans (norm_sum_le _ _) _,
    convert le_trans (finset.sum_le_sum this) _,
    rw finset.sum_const,
    rw finset.card_range, },
end

instance wut [nontrivial R] [semi_normed_algebra ℚ_[p] R] : char_zero R :=
(ring_hom.char_zero_iff ((algebra_map ℚ_[p] R).injective)).1 infer_instance

lemma sum_odd_char [nontrivial R] [no_zero_divisors R] [semi_normed_algebra ℚ_[p] R]
  [fact (0 < n)] [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) :
  ∃ y, (2 : R) * ∑ i in finset.range (d * p^m), ((asso_dirichlet_character (dirichlet_character.mul χ
    ((teichmuller_character_mod_p_change_level p d R m)^k))) i * i^(k - 1)) =
    ↑(d * p^m) * y ∧ ∥y∥ ≤ (d * p ^ m + 1) • ((χ.mul
    (teichmuller_character_mod_p_change_level p d R m ^ k)).bound * (↑k - 1)) +
    ∥(((d * p ^ m : ℕ) : R) ^ (k - 2)) * (1 + 1)∥ * (χ.mul
    (teichmuller_character_mod_p_change_level p d R m ^ k)).bound :=
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
  clear f1,
  rw mul_sub, rw mul_comm _ (↑(d * p ^ m) ^ (k - 1)),
  rw ←mul_assoc _ (↑(d * p ^ m) ^ (k - 1)) _, rw mul_comm _ (↑(d * p ^ m) ^ (k - 1)),
  rw mul_assoc _ (2 : R) _, rw ←nat.cast_pow,
  conv { congr, funext, rw sub_eq_iff_eq_add, rw nat.pow_eq_mul_pow_sub d p m k hk,
    rw nat.cast_mul (d * p^m) _, rw mul_assoc ↑(d * p^m) _ _,
    conv { congr, rw ←mul_add ↑(d * p^m) _ _, }, },
  have two_eq_one_add_one : (2 : R) = (1 : R) + (1 : R) := rfl,
  rw two_eq_one_add_one, rw add_mul, rw one_mul,
  conv { congr, funext, conv { congr, to_lhs, congr, skip,
    rw sum_eq_neg_sum_add_dvd d p m _ hχ hp k (le_of_lt hk), }, },
  rw ←neg_eq_neg_one_mul, rw ←add_assoc, rw ←sub_eq_add_neg,
  conv { congr, funext, rw sub_self _, rw zero_add, },
  refine ⟨_, _, _⟩,
  { exact ∑ (x : ℕ) in finset.range (d * p ^ m + 1),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) (-1) *
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑x *
    ∑ (x_1 : ℕ) in finset.range (k - 1),
    ↑(d * p ^ m) ^ x_1 * ((-1) * ↑x) ^ (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1))) -
    ↑((d * p ^ m) ^ (k - 2)) * ((1 + 1) * (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p_change_level p d R m ^ k))) ↑(d * p ^ m)), },
  { rw sub_add_cancel, },
  { apply le_trans (norm_sub_le _ _) _,
    conv { congr, congr, congr, apply_congr, skip, rw ← mul_assoc, rw ←monoid_hom.map_mul, },
    apply le_trans (add_le_add (norm_sum_le_smul d p m _ hk hχ hp) (le_refl _)) _,
    rw ← mul_assoc,
    apply le_trans (add_le_add (le_refl _) (norm_mul_le _ _)) _,
    apply le_trans (add_le_add (le_refl _) ((mul_le_mul_left _).2
      (le_of_lt (dirichlet_character.bound_spec _ _)))) _,
    { rw lt_iff_le_and_ne,
      refine ⟨norm_nonneg _, λ h, _⟩,
      rw eq_comm at h, rw norm_eq_zero at h,
      rw mul_eq_zero at h, cases h,
      { rw nat.cast_eq_zero at h, apply pow_ne_zero _ _ h,
        apply ne_zero_of_lt (mul_prime_pow_pos p d _), },
      { rw ← eq_neg_iff_add_eq_zero at h,
        apply zero_ne_one (eq_zero_of_eq_neg R h).symm, }, },
    { rw nat.cast_pow, }, },
end

lemma sum_odd_character [nontrivial R] [no_zero_divisors R] [semi_normed_algebra ℚ_[p] R]
  [fact (0 < n)] [fact (0 < m)] {k : ℕ} (hk : 1 < k) :
  filter.tendsto (λ m, ∑ i in finset.range (d * p^m), ((asso_dirichlet_character
  (dirichlet_character.mul χ ((teichmuller_character_mod_p_change_level p d R (d * p^m))^k)))
  i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0) :=
begin
  rw metric.tendsto_at_top,
  intros ε hε,
  refine ⟨_, λ x hx, _⟩,
  swap,
  rw dist_eq_norm, rw sub_zero,
--  cases sum_odd_char d p m χ hk,
  sorry,
  sorry,
end
