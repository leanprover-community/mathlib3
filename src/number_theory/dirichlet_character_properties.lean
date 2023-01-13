import number_theory.dirichlet_character
import number_theory.zmod_properties
import analysis.normed_space.basic
import topology.algebra.group
import topology.continuous_function.compact

/-- Making `zmod` a discrete topological space. -/
def zmod.topological_space' (d : ℕ) : topological_space (zmod d) := ⊥

local attribute [instance] zmod.topological_space'
open_locale big_operators

namespace nat
lemma coprime_sub {n m : ℕ} (h : n.coprime m) (hn : m ≤ n) : (n - m).coprime n :=
begin
  by_contradiction h',
  obtain ⟨p, h1, h2, h3⟩ := nat.prime.not_coprime_iff_dvd.1 h',
  have h4 := nat.dvd_sub (nat.sub_le _ _) h3 h2,
  rw nat.sub_sub_self hn at h4,
  apply nat.prime.not_coprime_iff_dvd.2 ⟨p, h1, h3, h4⟩ h,
end
end nat

namespace dirichlet_character
lemma continuous {R : Type*} [monoid R] [topological_space R]
  {n : ℕ} (χ : dirichlet_character R n) : continuous χ := continuous_of_discrete_topology

open dirichlet_character
lemma asso_dirichlet_character_continuous {R : Type*} [monoid_with_zero R] [topological_space R]
  {n : ℕ} (χ : dirichlet_character R n) : _root_.continuous (asso_dirichlet_character χ) :=
begin
  convert continuous_of_discrete_topology,
  apply_instance,
end

lemma asso_dirichlet_character_bounded {R : Type*} [monoid_with_zero R]
  [normed_group R] {n : ℕ} [fact (0 < n)] (χ : dirichlet_character R n) : ∃ M : ℝ,
  ∥ (⟨asso_dirichlet_character χ,
    dirichlet_character.asso_dirichlet_character_continuous χ⟩ : C(zmod n, R)) ∥ < M :=
begin
  refine ⟨(⨆ i : zmod n, ∥asso_dirichlet_character χ i∥) + 1, _⟩,
  apply lt_of_le_of_lt _ (lt_add_one _),
  { convert le_refl _,
    rw continuous_map.norm_eq_supr_norm,
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
          right, left, rw ←hy, },
        { rw h' at hy,
          right, right, rw hy, }, },
      { apply int.is_unit_eq_one_or h, }, },
    rw asso_dirichlet_character_eq_zero _ h at hy,
    left, rw ←hy,
    rw asso_dirichlet_character_eq_zero _,
    apply @not_is_unit_zero _ _ infer_instance,
    change nontrivial ℤ, apply_instance, },
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
set.finite.bdd_above (asso_dirichlet_character_range_fin _)

lemma asso_dirichlet_character_bounded_spec {R : Type*} [monoid_with_zero R] [normed_group R]
  {n : ℕ} (χ : dirichlet_character R n) :
  ∃ M : ℝ, (∀ a, ∥asso_dirichlet_character χ a∥ < M) ∧ 0 < M :=
begin
  refine ⟨(⨆ i : zmod n, ∥asso_dirichlet_character χ i∥) + 1, λ a, lt_of_le_of_lt _
    (lt_add_one _), (lt_add_of_le_of_pos _ _)⟩,
  { apply le_cSup (asso_dirichlet_character_range_bdd_above _) (⟨a, rfl⟩), },
  { apply le_csupr_of_le _ _,
    swap 3, { exact 1, },
    { apply norm_nonneg _, },
    { apply asso_dirichlet_character_range_bdd_above, }, },
  { norm_num, },
end

/-- Every Dirichlet character is bounded above. -/
noncomputable abbreviation bound {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) : ℝ :=
classical.some (dirichlet_character.asso_dirichlet_character_bounded_spec χ)

lemma lt_bound {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) (a : zmod n) :
  ∥asso_dirichlet_character χ a∥ < dirichlet_character.bound χ :=
(classical.some_spec (dirichlet_character.asso_dirichlet_character_bounded_spec χ)).1 a

lemma bound_pos {R : Type*} [monoid_with_zero R] [normed_group R] {n : ℕ}
  (χ : dirichlet_character R n) : 0 < dirichlet_character.bound χ :=
(classical.some_spec (dirichlet_character.asso_dirichlet_character_bounded_spec χ)).2

open zmod
lemma mul_eval_of_coprime {R : Type*} [comm_monoid_with_zero R] {n m : ℕ}
  (χ : dirichlet_character R n) (ψ : dirichlet_character R m) {a : ℕ} (ha : a.coprime (n * m)) :
  asso_dirichlet_character (dirichlet_character.mul χ ψ) a =
  asso_dirichlet_character χ a * (asso_dirichlet_character ψ a) :=
begin
  rw [mul, ←(zmod.cast_nat_cast (conductor_dvd (χ.change_level (dvd_lcm_left n m) *
    ψ.change_level (dvd_lcm_right n m))) a)],
  { have dvd : lcm n m ∣ n * m := lcm_dvd_iff.2 ⟨(dvd_mul_right _ _), (dvd_mul_left _ _)⟩,
    have := zmod.is_unit_of_is_coprime_dvd dvd ha,
    rw ←change_level_asso_dirichlet_character_eq' _ (conductor_dvd _) this,
    delta asso_primitive_character,
    rw [←(factors_through_spec _ (factors_through_conductor (χ.change_level _ * ψ.change_level _))),
      asso_dirichlet_character_mul, monoid_hom.mul_apply, change_level_asso_dirichlet_character_eq'
      _ _ this, change_level_asso_dirichlet_character_eq' _ _ this, zmod.cast_nat_cast
      (dvd_lcm_left n m), zmod.cast_nat_cast (dvd_lcm_right n m)],
    any_goals { refine zmod.char_p _, }, },
  { refine zmod.char_p _, },
end

namespace asso_dirichlet_character
lemma eval_mul_sub {R : Type*} [monoid_with_zero R] {n : ℕ} (χ : dirichlet_character R n)
  (k x : ℕ) : asso_dirichlet_character χ (k * n - x) = asso_dirichlet_character χ (-1) *
  (asso_dirichlet_character χ x) :=
by { rw [zmod.nat_cast_self, mul_zero, zero_sub, neg_eq_neg_one_mul, monoid_hom.map_mul], }

lemma eval_mul_sub' {R : Type*} [monoid_with_zero R] {n k : ℕ} (χ : dirichlet_character R n)
  (hk : n ∣ k) (x : ℕ) : asso_dirichlet_character χ (k - x) = asso_dirichlet_character χ (-1) *
  (asso_dirichlet_character χ x) :=
begin
  have : (k : zmod n) = 0,
  { rw [←zmod.nat_cast_mod, nat.mod_eq_zero_of_dvd hk, nat.cast_zero], },
  rw [this, zero_sub, neg_eq_neg_one_mul, monoid_hom.map_mul],
end
end asso_dirichlet_character

/-- The level at which the Dirichlet character is defined. -/
abbreviation lev {R : Type*} [monoid R] {n : ℕ} (χ : dirichlet_character R n) : ℕ := n
-- dont know how to remove this linting error

lemma lev_mul_dvd_lcm {R : Type*} [comm_monoid_with_zero R] {n k : ℕ} (χ : dirichlet_character R n)
  (ψ : dirichlet_character R k) : lev (mul χ ψ) ∣ lcm n k := dvd_trans (conductor_dvd _) dvd_rfl

lemma lev_mul_dvd_mul_lev {R : Type*} [comm_monoid_with_zero R] {n k : ℕ} (χ : dirichlet_character R n)
  (ψ : dirichlet_character R k) : lev (mul χ ψ) ∣ n * k :=
dvd_trans (conductor_dvd _) (nat.lcm_dvd_mul _ _)

open dirichlet_character
lemma mul_eval_neg_one {R : Type*} [comm_monoid_with_zero R] {n m : ℕ} [fact (0 < n)] [fact (0 < m)]
  (χ : dirichlet_character R n) (ψ : dirichlet_character R m) :
  asso_dirichlet_character (dirichlet_character.mul χ ψ) (-1 : ℤ) =
  asso_dirichlet_character χ (-1) * asso_dirichlet_character ψ (-1) :=
begin
  have one_le : 1 ≤ n * m := nat.succ_le_iff.2 (nat.mul_pos (fact.out _) (fact.out _)),
  have f1 : (-1 : zmod (lev (χ.mul ψ))) = ↑((n * m - 1) : ℕ),
  { rw [nat.cast_sub one_le, (zmod.nat_coe_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (conductor_dvd _)
      (lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))), zero_sub, nat.cast_one], },
  rw [int.cast_neg, int.cast_one, f1,
    mul_eval_of_coprime _ _ (nat.coprime_sub (nat.coprime_one_right _) one_le)],
  simp only [nat.cast_sub one_le, nat.cast_sub one_le, nat.cast_mul, zmod.nat_cast_self, zero_mul,
    nat.cast_one, zero_sub, mul_zero],
end

lemma mul_eval_int {R : Type*} [comm_monoid_with_zero R] {n m : ℕ} [fact (0 < n)] [fact (0 < m)]
  (χ : dirichlet_character R n) (ψ : dirichlet_character R m) {a : ℤ}
  (ha : is_coprime a (n * m : ℤ)) : asso_dirichlet_character (dirichlet_character.mul χ ψ) a =
  asso_dirichlet_character χ a * asso_dirichlet_character ψ a :=
begin
  cases a,
  { change asso_dirichlet_character (dirichlet_character.mul χ ψ) a =
      asso_dirichlet_character χ a * asso_dirichlet_character ψ a,
    rw mul_eval_of_coprime χ ψ (nat.is_coprime_iff_coprime.1 ha), },
  { rw [int.neg_succ_of_nat_coe, ←neg_one_mul, int.cast_mul, monoid_hom.map_mul, mul_eval_neg_one],
    rw [int.neg_succ_of_nat_coe, is_coprime.neg_left_iff] at ha,
    rw [int.cast_coe_nat, mul_eval_of_coprime χ ψ (nat.is_coprime_iff_coprime.1 ha),
      mul_mul_mul_comm],
    simp_rw [←monoid_hom.map_mul, int.cast_mul],
    norm_cast, },
end

instance {R : Type*} [comm_monoid_with_zero R] {n : ℕ} : has_pow (dirichlet_character R n) ℕ :=
monoid.has_pow

lemma pow_apply {R : Type*} [comm_monoid_with_zero R] {n : ℕ} (k : ℕ)
  (χ : dirichlet_character R n) (a : (zmod n)ˣ) :
  ((χ: monoid_hom (units (zmod n)) (units R))^k) a = (χ a)^k := rfl
end dirichlet_character
