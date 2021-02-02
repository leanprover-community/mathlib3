/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import analysis.special_functions.pow
import algebraic_number_theory.class_number.euclidean_absolute_value
import algebraic_number_theory.class_number.finset
import combinatorics.pigeonhole
import field_theory.finite.basic

/-!
# Admissible absolute values

This file defines a structure `admissible_absolute_value` which we use to show the class number
of the ring of integers of a global field is finite.
-/

section admissible

variables {R : Type*} [euclidean_domain R]

/-- An `admissible_absolute_value R` is a Euclidean absolute value `R → ℤ`,
such that a large enough set of elements in `R^n` will contain a pair of elements
whose remainders are pointwise close together. -/
structure admissible_absolute_value (R : Type*) [euclidean_domain R]
  extends euclidean_absolute_value R ℤ :=
(card : ℝ → ℕ)
(exists_partition' : ∀ (n : ℕ) {ε : ℝ} (hε : 0 < ε) (b : R) (hb : b ≠ 0) (A : fin n → R),
                     ∃ (t : fin n → fin (card ε)),
                     ∀ i₀ i₁, t i₀ = t i₁ → (to_fun (A i₁ % b - A i₀ % b) : ℝ) < to_fun b • ε)

variables (abs : admissible_absolute_value R)

namespace admissible_absolute_value

instance : has_coe_to_fun (admissible_absolute_value R) :=
{ F := _,
  coe := λ abs, abs.to_fun }

instance : has_coe (admissible_absolute_value R) (euclidean_absolute_value R ℤ) :=
⟨λ abs, abs.to_euclidean_absolute_value⟩

instance : has_coe (admissible_absolute_value R) (absolute_value R ℤ) :=
⟨λ abs, abs.to_euclidean_absolute_value.to_absolute_value⟩

lemma nonneg (x : R) : 0 ≤ abs x := abs.to_euclidean_absolute_value.nonneg x

@[simp]
lemma eq_zero_iff {x : R} : abs x = 0 ↔ x = 0 :=
abs.to_euclidean_absolute_value.map_eq_zero_iff' x

@[simp]
lemma map_zero : abs 0 = 0 :=
abs.to_euclidean_absolute_value.map_zero

lemma map_ne_zero {x : R} : abs x ≠ 0 ↔ x ≠ 0 :=
abs.to_euclidean_absolute_value.map_ne_zero

lemma pos {x : R} (hx : x ≠ 0) : 0 < abs x :=
abs.to_euclidean_absolute_value.pos hx

@[simp]
lemma map_mul (x y : R) : abs (x * y) = abs x * abs y :=
abs.to_euclidean_absolute_value.map_mul x y

lemma le_add (x y : R) : abs (x + y) ≤ abs x + abs y :=
abs.to_euclidean_absolute_value.le_add x y

@[simp]
lemma map_lt_map_iff {x y : R} : abs x < abs y ↔ euclidean_domain.r x y :=
abs.to_euclidean_absolute_value.map_lt_map_iff

lemma mod_lt (a : R) {b : R} (hb : b ≠ 0) :
  abs (a % b) < abs b :=
abs.to_euclidean_absolute_value.sub_mod_lt a hb

@[simp]
lemma map_sub_eq_zero_iff (a b : R) :
  abs (a - b) = 0 ↔ a = b :=
abs.to_euclidean_absolute_value.map_sub_eq_zero_iff a b

/-- We can partition a finite family into `card ε` sets, such that the remainders
in each set are close together. -/
lemma exists_partition (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (A : fin n → R) :
  ∃ (t : fin n → fin (abs.card ε)),
  ∀ i₀ i₁, t i₀ = t i₁ → (abs (A i₁ % b - A i₀ % b) : ℝ) < abs b • ε :=
abs.exists_partition' n hε b hb A

/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
lemma exists_approx (n : ℕ) :
  ∀ {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (A : fin (abs.card ε ^ n).succ → (fin n → R)),
  ∃ (i₀ i₁), (i₀ ≠ i₁) ∧ ∀ k, (abs (A i₁ k % b - A i₀ k % b) : ℝ) < abs b • ε :=
begin
  haveI := classical.dec_eq R,
  induction n with n ih,
  { intros ε hε b hb A,
    refine ⟨0, 1, _, _⟩,
    { simp },
    rintros ⟨i, ⟨⟩⟩ },
  intros ε hε b hb A,
  by_cases hA : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₀ = A i₁,
  { obtain ⟨i₀, i₁, h, eq⟩ := hA,
    refine ⟨i₀, i₁, h, λ k, _⟩,
    rw [eq, sub_self, abs.map_zero, algebra.smul_def, int.cast_zero, ring_hom.eq_int_cast],
    exact mul_pos (int.cast_pos.mpr (abs.pos hb)) hε },
  have A_inj : function.injective A,
  { simp only [not_exists, not_and, ne.def, not_imp_not] at hA,
    exact λ x y h, hA x y h },
  set M := abs.card ε with hM,
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M^n` elements where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ : ∃ s : fin (M ^ n).succ → fin (M ^ n.succ).succ,
    function.injective s ∧
    ∀ i₀ i₁, (abs (A (s i₁) 0 % b - A (s i₀) 0 % b) : ℝ) < abs b • ε,
  { -- We can partition the `A`s into `m` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ : ∃ (t : fin (M ^ n.succ).succ → fin M),
      ∀ i₀ i₁, t i₀ = t i₁ → (abs (A i₁ 0 % b - A i₀ 0 % b) : ℝ) < abs b • ε :=
      abs.exists_partition _ hε hb (λ x, A x 0),
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ := @fintype.exists_lt_card_fiber_of_mul_lt_card _ _ _ _ _ t (M ^ n)
      (by simpa only [fintype.card_fin, pow_succ] using nat.lt_succ_self (M ^ n.succ) ),
    refine ⟨finset.to_vec _ hs, finset.to_vec_injective _ hs, λ i₀ i₁, ht _ _ _⟩,
    have := finset.to_vec_mem (finset.univ.filter (λ x, t x = s)) hs,
    obtain ⟨_, h₀⟩ := finset.mem_filter.mp (this i₀),
    obtain ⟨_, h₁⟩ := finset.mem_filter.mp (this i₁),
    exact h₀.trans h₁.symm },
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb (λ x, fin.tail (A (s x))),
  refine ⟨s k₀, s k₁, λ h, hk (s_inj h), λ i, fin.cases _ (λ i, _) i⟩,
  { exact hs k₀ k₁ },
  { exact h i },
end

end admissible_absolute_value

end admissible

namespace int

/-- We can partition a finite family of integers between `0` and `b` into `partition_card ε` sets,
such that the elements of each set are within `b * ε` of each other.  -/
noncomputable def partition_card (ε : ℝ) : ℕ := nat_ceil (1 / ε)

lemma le_partition_card (ε : ℝ) : 1 / ε ≤ partition_card ε :=
le_nat_ceil _

/-- We can partition a finite family into `partition_card ε` sets, such that the remainders
in each set are close together. -/
lemma exists_partition (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : ℤ} (hb : b ≠ 0) (A : fin n → ℤ) :
  ∃ (t : fin n → fin (partition_card ε)),
  ∀ i₀ i₁, t i₀ = t i₁ → ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε :=
begin
  have hb' : (0 : ℝ) < ↑(abs b) := int.cast_pos.mpr (abs_pos.mpr hb),
  have hbε : 0 < abs b • ε,
  { rw algebra.smul_def,
    exact mul_pos hb' hε },
  have hfloor : ∀ i, 0 ≤ floor ((A i % b : ℤ) / (abs b • ε) : ℝ),
  { intro i,
    exact floor_nonneg.mpr (div_nonneg (cast_nonneg.mpr (mod_nonneg _ hb)) hbε.le) },
  refine ⟨λ i, ⟨nat_abs (floor ((A i % b : ℤ) / (abs b • ε) : ℝ)), _⟩, _⟩,
  { rw [← coe_nat_lt, nat_abs_of_nonneg (hfloor i), floor_lt],
    apply lt_of_lt_of_le _ (le_partition_card _),
    rw [algebra.smul_def, ring_hom.eq_int_cast, ← div_div_eq_div_mul, div_lt_div_right hε,
        div_lt_iff hb', one_mul, cast_lt],
    exact mod_lt _ hb },
  intros i₀ i₁ hi,
  have hi : (⌊↑(A i₀ % b) / abs b • ε⌋.nat_abs : ℤ) = ⌊↑(A i₁ % b) / abs b • ε⌋.nat_abs :=
    congr_arg (coe : ℕ → ℤ) (subtype.mk_eq_mk.mp hi),
  rw [nat_abs_of_nonneg (hfloor i₀), nat_abs_of_nonneg (hfloor i₁)] at hi,
  have hi := abs_sub_lt_one_of_floor_eq_floor hi,
  rw [abs_sub, ← sub_div, abs_div, abs_of_nonneg hbε.le, div_lt_iff hbε, one_mul] at hi,
  rwa [int.cast_abs, int.cast_sub]
end

/-- `abs : ℤ → ℤ` is an admissible absolute value -/
noncomputable def admissible_abs : admissible_absolute_value ℤ :=
{ map_lt_map_iff' := λ x y, show abs x < abs y ↔ nat_abs x < nat_abs y,
    by rw [abs_eq_nat_abs, abs_eq_nat_abs, coe_nat_lt],
  card := partition_card,
  exists_partition' := λ n ε hε b hb, exists_partition n hε hb,
  .. absolute_value.abs }

end int

namespace polynomial

open absolute_value real

variables {K : Type*} [field K] [fintype K] [decidable_eq K] {c : ℤ} (hc : 1 < c)

section

variables (K)

lemma one_lt_card : 1 < fintype.card K :=
begin
  obtain ⟨p, n, hp, hpn⟩ : ∃ p n, _ ∧ fintype.card K = _ := finite_field.card',
  rw hpn,
  exact pow_lt_pow hp.one_lt n.2
end

/-- `card_pow_degree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ deg f`. -/
noncomputable def card_pow_degree : absolute_value (polynomial K) ℤ :=
pow_degree (nat.cast_lt.mpr (one_lt_card K))

end

lemma card_pow_degree_apply {f : polynomial K} (hf : f ≠ 0) :
  card_pow_degree K f = fintype.card K ^ nat_degree f :=
by { simp only [card_pow_degree, pow_degree, int.nat_cast_eq_coe_nat], exact if_neg hf }

lemma lt_nat_degree_of_lt_degree {f : polynomial K} {n : ℕ} (h : (n : with_bot ℕ) < degree f) :
  n < nat_degree f :=
with_bot.coe_lt_coe.mp (lt_of_lt_of_le h degree_le_nat_degree)

/-- If `A` is a family of enough elements, there is a pair of equal elements in `A`. -/
lemma exists_eq {d : ℕ} {m : ℕ} (hm : fintype.card K ^ d ≤ m) (b : polynomial K)
  (hb : nat_degree b ≤ d) (A : fin m.succ → polynomial K) (hA : ∀ i, degree (A i) < degree b) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ :=
begin
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `0`, ... `degree b - 1` ≤ `d - 1`.
  -- In other words, the following map is not injective:
  set f : fin m.succ → (fin d → K) := λ i j, (A i).coeff j,
  have : fintype.card (fin d → K) < fintype.card (fin m.succ),
  { simpa using lt_of_le_of_lt hm (nat.lt_succ_self m) },
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := fintype.exists_ne_map_eq_of_card_lt f this,
  use [i₀, i₁, i_ne],
  ext j,
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j,
  { rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj),
        coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj)] },
  -- So we only need to look for the coefficients between `0` and `deg b`.
  rw not_le at hbj,
  apply congr_fun i_eq.symm ⟨j, _⟩,
  exact lt_of_lt_of_le (lt_nat_degree_of_lt_degree hbj) hb
end

/-- If `A` is a family of enough elements, there is a pair of elements in `A`
(not necessarily distinct), such that their difference has small degree. -/
lemma exists_approx_aux {d : ℕ} {m : ℕ} (hm : fintype.card K ^ d ≤ m) (b : polynomial K)
  (A : fin m.succ → polynomial K)
  (hA : ∀ i, degree (A i) < degree b):
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(nat_degree b - d) :=
begin
  have hb : b ≠ 0,
  { rintro rfl,
    specialize hA 0,
    rw degree_zero at hA,
    exact not_lt_of_le bot_le hA },
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `degree b - 1`, ... `degree b - d`.
  -- In other words, the following map is not injective:
  set f : fin m.succ → (fin d → K) := λ i j, (A i).coeff (nat_degree b - j.succ),
  have : fintype.card (fin d → K) < fintype.card (fin m.succ),
  { simpa using lt_of_le_of_lt hm (nat.lt_succ_self m) },
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := fintype.exists_ne_map_eq_of_card_lt f this,
  use [i₀, i₁, i_ne],
  refine (degree_lt_iff_coeff_zero _ _).mpr (λ j hj, _),
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j,
  { refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le _ hbj),
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hA _) (hA _)) },
  -- So we only need to look for the coefficients between `deg b - d` and `deg b`.
  rw [coeff_sub, sub_eq_zero],
  rw [not_le, degree_eq_nat_degree hb, with_bot.coe_lt_coe] at hbj,
  have hj : nat_degree b - j.succ < d,
  { by_cases hd : nat_degree b < d,
    { exact lt_of_le_of_lt (nat.sub_le_self _ _) hd },
    { rw not_lt at hd,
      have := lt_of_le_of_lt hj (nat.lt_succ_self j),
      rwa [nat.sub_lt_iff hd hbj] at this } },
  have : j = b.nat_degree - (nat_degree b - j.succ).succ,
  { rw [← nat.succ_sub hbj, nat.succ_sub_succ, nat.sub_sub_self hbj.le] },
  convert congr_fun i_eq.symm ⟨nat_degree b - j.succ, hj⟩
end

lemma nat_degree_lt_of_degree_lt {f : polynomial K} (hf : f ≠ 0) {n : ℕ} (h : degree f < n) :
  nat_degree f < n :=
by rwa [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hf]

/-- If `A` is a family of enough elements, there is a pair of elements in `A`
(not necessarily distinct), such that their difference has small degree. -/
lemma exists_approx {b : polynomial K} (hb : b ≠ 0) {ε : ℝ} (hε : 0 < ε)
  (A : fin (fintype.card K ^ (nat_ceil (- log ε / log (fintype.card K)))).succ → polynomial K) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ (card_pow_degree K (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree K b • ε :=
begin
  have hbε : 0 < card_pow_degree K b • ε,
  { rw [algebra.smul_def, ring_hom.eq_int_cast],
    exact mul_pos (int.cast_pos.mpr (absolute_value.pos _ hb)) hε },
  by_cases le_b : b.nat_degree ≤ nat_ceil (-log ε / log ↑(fintype.card K)),
  { obtain ⟨i₀, i₁, i_ne, mod_eq⟩ := exists_eq (le_refl _) b le_b (λ i, A i % b)
      (λ i, euclidean_domain.mod_lt (A i) hb),
    refine ⟨i₀, i₁, i_ne, _⟩,
    simp only at mod_eq,
    rwa [mod_eq, sub_self, absolute_value.map_zero, int.cast_zero] },
  rw not_le at le_b,
  obtain ⟨i₀, i₁, i_ne, deg_lt⟩ := exists_approx_aux (le_refl _) b (λ i, A i % b)
    (λ i, euclidean_domain.mod_lt (A i) hb),
  use [i₀, i₁, i_ne],
  by_cases h : A i₁ % b = A i₀ % b,
  { rwa [h, sub_self, absolute_value.map_zero, int.cast_zero] },
  have h' : A i₁ % b - A i₀ % b ≠ 0 := mt sub_eq_zero.mp h,
  rw [card_pow_degree_apply h', int.cast_pow, int.cast_coe_nat, card_pow_degree_apply hb,
      algebra.smul_def, ring_hom.eq_int_cast, int.cast_pow, int.cast_coe_nat],
  have deg_lt' : (nat_degree (A i₁ % b - A i₀ % b) : ℝ) <
    b.nat_degree + log ε / log (fintype.card K),
  { refine lt_of_lt_of_le (nat.cast_lt.mpr (nat_degree_lt_of_degree_lt h' deg_lt)) _,
    rw [← sub_neg_eq_add, neg_div],
    refine le_trans _ (sub_le_sub_left (le_nat_ceil _) (b.nat_degree : ℝ)),
    rw ← neg_div,
    exact le_of_eq (nat.cast_sub le_b.le) },
  rw [← rpow_nat_cast, ← rpow_nat_cast],
  refine lt_of_lt_of_le (rpow_lt_rpow_of_exponent_lt _ deg_lt') _,
  { simpa using one_lt_card K },
  conv_rhs { rw ← exp_log hε },
  have hK' : (0 : ℝ) < fintype.card K,
  { rw [← @nat.cast_zero ℝ, nat.cast_lt, fintype.card_pos_iff],
    exact ⟨0⟩ },
  rw [rpow_def_of_pos hK', rpow_def_of_pos hK', ← exp_add, mul_add, mul_div_cancel'],
  refine ne_of_gt (log_pos _),
  rw [← nat.cast_one, nat.cast_lt],
  exact one_lt_card K
end
.

lemma card_pow_degree_anti_archimedean {x y z : polynomial K} {a : ℝ}
  (hxy : (card_pow_degree K (x - y) : ℝ) < a) (hyz : (card_pow_degree K (y - z) : ℝ) < a) :
  (card_pow_degree K (x - z) : ℝ) < a :=
begin
  have ha : 0 < a := lt_of_le_of_lt (int.cast_nonneg.mpr (absolute_value.nonneg _ _)) hxy,
  by_cases hxy' : x = y,
  { rwa hxy' },
  by_cases hyz' : y = z,
  { rwa ← hyz' },
  by_cases hxz' : x = z,
  { rwa [hxz', sub_self, absolute_value.map_zero, int.cast_zero] },
  rw [← ne.def, ← sub_ne_zero] at hxy' hyz' hxz',
  refine lt_of_le_of_lt _ (max_lt hxy hyz),
  rw [card_pow_degree_apply hxz', card_pow_degree_apply hxy', card_pow_degree_apply hyz'],
  have : (1 : ℝ) ≤ fintype.card K := by simpa using (one_lt_card K).le,
  simp only [int.cast_pow, int.cast_coe_nat, le_max_iff],
  refine or.imp (pow_le_pow this) (pow_le_pow this) _,
  rw [nat_degree_le_iff_degree_le, nat_degree_le_iff_degree_le, ← le_max_iff,
      ← degree_eq_nat_degree hxy', ← degree_eq_nat_degree hyz'],
  convert degree_add_le (x - y) (y - z) using 2,
  exact (sub_add_sub_cancel _ _ _).symm
end

/-- A slightly stronger version of `exists_partition` on which we perform induction on `n`. -/
lemma exists_partition_aux (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : polynomial K} (hb : b ≠ 0)
  (A : fin n → polynomial K) :
  ∃ (t : fin n → fin (fintype.card K ^ nat_ceil (-log ε / log ↑(fintype.card K)))),
  ∀ (i₀ i₁ : fin n),
  t i₀ = t i₁ ↔ (card_pow_degree K (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree K b • ε :=
begin
  have hbε : 0 < card_pow_degree K b • ε,
  { rw [algebra.smul_def, ring_hom.eq_int_cast],
    exact mul_pos (int.cast_pos.mpr (absolute_value.pos _ hb)) hε },
  induction n with n ih,
  { refine ⟨fin_zero_elim, fin_zero_elim⟩ },
  obtain ⟨t', ht'⟩ := ih (fin.tail A),
  suffices : ∃ j,
    ∀ i, t' i = j ↔ (card_pow_degree K (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree K b • ε,
  { obtain ⟨j, hj⟩ := this,
    refine ⟨fin.cons j t', λ i₀ i₁, _⟩,
    refine fin.cases _ (λ i₀, _) i₀; refine fin.cases _ (λ i₁, _) i₁,
    { simpa using hbε },
    { rw [fin.cons_succ, fin.cons_zero, eq_comm, absolute_value.sub_comm],
      exact hj i₁ },
    { rw [fin.cons_succ, fin.cons_zero],
      exact hj i₀ },
    { rw [fin.cons_succ, fin.cons_succ],
      exact ht' i₀ i₁ } },
  have approx_of_approx : ∀ (i : fin n),
    (card_pow_degree K (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree K b • ε →
    ∀ i', t' i' = t' i →
    (card_pow_degree K (A 0 % b - A i'.succ % b) : ℝ) < card_pow_degree K b • ε,
  { intros i hi i' hi',
    exact card_pow_degree_anti_archimedean hi ((ht' _ _).mp hi') },
  by_cases exists_nonempty_j : ∃ j, (∃ i, t' i = j) ∧
    ∀ i, t' i = j → (card_pow_degree K (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree K b • ε,
  { obtain ⟨j, ⟨i, hi⟩, hj⟩ := exists_nonempty_j,
    refine ⟨j, λ i', ⟨hj i', λ hi', trans ((ht' _ _).mpr _) hi⟩⟩,
    apply card_pow_degree_anti_archimedean _ hi',
    rw absolute_value.sub_comm,
    exact hj _ hi },
  obtain ⟨j, hj⟩ : ∃ j, ∀ (i : fin n), t' i = j →
    (card_pow_degree K (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree K b • ε,
  { by_contra this,
    push_neg at this,
    obtain ⟨j₀, j₁, j_ne, approx⟩ := exists_approx hb hε
      (fin.cons (A 0) (λ j, A (fin.succ (classical.some (this j))))),
    revert j_ne approx,
    refine fin.cases _ (λ j₀, _) j₀; refine fin.cases (λ j_ne approx, _) (λ j₁ j_ne approx, _) j₁,
    { exact absurd rfl j_ne },
    { rw [fin.cons_succ, fin.cons_zero, ← not_le, absolute_value.sub_comm] at approx,
      have := (classical.some_spec (this j₁)).2,
      contradiction },
    { rw [fin.cons_succ, fin.cons_zero, ← not_le] at approx,
      have := (classical.some_spec (this j₀)).2,
      contradiction },
    { rw [fin.cons_succ, fin.cons_succ] at approx,
      rw [ne.def, fin.succ_inj] at j_ne,
      have : j₀ = j₁ :=
      trans (classical.some_spec (this j₀)).1.symm
      (trans ((ht' (classical.some (this j₀)) (classical.some (this j₁))).mpr approx)
      (classical.some_spec (this j₁)).1),
      contradiction } },
  refine ⟨j, λ i, ⟨hj i, λ hi, _⟩⟩,
  have := exists_nonempty_j ⟨t' i, ⟨i, rfl⟩, approx_of_approx _ hi⟩,
  contradiction
end

lemma exists_partition (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : polynomial K} (hb : b ≠ 0)
  (A : fin n → polynomial K) :
  ∃ (t : fin n → fin (fintype.card K ^ nat_ceil (-log ε / log ↑(fintype.card K)))),
    ∀ (i₀ i₁ : fin n), t i₀ = t i₁ →
      (card_pow_degree K (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree K b • ε :=
begin
  obtain ⟨t, ht⟩ := exists_partition_aux n hε hb A,
  exact ⟨t, λ i₀ i₁ hi, (ht i₀ i₁).mp hi⟩
end

noncomputable def admissible_char_pow_degree : admissible_absolute_value (polynomial K) :=
{ map_lt_map_iff' := λ p q, begin
    by_cases hp : p = 0; by_cases hq : q = 0,
    { simp [hp, hq, euclidean_domain.r] },
    { simp [hp, hq, euclidean_domain.r, absolute_value.pos_iff, bot_lt_iff_ne_bot, degree_eq_bot] },
    { simpa [hp, hq, euclidean_domain.r, absolute_value.pos_iff, bot_lt_iff_ne_bot, degree_eq_bot]
        using (card_pow_degree K).nonneg p },
    { simp only [card_pow_degree_apply hp, card_pow_degree_apply hq, euclidean_domain.r,
                 mul_hom.to_fun_eq_coe, coe_to_mul_hom],
      rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq, with_bot.coe_lt_coe, pow_lt_pow_iff],
      exact_mod_cast one_lt_card K },
  end,
  card := λ ε, fintype.card K ^ (nat_ceil (- log ε / log (fintype.card K))),
  exists_partition' := λ n ε hε b hb, exists_partition n hε hb,
  .. card_pow_degree K }

end polynomial
