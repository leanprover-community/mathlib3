/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.polynomial.degree.card_pow_degree
import field_theory.finite.basic
import number_theory.class_number.admissible_absolute_value

/-!
# Admissible absolute values on polynomials
This file defines an admissible absolute value
`polynomial.card_pow_degree_is_admissible` which we use to show the class number
of the ring of integers of a function field is finite.

## Main results

* `polynomial.card_pow_degree_is_admissible` shows `card_pow_degree`,
  mapping `p : polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

namespace polynomial

open absolute_value real

variables {Fq : Type*} [field Fq] [fintype Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite field, there is a
pair of equal elements in `A`. -/
lemma exists_eq_polynomial {d : ℕ} {m : ℕ} (hm : fintype.card Fq ^ d ≤ m) (b : polynomial Fq)
  (hb : nat_degree b ≤ d) (A : fin m.succ → polynomial Fq) (hA : ∀ i, degree (A i) < degree b) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ :=
begin
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `0`, ... `degree b - 1` ≤ `d - 1`.
  -- In other words, the following map is not injective:
  set f : fin m.succ → (fin d → Fq) := λ i j, (A i).coeff j,
  have : fintype.card (fin d → Fq) < fintype.card (fin m.succ),
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
  exact lt_of_lt_of_le (coe_lt_degree.mp hbj) hb
end

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree. -/
lemma exists_approx_polynomial_aux {d : ℕ} {m : ℕ} (hm : fintype.card Fq ^ d ≤ m)
  (b : polynomial Fq) (A : fin m.succ → polynomial Fq) (hA : ∀ i, degree (A i) < degree b) :
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
  set f : fin m.succ → (fin d → Fq) := λ i j, (A i).coeff (nat_degree b - j.succ),
  have : fintype.card (fin d → Fq) < fintype.card (fin m.succ),
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
    { exact lt_of_le_of_lt sub_le_self' hd },
    { rw not_lt at hd,
      have := lt_of_le_of_lt hj (nat.lt_succ_self j),
      rwa [sub_lt_iff_sub_lt hd hbj] at this } },
  have : j = b.nat_degree - (nat_degree b - j.succ).succ,
  { rw [← nat.succ_sub hbj, nat.succ_sub_succ, nat.sub_sub_self hbj.le] },
  convert congr_fun i_eq.symm ⟨nat_degree b - j.succ, hj⟩
end

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together. -/
lemma exists_approx_polynomial {b : polynomial Fq} (hb : b ≠ 0)
  {ε : ℝ} (hε : 0 < ε)
  (A : fin (fintype.card Fq ^ nat_ceil (- log ε / log (fintype.card Fq))).succ → polynomial Fq) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ (card_pow_degree (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree b • ε :=
begin
  have hbε : 0 < card_pow_degree b • ε,
  { rw [algebra.smul_def, ring_hom.eq_int_cast],
    exact mul_pos (int.cast_pos.mpr (absolute_value.pos _ hb)) hε },
  have one_lt_q : 1 < fintype.card Fq := fintype.one_lt_card,
  have one_lt_q' : (1 : ℝ) < fintype.card Fq, { assumption_mod_cast },
  have q_pos : 0 < fintype.card Fq, { linarith },
  have q_pos' : (0 : ℝ) < fintype.card Fq, { assumption_mod_cast },
  -- If `b` is already small enough, then the remainders are equal and we are done.
  by_cases le_b : b.nat_degree ≤ nat_ceil (-log ε / log ↑(fintype.card Fq)),
  { obtain ⟨i₀, i₁, i_ne, mod_eq⟩ := exists_eq_polynomial (le_refl _) b le_b (λ i, A i % b)
      (λ i, euclidean_domain.mod_lt (A i) hb),
    refine ⟨i₀, i₁, i_ne, _⟩,
    simp only at mod_eq,
    rwa [mod_eq, sub_self, absolute_value.map_zero, int.cast_zero] },
  -- Otherwise, it suffices to choose two elements whose difference is of small enough degree.
  rw not_le at le_b,
  obtain ⟨i₀, i₁, i_ne, deg_lt⟩ := exists_approx_polynomial_aux (le_refl _) b (λ i, A i % b)
    (λ i, euclidean_domain.mod_lt (A i) hb),
  simp only at deg_lt,
  use [i₀, i₁, i_ne],
  -- Again, if the remainders are equal we are done.
  by_cases h : A i₁ % b = A i₀ % b,
  { rwa [h, sub_self, absolute_value.map_zero, int.cast_zero] },
  have h' : A i₁ % b - A i₀ % b ≠ 0 := mt sub_eq_zero.mp h,
  -- If the remainders are not equal, we'll show their difference is of small degree.
  -- In particular, we'll show the degree is less than the following:
  suffices : (nat_degree (A i₁ % b - A i₀ % b) : ℝ) <
    b.nat_degree + log ε / log (fintype.card Fq),
  { rwa [← real.log_lt_log_iff (int.cast_pos.mpr (card_pow_degree.pos h')) hbε,
        card_pow_degree_nonzero _ h', card_pow_degree_nonzero _ hb,
        algebra.smul_def, ring_hom.eq_int_cast,
        int.cast_pow, int.cast_coe_nat, int.cast_pow, int.cast_coe_nat,
        log_mul (pow_ne_zero _ q_pos'.ne') hε.ne',
        ← rpow_nat_cast, ← rpow_nat_cast, log_rpow q_pos', log_rpow q_pos',
        ← lt_div_iff (log_pos one_lt_q'), add_div, mul_div_cancel _ (log_pos one_lt_q').ne'] },
  -- And that result follows from manipulating the result from `exists_approx_polynomial_aux`
  -- to turn the `- ceil (- stuff)` into `+ stuff`.
  refine lt_of_lt_of_le (nat.cast_lt.mpr (with_bot.coe_lt_coe.mp _)) _,
  swap, { convert deg_lt, rw degree_eq_nat_degree h' },
  rw [← sub_neg_eq_add, neg_div],
  refine le_trans _ (sub_le_sub_left (le_nat_ceil _) (b.nat_degree : ℝ)),
  rw ← neg_div,
  exact le_of_eq (nat.cast_sub le_b.le)
end

/-- If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as close. -/
lemma card_pow_degree_anti_archimedean {x y z : polynomial Fq} {a : ℤ}
  (hxy : card_pow_degree (x - y) < a) (hyz : card_pow_degree (y - z) < a) :
  card_pow_degree (x - z) < a :=
begin
  have ha : 0 < a := lt_of_le_of_lt (absolute_value.nonneg _ _) hxy,
  by_cases hxy' : x = y,
  { rwa hxy' },
  by_cases hyz' : y = z,
  { rwa ← hyz' },
  by_cases hxz' : x = z,
  { rwa [hxz', sub_self, absolute_value.map_zero] },
  rw [← ne.def, ← sub_ne_zero] at hxy' hyz' hxz',
  refine lt_of_le_of_lt _ (max_lt hxy hyz),
  rw [card_pow_degree_nonzero _ hxz', card_pow_degree_nonzero _ hxy',
      card_pow_degree_nonzero _ hyz'],
  have : (1 : ℤ) ≤ fintype.card Fq, { exact_mod_cast (@fintype.one_lt_card Fq _ _).le },
  simp only [int.cast_pow, int.cast_coe_nat, le_max_iff],
  refine or.imp (pow_le_pow this) (pow_le_pow this) _,
  rw [nat_degree_le_iff_degree_le, nat_degree_le_iff_degree_le, ← le_max_iff,
      ← degree_eq_nat_degree hxy', ← degree_eq_nat_degree hyz'],
  convert degree_add_le (x - y) (y - z) using 2,
  exact (sub_add_sub_cancel _ _ _).symm
end

/-- A slightly stronger version of `exists_partition` on which we perform induction on `n`:
for all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into equivalence classes, where the equivalence(!) relation is "closer than `ε`". -/
lemma exists_partition_polynomial_aux (n : ℕ) {ε : ℝ} (hε : 0 < ε)
  {b : polynomial Fq} (hb : b ≠ 0) (A : fin n → polynomial Fq) :
  ∃ (t : fin n → fin (fintype.card Fq ^ nat_ceil (-log ε / log ↑(fintype.card Fq)))),
  ∀ (i₀ i₁ : fin n),
  t i₀ = t i₁ ↔ (card_pow_degree (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree b • ε :=
begin
  have hbε : 0 < card_pow_degree b • ε,
  { rw [algebra.smul_def, ring_hom.eq_int_cast],
    exact mul_pos (int.cast_pos.mpr (absolute_value.pos _ hb)) hε },
  -- We go by induction on the size `A`.
  induction n with n ih,
  { refine ⟨fin_zero_elim, fin_zero_elim⟩ },

  -- Show `anti_archimedean` also holds for real distances.
  have anti_archim' : ∀ {i j k} {ε : ℝ}, (card_pow_degree (A i % b - A j % b) : ℝ) < ε →
    (card_pow_degree (A j % b - A k % b) : ℝ) < ε → (card_pow_degree (A i % b - A k % b) : ℝ) < ε,
  { intros i j k ε,
    rw [← lt_ceil, ← lt_ceil, ← lt_ceil],
    exact card_pow_degree_anti_archimedean },

  obtain ⟨t', ht'⟩ := ih (fin.tail A),
  -- We got rid of `A 0`, so determine the index `j` of the partition we'll re-add it to.
  suffices : ∃ j,
    ∀ i, t' i = j ↔ (card_pow_degree (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree b • ε,
  { obtain ⟨j, hj⟩ := this,
    refine ⟨fin.cons j t', λ i₀ i₁, _⟩,
    refine fin.cases _ (λ i₀, _) i₀; refine fin.cases _ (λ i₁, _) i₁,
    { simpa using hbε },
    { rw [fin.cons_succ, fin.cons_zero, eq_comm, absolute_value.map_sub],
      exact hj i₁ },
    { rw [fin.cons_succ, fin.cons_zero],
      exact hj i₀ },
    { rw [fin.cons_succ, fin.cons_succ],
      exact ht' i₀ i₁ } },
  -- `exists_approx_polynomial` guarantees that we can insert `A 0` into some partition `j`,
  -- but not that `j` is uniquely defined (which is needed to keep the induction going).
  obtain ⟨j, hj⟩ : ∃ j, ∀ (i : fin n), t' i = j →
    (card_pow_degree (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree b • ε,
  { by_contra this, push_neg at this,
    obtain ⟨j₀, j₁, j_ne, approx⟩ := exists_approx_polynomial hb hε
      (fin.cons (A 0) (λ j, A (fin.succ (classical.some (this j))))),
    revert j_ne approx,
    refine fin.cases _ (λ j₀, _) j₀; refine fin.cases (λ j_ne approx, _) (λ j₁ j_ne approx, _) j₁,
    { exact absurd rfl j_ne },
    { rw [fin.cons_succ, fin.cons_zero, ← not_le, absolute_value.map_sub] at approx,
      have := (classical.some_spec (this j₁)).2,
      contradiction },
    { rw [fin.cons_succ, fin.cons_zero, ← not_le] at approx,
      have := (classical.some_spec (this j₀)).2,
      contradiction },
    { rw [fin.cons_succ, fin.cons_succ] at approx,
      rw [ne.def, fin.succ_inj] at j_ne,
      have : j₀ = j₁ :=
        (classical.some_spec (this j₀)).1.symm.trans
        (((ht' (classical.some (this j₀)) (classical.some (this j₁))).mpr approx).trans
        (classical.some_spec (this j₁)).1),
      contradiction } },
  -- However, if one of those partitions `j` is inhabited by some `i`, then this `j` works.
  by_cases exists_nonempty_j : ∃ j, (∃ i, t' i = j) ∧
    ∀ i, t' i = j → (card_pow_degree (A 0 % b - A i.succ % b) : ℝ) < card_pow_degree b • ε,
  { obtain ⟨j, ⟨i, hi⟩, hj⟩ := exists_nonempty_j,
    refine ⟨j, λ i', ⟨hj i', λ hi', trans ((ht' _ _).mpr _) hi⟩⟩,
    apply anti_archim' _ hi',
    rw absolute_value.map_sub,
    exact hj _ hi },
  -- And otherwise, we can just take any `j`, since those are empty.
  refine ⟨j, λ i, ⟨hj i, λ hi, _⟩⟩,
  have := exists_nonempty_j ⟨t' i, ⟨i, rfl⟩, λ i' hi', anti_archim' hi ((ht' _ _).mp hi')⟩,
  contradiction
end

/-- For all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into classes, where all remainders in a class are close together. -/
lemma exists_partition_polynomial (n : ℕ) {ε : ℝ} (hε : 0 < ε)
  {b : polynomial Fq} (hb : b ≠ 0) (A : fin n → polynomial Fq) :
  ∃ (t : fin n → fin (fintype.card Fq ^ nat_ceil (-log ε / log ↑(fintype.card Fq)))),
    ∀ (i₀ i₁ : fin n), t i₀ = t i₁ →
      (card_pow_degree (A i₁ % b - A i₀ % b) : ℝ) < card_pow_degree b • ε :=
begin
  obtain ⟨t, ht⟩ := exists_partition_polynomial_aux n hε hb A,
  exact ⟨t, λ i₀ i₁ hi, (ht i₀ i₁).mp hi⟩
end

/-- `λ p, fintype.card Fq ^ degree p` is an admissible absolute value.
We set `q ^ degree 0 = 0`. -/
noncomputable def card_pow_degree_is_admissible :
  is_admissible (card_pow_degree : absolute_value (polynomial Fq) ℤ) :=
{ card := λ ε, fintype.card Fq ^ (nat_ceil (- log ε / log (fintype.card Fq))),
  exists_partition' := λ n ε hε b hb, exists_partition_polynomial n hε hb,
  .. @card_pow_degree_is_euclidean Fq _ _ }

end polynomial
