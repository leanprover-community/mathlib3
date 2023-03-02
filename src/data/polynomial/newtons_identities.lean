/-
Copyright (c) 2022 Xialu Zheng, Bendit Chan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xialu Zheng, Bendit Chan, Kevin Buzzard
-/
import data.polynomial.degree.lemmas
import data.mv_polynomial.comm_ring
import algebra.polynomial.big_operators
import ring_theory.mv_polynomial.symmetric
import ring_theory.polynomial.vieta
import ring_theory.power_series.basic

/-

# Newton's Identities

TODO: write something nice here

https://en.wikipedia.org/wiki/Newton%27s_identities

## Main definitions

(in namespace `polynomial.symmetric`)

`e R n k` is the `k`th symmetric polynomial in `n` variables with
coefficients in the commutative ring `R`.

`s R n k` is (-1)^k * e n k

`p R n k` is the sum of the k'th powers of the n polynomial variables

-/

namespace polynomial
namespace symmetric

variables (R : Type*) [comm_ring R] (n k : ℕ)


open_locale polynomial
open_locale big_operators
open finset polynomial

noncomputable def e : mv_polynomial (fin n) R :=
polynomial.coeff (∏ i : fin n, (X + C (mv_polynomial.X i))) k

noncomputable def s : mv_polynomial (fin n) R :=
polynomial.coeff (∏ i : fin n, (X - C (mv_polynomial.X i))) k

noncomputable def p : mv_polynomial (fin n) R :=
∑ i : fin n, (mv_polynomial.X i) ^ k

lemma s_symm : ∀ k : ℕ, k ≤ n → s R n k = (-1)^(n - k) * mv_polynomial.esymm (fin n) R (n - k) :=
begin
  intros k hk,
  rw [s, finset.prod, multiset.prod_X_sub_C_coeff', finset.esymm_map_val],
  congr;
  exact finset.card_fin n,
  change k ≤ finset.card _,
  rwa finset.card_fin n,
end

lemma p_zero : p R n 0 = n :=
begin
  unfold p,
  simp_rw pow_zero,
  norm_cast,
  rw ← card_eq_sum_ones,
  simp,
end

lemma nat_degree_le_one_iff (p : polynomial R) : p.nat_degree ≤ 1 ↔ ∃ a b,
p = C a * X + (C b) :=
begin
  split,
  { apply exists_eq_X_add_C_of_nat_degree_le_one },
  { rintro ⟨a, b, rfl⟩,
    rw nat_degree_add_le_iff_left,
    { rw mul_comm,
      transitivity,
      apply nat_degree_mul_C_le,
      apply nat_degree_X_le, },
    { simp, } },
end

lemma s_big (h : n < k) : s R n k = 0 :=
begin
  apply coeff_eq_zero_of_nat_degree_lt,
  refine lt_of_le_of_lt _ h,
  transitivity,
  apply nat_degree_prod_le,
  transitivity,
  apply sum_le_sum, swap, exact λ x, 1,
  { intros,
    rw nat_degree_le_one_iff,
    use [1,-mv_polynomial.X i],
    simp, ring, },
  { apply le_of_eq,
    simp, },
end


-- nedd to fix s_neg (h : k < 0) : s R n k = 0

-- n = k case
lemma sumzero : ∀ j : fin n, ∑ i in range (n + 1), s R n i * (mv_polynomial.X j)^i = 0 :=
begin
  intro j,
  unfold s,
  rw ← polynomial.eval_eq_sum_range',
  { rw eval_prod,
    apply finset.prod_eq_zero (show j ∈ univ, by simp),
    simp, },
  { rw nat.lt_add_one_iff,
    refine le_trans (polynomial.nat_degree_prod_le _ _) _,
    convert finset.sum_le_card_nsmul _ _ 1 _,
    simp,
    intros a ha,
    exact nat_degree_X_sub_C_le _, },
end

lemma newt_nk (h : n = k) : ∑ j in range (k + 1), s R n j * p R n j = 0 :=
begin
  subst h,
  unfold p,
  suffices : ∑ (x : ℕ) in range (n + 1), ∑ (i : fin n), s R n x * mv_polynomial.X i ^ x = 0,
  { rw [← this, finset.sum_congr rfl],
    exact λ x hx, finset.mul_sum, },
  rw [finset.sum_comm, finset.sum_eq_zero],
  intros j hj,
  apply sumzero,
end

-- n < k case
lemma newt_nltk (h : n < k) :  ∑ j in range (k + 1), s R n j * p R n j = 0 :=
begin
  have hk : k + 1 = (n + 1) + (k - n),
  { zify [le_of_lt h],
    ring, },
  rw [hk, finset.sum_range_add, newt_nk, zero_add],
  apply sum_eq_zero,
  intros x hx,
  rw s_big,
  simp, linarith, refl,
end

-- k < n case
noncomputable def f : mv_polynomial (fin n) R := (k - n) * s R n (n - k) + ∑ j in range (k + 1), s R n (n - k + j) * p R n j

-- try induction on m = n - k

lemma s_degree : ∀ j : ℕ, j ≤ n → (s R n j).total_degree ≤ n - j :=
begin
  intros j hj,
  casesI subsingleton_or_nontrivial R,
  {
    letI : unique (mv_polynomial (fin n) R), apply mv_polynomial.unique,
    have hs : s R n j = 0 := by simp,
    simp [hs, mv_polynomial.total_degree_zero],
  },
  {
    rw s_symm,
    have hd : (mv_polynomial.esymm (fin n) R (n - j)).total_degree ≤ n - j,
    {
      apply le_trans (mv_polynomial.total_degree_finset_sum _ _),
      rw finset.sup_le_iff,
      intros b hb,
      convert mv_polynomial.total_degree_finset_prod _ _,
      rw finset.mem_powerset_len at hb,
      simp [hb.2.symm],
    },
    apply le_trans (mv_polynomial.total_degree_mul _ _),
    have := neg_one_pow_eq_or (mv_polynomial (fin n) R) (n-j),
    cases this;
    rw this;
    simp;
    exact hd,
    exact hj,
  },
end

lemma p_degree : ∀ j : ℕ, (p R n j).total_degree ≤ j :=
begin
  intro j,
  casesI subsingleton_or_nontrivial R,
  {
    letI : unique (mv_polynomial (fin n) R), apply mv_polynomial.unique,
    have hp : p R n j = 0 := by simp,
    simp [hp, mv_polynomial.total_degree_zero],
  },
  {
    apply le_trans (mv_polynomial.total_degree_finset_sum _ _),
    simp,
  },
end

lemma newt_degree (h : k ≤ n): (f R n k).total_degree ≤ k :=
begin
  apply le_trans (mv_polynomial.total_degree_add _ _),
  rw max_le_iff,
  split,
  {
    apply le_trans (mv_polynomial.total_degree_mul _ _),
    have h' : n - k ≤ n,
    { zify, simp, },
    apply le_trans (add_le_add _ (s_degree R n (n - k) h')) _,
    exact 0,
    { zify,
      simp,
      apply nat.eq_zero_of_le_zero,
      apply le_trans (mv_polynomial.total_degree_sub _ _),
      simp,
      exact ⟨mv_polynomial.total_degree_C k, mv_polynomial.total_degree_C n⟩, },
    { simp,
      zify,
      ring_nf,  }
  },
  {
    apply le_trans (mv_polynomial.total_degree_finset_sum _ _),
    rw finset.sup_le_iff,
    intros j hj,
    apply le_trans (mv_polynomial.total_degree_mul _ _),
    have h' : n - k + j ≤ n,
    { zify,
      rw finset.mem_range at hj,
      linarith, },
    apply le_trans (add_le_add (s_degree R _ _ h') (p_degree R _ _)) _,
    apply le_of_eq,
    zify,
    ring,
  },
end

open_locale classical

-- (maybe shld be put into mv_polynomial api)
lemma mv_polynomial.dvd_iff (σ : Type*)  [fintype σ] (R : Type*) [comm_ring R] (p : mv_polynomial σ R) (i : σ): mv_polynomial.eval₂ mv_polynomial.C (λ t, if t = i then 0 else mv_polynomial.X t) p = 0 → mv_polynomial.X i ∣ p :=
begin
  sorry

end

lemma newt_divisible_by (h : f R (n - 1) k = 0) : ∀ (i : fin n), (mv_polynomial.X i) ∣ (f R n k) :=
begin
  intro i,
  -- have h0 : mv_polynomial.X i = 0 → f R n k = 0,
  -- {
  --   sorry
  -- },

  sorry,

end

lemma mv_polynomial.total_degree_esymm (σ : Type*)  [fintype σ]  [nontrivial R]  (n : ℕ) (hn : n ≤ fintype.card σ) :
  (mv_polynomial.esymm σ R n).total_degree = n :=
begin
  sorry
end


lemma newt_klen (h : k ≤ n) : f R n k = 0 :=
--∑ j in range (k + 1), s R n (n - k + j) * p R n j = (n - k) * s R n (n - k) :=
begin
  casesI subsingleton_or_nontrivial R,
  {
    letI : unique (mv_polynomial (fin n) R), apply mv_polynomial.unique,
    simp only [eq_iff_true_of_subsingleton],
  },
  {
    induction h' : n - k with i hi generalizing n k,
    { have := (tsub_eq_zero_iff_le.mp h').antisymm h,
      unfold f,
      simp [newt_nk, this], },
    {
      have hle : k ≤ n - 1,
      { have := nat.succ_pos i,
        rw ← h' at this,
        suffices : k + 1 ≤ n,
        exact le_tsub_of_add_le_right this,
        linarith, },
      have hnk : (n - 1) - k = i,
      { rw [nat.succ_eq_add_one, nat.sub_eq_iff_eq_add h] at h',
        rwa [tsub_tsub, nat.sub_eq_iff_eq_add, ← nat.add_assoc],
        linarith, },
      specialize hi (n - 1) k hle hnk,
      have hdiv' : s R n 0 ∣ (f R n k),
      {
        sorry
      },
      have hdiv := exists_eq_mul_right_of_dvd hdiv',
      clear hdiv',
      cases hdiv with g hg,
      by_contra he,
      have hn : (f R n k).total_degree = (s R n 0).total_degree + g.total_degree,
      {
        sorry
      },
      simp [s_symm] at hn,
      rw [show ((-1) ^ n * mv_polynomial.esymm (fin n) R n).total_degree =
         (mv_polynomial.esymm (fin n) R n).total_degree, from _, mv_polynomial.total_degree_esymm] at hn,
      work_on_goal 2 { simp only [fintype.card_fin], },
      work_on_goal 2 {
        cases neg_one_pow_eq_or _ n;
        rw [h_2]; simp,
        },
      have hl := le_trans (le_trans (le_of_eq hn.symm) (newt_degree _ _ _ h)) hle,
      have gdeg : 0 ≤ g.total_degree := nat.zero_le _,
      simp only [tsub_zero] at hl,
      have H := add_le_add le_rfl gdeg,
      swap, use n,
      have H' := le_trans H hl,
      cases n,
      norm_num at H',
      rw nat.succ_sub_one at H',
      exact nat.not_succ_le_self n H',
      },
  },
end

/-- Newton's symmetric function identities -/
lemma newt : f R n k = 0 :=
begin
  by_cases n < k,
  { have := newt_nltk,
    specialize this R n k h,
    unfold f,
    rw ← this,
    sorry
  },
  { push_neg at h,
    exact newt_klen R n k h, },
end

end symmetric
end polynomial
