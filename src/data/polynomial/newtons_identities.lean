/-
Copyright (c) 2022 Xialu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xialu Zheng, Kevin Buzzard
-/
import data.polynomial.degree.lemmas
import data.mv_polynomial.comm_ring
import algebra.polynomial.big_operators

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

-- lemma p_def (n : ℕ) : p R n = ∑ i : fin n, (mv_polynomial.X i) ^ k :=

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

/-- attempt to prove the inductive step -/
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
    exact nat_degree_X_sub_C_le, },
end

lemma newt_nk (h : n = k) : ∑ j in range (k + 1), s R n j * p R n j = 0 :=
begin
  subst h,
  unfold p,
  have hs : ∑ (x : ℕ) in range (n + 1), s R n x * ∑ (i : fin n), mv_polynomial.X i ^ x = ∑ (x : ℕ) in range (n + 1), ∑ (i : fin n), s R n x * mv_polynomial.X i ^ x,
  {
    rw finset.sum_congr,
    refl,
    intros x hx,
    rw finset.mul_sum,
  },
  rw hs,
  clear hs,
  rw finset.sum_comm,
  rw finset.sum_eq_zero,
  intro j,
  simp,
  apply sumzero,
end


/-- Newton's symmetric function identities -/
lemma newt : (∑ j in range k, s R n j * p R n (k - j)) + k * p R n 0 = 0 :=
begin
  sorry
  -- this will be quite a challenge!
end

end symmetric
end polynomial
