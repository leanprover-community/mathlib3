/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.nat.prime
import data.nat.mul_ind
import data.nat.factorization

/-!
# Prime factorizations

 `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : ℕ`.

-/

open nat finset list finsupp
open_locale big_operators
open_locale nat  -- to enable φ notation

namespace nat

/-- For `n > 0`, the product of `p_i ^ k_i` over the prime factorization of `n` equals `n` -/
lemma factorization_prod_pow {n : ℕ} (hn : 0 < n) :
  n = n.factorization.prod pow :=
begin
  rw ←finsupp.prod_to_multiset,
  simp only [factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  exact (prod_factors hn).symm,
end

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- If a product over `n.factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.to_finset` -/
lemma rebase_prod_factorization {n : ℕ} {β : Type*} [comm_monoid β] (f : ℕ → β) :
  n.factorization.prod (λ p k, f p) = ∏ p in n.factors.to_finset, (f p) :=
by { apply prod_congr support_factorization, simp }

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- For disjoint `f1` and `f2`, and function `g`
the product of `g x (f1 x + f2 x))` over `f1.support` equals the product of `g` over `f1.support` -/
lemma disjoint_prod_add_aux {f1 f2 : ℕ →₀ ℕ} (hd : disjoint f1.support f2.support)
  {β : Type*} [comm_monoid β] {g : ℕ → ℕ → β} :
(∏ (x : ℕ) in f1.support, g x (f1 x + f2 x)) = f1.prod g :=
begin
  unfold finsupp.prod,
  rw prod_congr rfl,
  intros x hx,
  simp only [not_mem_support_iff.mp (finset.disjoint_left.mp hd hx), add_zero],
end

lemma disjoint_prod_add {f1 f2 : ℕ →₀ ℕ} (hd : disjoint f1.support f2.support)
  {β : Type*} [comm_monoid β] {g : ℕ → ℕ → β} :
  f1.prod g * f2.prod g = (f1 + f2).prod g :=
begin
  rw [←disjoint_prod_add_aux hd, ←disjoint_prod_add_aux (disjoint.comm.mp hd)],
  simp only [add_comm, finsupp.prod, support_add_eq hd, prod_union hd, add_apply],
end

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- For any multiplicative function `f` with `f 1 = 1` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the prime factorization of `n` -/
lemma multiplicative_factorization {n : ℕ} {β : Type*} [comm_monoid β] {f : ℕ → β}
  (hn : 0 < n)
  (h_mult : ∀ x y : ℕ, coprime x y → f(x * y) = f x * f y)
  (hf : f 1 = 1) :
f n = n.factorization.prod (λ p k, f(p ^ k)) :=
begin
  apply @nat.rec_on_pos_prime_coprime
    (λ n, (0 < n) → (f n = n.factorization.prod (λ p k, f(p ^ k)))),

  -- Case for positive prime power p^k
  { intros p k hp hk hpk,
    rw factorization_prime_pow hp,
    rw finsupp.prod_single_index _,
    simpa using hf },

  -- Case for 0, trivially
  { simp },

  -- Case for 1
  { rintros -, rw [factorization_one, hf], simp },

  -- Case for coprime a and b
  { intros a b hab ha hb hab_pos,
    rw h_mult a b hab,
    rw ha (pos_of_mul_pos_right hab_pos (b.zero_le)),
    rw hb (pos_of_mul_pos_left hab_pos (a.zero_le)),
    rw factorization_mul_add_of_coprime hab,
    apply disjoint_prod_add (factorization_disjoint_of_coprime hab) },

  exact hn,
end

---------------------------------------------------------------------------------------------------

/-- If the factorization of `n` contains just one prime `p` then `n` is a power of `p` -/
lemma prime_pow_of_factorization_single {n p k : ℕ} (hn : 0 < n)
  (h : n.factorization = single p k) : n = p ^ k :=
by { rw [factorization_prod_pow hn, h], simp }

---------------------------------------------------------------------------------------------------


end nat
