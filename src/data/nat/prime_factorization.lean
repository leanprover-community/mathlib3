/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.nat.prime
import data.nat.mul_ind

/-!
# Prime factorizations

 `n.prime_factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `prime_factorization 2000 2` is 4
  * `prime_factorization 2000 5` is 3
  * `prime_factorization 2000 k` is 0 for all other `k : ℕ`.

-/

open nat finset list finsupp
open_locale big_operators
open_locale nat  -- to enable φ notation

namespace nat

/-- `n.prime_factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
noncomputable def prime_factorization (n : ℕ) : ℕ →₀ ℕ := (n.factors : multiset ℕ).to_finsupp

lemma prime_factorization_count {n p : ℕ} : n.prime_factorization p = list.count p n.factors :=
by simp [prime_factorization]

/-- Every positive natural number has a unique prime factorization -/
lemma prime_factorization_eq_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  a.prime_factorization = b.prime_factorization ↔ a = b :=
⟨λ h, eq_of_count_factors_eq ha hb (λ p, by simp [←prime_factorization_count, h]), λ h, by rw h⟩

/-- For `n > 0`, the product of `p_i ^ k_i` over the prime factorization of `n` equals `n` -/
lemma prime_factorization_prod_pow {n : ℕ} (hn : 0 < n) :
  n = n.prime_factorization.prod pow :=
begin
  rw ←finsupp.prod_to_multiset,
  simp only [prime_factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  exact (prod_factors hn).symm,
end

@[simp] lemma prime_factorization_zero : prime_factorization 0 = 0  :=
by simp [prime_factorization]

@[simp] lemma prime_factorization_one : prime_factorization 1 = 0 :=
by simp [prime_factorization]

/-- The support of `n.prime_factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_prime_factorization {n : ℕ} :
  n.prime_factorization.support = n.factors.to_finset :=
by simpa [prime_factorization, multiset.to_finsupp_support]

lemma factor_iff_mem_factorization {n p : ℕ} :
  (p ∈ n.prime_factorization.support) ↔ (p ∈ n.factors) :=
by simp only [support_prime_factorization, list.mem_to_finset]

/-- The only numbers with empty prime factorization are 0 and 1 -/
lemma prime_factorization_eq_nil_iff (n : ℕ) : n.prime_factorization = 0 ↔ n = 0 ∨ n = 1 :=
by simp [prime_factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
lemma prime_factorization_pow {n k : ℕ} :
  prime_factorization (n^k) = k • n.prime_factorization :=
begin
  ext p,
  simp only [algebra.id.smul_eq_mul, finsupp.coe_smul, pi.smul_apply],
  simp only [prime_factorization_count, factors_count_pow],
end

/-- The only prime factor of prime `p` is `p` itself, with multiplicity 1 -/
@[simp] lemma prime_factorization_prime {p : ℕ} (hp : prime p) :
  p.prime_factorization = single p 1 :=
begin
  ext q,
  rw [prime_factorization_count, factors_prime hp],
  by_cases hqp : q = p,
  { rw hqp, simp },
  { rw finsupp.single_eq_of_ne (ne.symm hqp),
    exact count_eq_zero_of_not_mem ((not_iff_not_of_iff list.mem_singleton).mpr hqp) },
end

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
@[simp] lemma prime_factorization_prime_pow {p k : ℕ} (hp : prime p) :
  prime_factorization (p^k) = single p k :=
by simp [prime_factorization_pow, prime_factorization_prime hp]



---------------------------------------------------------------------------------------------------
-- Prime factorisations involving `coprime a b` and/or positive `a` and `b`
---------------------------------------------------------------------------------------------------

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
lemma prime_factorization_disjoint_of_coprime {a b : ℕ} (hab : coprime a b) :
  disjoint a.prime_factorization.support b.prime_factorization.support :=
begin
  simp only [support_prime_factorization],
  exact disjoint_to_finset_iff_disjoint.mpr (coprime_factors_disjoint hab),
end

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma prime_factorization_mul_add_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).prime_factorization = a.prime_factorization + b.prime_factorization :=
begin
  ext q,
  simp only [finsupp.coe_add, pi.add_apply, prime_factorization_count],
  simp only [count_factors_mul_of_coprime hab],
end

/-- For positive `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma prime_factorization_mul_add_of_pos {a b : ℕ}  (ha : 0 < a) (hb : 0 < b) :
  (a * b).prime_factorization = a.prime_factorization + b.prime_factorization :=
begin
  ext q,
  simp only [finsupp.coe_add, pi.add_apply, prime_factorization_count],
  simp only [count_factors_mul_of_pos ha hb],
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma prime_factorization_union_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).prime_factorization.support =
    a.prime_factorization.support ∪ b.prime_factorization.support
  :=
begin
  rw prime_factorization_mul_add_of_coprime hab,
  exact support_add_eq (prime_factorization_disjoint_of_coprime hab),
end

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- If a product over `n.prime_factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.to_finset` -/
lemma rebase_prod_prime_factorization {n : ℕ} {β : Type*} [comm_monoid β] (f : ℕ → β) :
  n.prime_factorization.prod (λ p k, f p) = ∏ p in n.factors.to_finset, (f p) :=
by { apply prod_congr support_prime_factorization, simp }

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
f n = n.prime_factorization.prod (λ p k, f(p ^ k)) :=
begin
  apply @nat.rec_on_pos_prime_coprime
    (λ n, (0 < n) → (f n = n.prime_factorization.prod (λ p k, f(p ^ k)))),

  -- Case for positive prime power p^k
  { intros p k hp hk hpk,
    rw prime_factorization_prime_pow hp,
    rw finsupp.prod_single_index _,
    simpa using hf },

  -- Case for 0, trivially
  { simp },

  -- Case for 1
  { rintros -, rw [prime_factorization_one, hf], simp },

  -- Case for coprime a and b
  { intros a b hab ha hb hab_pos,
    rw h_mult a b hab,
    rw ha (pos_of_mul_pos_right hab_pos (b.zero_le)),
    rw hb (pos_of_mul_pos_left hab_pos (a.zero_le)),
    rw prime_factorization_mul_add_of_coprime hab,
    apply disjoint_prod_add (prime_factorization_disjoint_of_coprime hab) },

  exact hn,
end

---------------------------------------------------------------------------------------------------

/-- If the prime_factorization of `n` contains just one prime `p` then `n` is a power of `p` -/
lemma prime_pow_of_prime_factorization_single {n p k : ℕ} (hn : 0 < n)
  (h : n.prime_factorization = single p k) : n = p ^ k :=
by { rw [prime_factorization_prod_pow hn, h], simp }

---------------------------------------------------------------------------------------------------


end nat
