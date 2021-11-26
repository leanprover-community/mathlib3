import data.nat.prime
import data.nat.mul_ind

open nat
open finset
open list
open finsupp

open_locale big_operators


---------------------------------------------------------------------------------------------------
-- This is in PR #10492:
/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma count_factors_mul_of_coprime {p a b : ℕ} (hab : coprime a b)  :
  list.count p (a * b).factors = list.count p a.factors + list.count p b.factors :=
by { rw [perm_iff_count.mp (perm_factors_mul_of_coprime hab) p, count_append] }
---------------------------------------------------------------------------------------------------
-- This is in PR #10493:
lemma eq_of_eq_count_factors {a b : ℕ} (ha: 0 < a) (hb: 0 < b)
  (h: ∀ (p : ℕ), count p a.factors = count p b.factors) : a = b :=
by { simpa [prod_factors ha, prod_factors hb] using perm.prod_eq (perm_iff_count.mpr h) }
---------------------------------------------------------------------------------------------------


/-! # Prime factorizations -/

namespace nat

/-- `n.prime_factorization` is the finitely supported function mapping factors of `n` to their multiplicities in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `prime_factorization 2000 2` is 4
  * `prime_factorization 2000 5` is 3
  * `prime_factorization 2000 k` is 0 for all other `k : ℕ`.
`prime_factorization` is noncomputable; if we need to compute the value we can use `list.count p n.factors`.
-/
noncomputable def prime_factorization (n : ℕ) : ℕ →₀ ℕ := (n.factors : multiset ℕ).to_finsupp

lemma prime_factorization_count {n p : ℕ} : n.prime_factorization p = list.count p n.factors :=
by { unfold prime_factorization, simp }

/-- Every positive natural number has a unique prime factorization -/
lemma prime_factorization_eq_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  a.prime_factorization = b.prime_factorization ↔ a = b :=
begin
  split,
  { intros h,
    refine eq_of_eq_count_factors ha hb (λ p, _),
    simp only [←prime_factorization_count, h] },
  { intros h, rw h },
end

lemma prime_factorization_zero : prime_factorization 0 = 0  :=
by { unfold prime_factorization, rw factors_zero, simp }

lemma prime_factorization_one : prime_factorization 1 = 0 :=
by { unfold prime_factorization, rw factors_one, simp }

/-- The support of `n.prime_factorization` is exactly `n.factors.to_finset` -/
lemma support_prime_factorization {n : ℕ} : n.prime_factorization.support = n.factors.to_finset :=
by { unfold prime_factorization, simpa only [multiset.to_finsupp_support] using rfl }

lemma factor_iff_mem_factorization {n p : ℕ} :
  (p ∈ n.prime_factorization.support) ↔ (p ∈ n.factors) :=
by simp only [support_prime_factorization, list.mem_to_finset]

/-- The only numbers with empty prime factorization are 0 and 1 -/
lemma prime_factorization_eq_nil_iff (n : ℕ) : n.prime_factorization = 0 ↔ n = 0 ∨ n = 1 :=
begin
  simp only [prime_factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero],
  exact (factors_eq_nil n),
end

/-- For prime `p` and `k > 0`, the only prime factor of `p^k` is `p` with multiplicity `k` -/
lemma prime_factorization_prime_pos_pow {p k : ℕ} (hp : prime p) (hk : 0 < k) :
  prime_factorization (p^k) = single p k :=
begin
  rw eq_single_iff,
  split,
  { simp only [support_prime_factorization, prime_pow_prime_divisor hk hp, finset.subset.refl] },
  { rw [prime_factorization_count, prime.factors_pow hp k, count_repeat p k] }
end

/-- The only prime factor of prime `p` is `p` itself with multiplicity 1 -/
lemma prime_factorization_prime {p : ℕ} (hp : prime p) : p.prime_factorization = single p 1 :=
by { simp only [←prime_factorization_prime_pos_pow hp one_pos, pow_one] }

---------------------------------------------------------------------------------------------------
-- Prime factorisations involving `coprime a b`
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
  simp only [finsupp.coe_add, pi.add_apply, prime_factorization_count, count_factors_mul_of_coprime hab],
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma prime_factorization_union_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).prime_factorization.support = a.prime_factorization.support ∪ b.prime_factorization.support
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

/-- For disjoint `f1` and `f2`, and function `g` with `∀ a, g a 0 = 1`,
the product of `g x (f1 x + f2 x))` over `f1.support` equals the product of `g` over `f1.support` -/
lemma disjoint_prod_add_aux {f1 f2 : ℕ →₀ ℕ} (hd : disjoint f1.support f2.support)
  {β : Type*} [comm_monoid β] {g : ℕ → ℕ → β} (hg_zero : ∀ (a : ℕ), g a 0 = 1) :
(∏ (x : ℕ) in f1.support, g x (f1 x + f2 x)) = f1.prod g
:=
begin
  unfold finsupp.prod,
  rw prod_congr rfl,
  intros x hx,
  simp only [not_mem_support_iff.mp (finset.disjoint_left.mp hd hx), add_zero],
end

lemma disjoint_prod_add {f1 f2 : ℕ →₀ ℕ} (hd : disjoint f1.support f2.support)
  {β : Type*} [comm_monoid β] {g : ℕ → ℕ → β} (hg_zero : ∀ (a : ℕ), g a 0 = 1) :
  f1.prod g * f2.prod g = (f1 + f2).prod g
:=
begin
  rw [←disjoint_prod_add_aux hd hg_zero, ←disjoint_prod_add_aux (disjoint.comm.mp hd) hg_zero],
  simp only [add_comm, finsupp.prod, support_add_eq hd, prod_union hd, add_apply],
end

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- For any multiplicative function `f` with `f 1 = 1` and any `n > 0`, we can evaluate `f n` by evaluating `f` at `p ^ k` over the prime factorization of `n` -/
lemma multiplicative_factorization {n : ℕ} {β : Type*} [comm_monoid β] {f : ℕ → β}
  (hn : 0 < n)
  (h_mult : ∀ x y : ℕ, coprime x y → f(x * y) = f x * f y)
  (hf : f 1 = 1) :
f n = n.prime_factorization.prod (λ p k, f(p ^ k))
:=
begin
  apply @nat.rec_on_pos_prime_coprime
    (λ n, (0 < n) → (f n = n.prime_factorization.prod (λ p k, f(p ^ k)))),

  -- Case for positive prime power p^k
  { intros p k hp hk hpk,
    rw prime_factorization_prime_pos_pow hp hk,
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
    apply disjoint_prod_add (prime_factorization_disjoint_of_coprime hab),
    simpa using hf,
  },

  exact hn,
end

---------------------------------------------------------------------------------------------------

/-- For `n > 0`, the product of `p_i ^ k_i` over the prime factorization of `n` equals `n` -/
lemma prime_factorization_prod_eq_self {n : ℕ} (hn : 0 < n) :
  n = n.prime_factorization.prod pow :=
by { refine (multiplicative_factorization hn _ _), simp }

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

end nat
