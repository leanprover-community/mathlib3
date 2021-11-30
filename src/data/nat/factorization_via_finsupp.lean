import data.nat.prime
import data.nat.mul_ind
import tactic.omega

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
-- This is in pending PR #10536:
lemma count_factors_mul_of_pos {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  list.count p (a * b).factors = list.count p a.factors + list.count p b.factors :=
by rw [perm_iff_count.mp (perm_factors_mul_of_pos ha hb) p, count_append]

---------------------------------------------------------------------------------------------------
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

/-- The only prime factor of prime `p` is `p` itself, with multiplicity 1 -/
lemma prime_factorization_prime {p : ℕ} (hp : prime p) : p.prime_factorization = single p 1 :=
by { simp only [←prime_factorization_prime_pos_pow hp one_pos, pow_one] }

---------------------------------------------------------------------------------------------------

-- TODO: Add to next PR:
lemma disagree_factor_of_ne {d n : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd: n ≠ d) :
  ∃ (p : ℕ), (n.prime_factorization) p ≠ (d.prime_factorization) p :=
not_forall.mp (mt finsupp.ext (mt (prime_factorization_eq_iff hn hd).mp hnd))

-- TODO: Does `finsupp` not have `<`?
-- -- Change these back to {α : Type u_1} {M : Type u_5} when PRing in `data.finsupp.basic`
-- lemma finsupp.eq_zero_or_pos {α : Type*} {M : Type*} [has_zero M] [has_lt M] {f : α →₀ M} :
--   f = 0 ∨ 0 < f :=
-- begin

--   sorry,
-- end

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
  simp only [finsupp.coe_add, pi.add_apply, prime_factorization_count,
    count_factors_mul_of_coprime hab],
end

/-- For positive `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma prime_factorization_mul_add_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  (a * b).prime_factorization = a.prime_factorization + b.prime_factorization :=
begin
  ext q,
  simp only [finsupp.coe_add, pi.add_apply, prime_factorization_count,
    count_factors_mul_of_pos ha hb],
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
lemma prime_factorization_prod_pow {n : ℕ} (hn : 0 < n) :
  n = n.prime_factorization.prod pow :=
by { refine (multiplicative_factorization hn _ _), simp }

---------------------------------------------------------------------------------------------------

/-- If the prime_factorization of `n` contains just one prime `p` then `n` is a power of `p` -/
lemma prime_pow_of_prime_factorization_single {n p k : ℕ} (hn : 0 < n)
  (h : n.prime_factorization = single p k) : n = p ^ k :=
by { rw [prime_factorization_prod_pow hn, h], simp }

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- We have a map prime_factorization : ℕ ↦ { f : ℕ →₀ ℕ // f.support ⊆ primes }
-- For positive n this map is injective
-- We also have a map { f : ℕ →₀ ℕ // f.support = primes } ↦ ℕ
-- i.e. for any finsupp f we have (f.prod pow) : ℕ
-- Now we want to prove that these two maps are inverses
-- We already have one direction: for n > 0, n = n.prime_factorization.prod pow
-- Now we need to prove the converse: for f : ℕ →₀ ℕ with f.support ⊆ primes,
--   (f.prod pow).prime_factorization = f

lemma prime_factorization_inverse_prod_pow {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, prime p) :
  (f.prod pow).prime_factorization = f :=
begin
  by_cases hf0 : f = 0, { rw hf0, simp, rw prime_factorization_one },
  rw finsupp.ext_iff',
  split,
  {
    rw support_prime_factorization,
    ext q,
    rw [list.mem_to_finset, finsupp.mem_support_iff],
    sorry},
  {
    intros p hp,
    -- rw finsupp.mem_support_iff at hp,
    -- unfold finsupp.prod at hp,
    have := @prime_factorization_prod_pow (f.prod pow),
    sorry},
end

/-- Any `f : ℕ →₀ ℕ` with support on the primes is the prime factorization of some `n : ℕ` -/
lemma prime_factorization_of_prime_finsupp (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, prime p) :
  ∃ n : ℕ, f = n.prime_factorization :=
by { use f.prod pow, rw prime_factorization_inverse_prod_pow hf }
-- TODO: Tighten this to make `n` positive, to remove the ambiguity when `f=0`.

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- Divisibility

-- If `d` divides `n` then for every prime `p`, the power of `p` in `d` is `≤` the power in `n`
lemma prime_factorization_leq_of_dvd {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
  d ∣ n → d.prime_factorization ≤ n.prime_factorization :=
begin
  rw dvd_iff_exists_eq_mul_left,
  rw finsupp.le_def,
  { rintros ⟨c, hcn⟩ p,
    have hc : 0 < c,
      { rw zero_lt_iff, intros H, rw H at hcn, simp at hcn, apply absurd hcn hn.ne' },
    simp only [prime_factorization_count, hcn, le_factors_count_mul_right hc] }
end


-- If for every prime `p`, the power of `p` in `d` is `≤` the power in `n`, then `d` divides `n`
lemma dvd_of_prime_factorization_leq {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
  d.prime_factorization ≤ n.prime_factorization → d ∣ n :=
begin
  rw dvd_iff_exists_eq_mul_left,
  -- rw finsupp.le_def,

  intros h,
  by_cases hnd : n = d, { use 1, simpa },
  have hnd' : d.prime_factorization < n.prime_factorization,
    {
      refine lt_of_le_of_ne h _,
      apply mt (prime_factorization_eq_iff hd hn).mp,
      exact ne_comm.mp hnd,
    },

  set c_pf := n.prime_factorization - d.prime_factorization with c_pf_def,

  have c_pf_neq_zero : 0 < c_pf := tsub_pos_of_lt hnd',



  have h1 : ∀ (p : ℕ), p ∈ c_pf.support → prime p,
  {
    intros p hp,
    suffices : p ∈ n.prime_factorization.support,
      { rw factor_iff_mem_factorization at this,
        exact prime_of_mem_factors this },
    rw mem_support_iff at hp ⊢,
    rw c_pf_def at hp,
    simp at hp,
    exact ne_zero_of_lt hp,
  },

  rcases (prime_factorization_of_prime_finsupp c_pf h1) with ⟨c, hc⟩,
  use c,

  have hc_pos : 0 < c, {
    rw zero_lt_iff,
    intros H,
    rw [H,prime_factorization_zero] at hc,
    rw hc at c_pf_neq_zero,
    finish,


    -- rw hc at c_pf_def,
    -- rw finsupp.ext_iff at c_pf_def,
    -- cases (disagree_factor_of_ne hn hd hnd) with p hp,
    -- specialize c_pf_def p,
    -- simp at c_pf_def,
    -- have : (d.prime_factorization) p < (n.prime_factorization) p,
    --   { exact (ne.symm hp).le_iff_lt.mp (h p) },
    -- have := (tsub_pos_of_lt this).ne,
    -- contradiction,
  },

  have hcd : 0 < c * d := mul_pos hc_pos hd,


  rw ←prime_factorization_eq_iff hn hcd,
  rw prime_factorization_mul_add_of_pos hc_pos hd,
  rw [←hc, c_pf_def],



  ext p,
  rw add_comm,
  apply (nat.add_sub_of_le (h p)).symm,
end




example
(d n: ℕ)
(hd: 0 < d)
(hn: 0 < n)
(hdn: d ≤ n)
: n = (n - d) + d
:=
begin
  rw add_comm,
  exact (nat.add_sub_of_le hdn).symm,
end

end nat
