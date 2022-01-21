/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.nat.prime
import data.finsupp.multiset

/-!
# Prime factorizations

 `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
We have lots of disparate ways of talking about the multiplicity of a prime
in a natural number, including `factors.count`, `padic_val_nat`, `multiplicity`,
and the material in `data/pnat/factors`.  Move some of this material to this file,
prove results about the relationships between these definitions,
and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
with a normalization function, and then deduplicated.  The basics of this have been started in
`ring_theory/unique_factorization_domain`.

* Extend the inductions to any `normalization_monoid` with unique factorization.

-/

open nat finset list finsupp
open_locale big_operators

namespace nat

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
noncomputable def factorization (n : ℕ) : ℕ →₀ ℕ := (n.factors : multiset ℕ).to_finsupp

@[simp] lemma factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.prod pow = n :=
begin
  simp only [←prod_to_multiset, factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  exact prod_factors hn,
end

@[simp] lemma factors_count_eq {n p : ℕ} : n.factors.count p = n.factorization p :=
by simp [factorization]

lemma eq_of_count_factors_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
eq_of_perm_factors ha hb (by simpa only [list.perm_iff_count, factors_count_eq] using h)

/-- Every nonzero natural number has a unique prime factorization -/
lemma factorization_inj : set.inj_on factorization { x : ℕ | x ≠ 0 } :=
λ a ha b hb h, eq_of_count_factors_eq ha hb (λ p, by simp [h])

@[simp] lemma factorization_zero : factorization 0 = 0 :=
by simp [factorization]

@[simp] lemma factorization_one : factorization 1 = 0 :=
by simp [factorization]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : ℕ} : n.factorization.support = n.factors.to_finset :=
by simpa [factorization, multiset.to_finsupp_support]

lemma factor_iff_mem_factorization {n p : ℕ} : p ∈ n.factorization.support ↔ p ∈ n.factors :=
by simp only [support_factorization, list.mem_to_finset]

lemma prime_of_mem_factorization {n p : ℕ} : p ∈ n.factorization.support → p.prime :=
prime_of_mem_factors ∘ (@factor_iff_mem_factorization n p).mp

lemma pos_of_mem_factorization {n p : ℕ} : p ∈ n.factorization.support → 0 < p :=
prime.pos ∘ (@prime_of_mem_factorization n p)

/-- The only numbers with empty prime factorization are `0` and `1` -/
lemma factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
by simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

/-- For positive `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma count_factors_mul {p a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  list.count p (a * b).factors = list.count p a.factors + list.count p b.factors :=
by rw [perm_iff_count.mp (perm_factors_mul_of_pos ha hb) p, count_append]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization = a.factorization + b.factorization :=
by { ext p, simp only [add_apply, ←factors_count_eq, count_factors_mul ha hb] }

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
lemma factorization_pow (n k : ℕ) :
  factorization (n^k) = k • n.factorization :=
begin
  induction k with k ih,
  { simp },
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  rw [pow_succ, factorization_mul hn.ne' (pow_ne_zero _ hn.ne'), ih, succ_eq_one_add, add_smul,
    one_smul],
end

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma count_factors_mul_of_coprime {p a b : ℕ} (hab : coprime a b)  :
  list.count p (a * b).factors = list.count p a.factors + list.count p b.factors :=
by rw [perm_iff_count.mp (perm_factors_mul_of_coprime hab) p, count_append]

/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
lemma factors_count_eq_of_coprime_left {p a b : ℕ} (hab : coprime a b) (hpa : p ∈ a.factors) :
  list.count p (a * b).factors = list.count p a.factors :=
begin
  rw count_factors_mul_of_coprime hab,
  simpa only [count_eq_zero_of_not_mem (coprime_factors_disjoint hab hpa)],
end

lemma pow_factorization_dvd (n p : ℕ) : p ^ n.factorization p ∣ n :=
begin
  rw ←factors_count_eq,
  by_cases hp : p.prime,
  { apply dvd_of_factors_subperm (pow_ne_zero _ hp.ne_zero),
    rw [hp.factors_pow, list.subperm_ext_iff],
    intros q hq,
    simp [list.eq_of_mem_repeat hq] },
  { rw count_eq_zero_of_not_mem (mt prime_of_mem_factors hp),
    simp },
end

lemma pow_succ_factorization_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.prime) :
  ¬ p ^ (n.factorization p + 1) ∣ n :=
begin
  intro h,
  have := factors_sublist_of_dvd h hn,
  rw [hp.factors_pow, ←le_count_iff_repeat_sublist, factors_count_eq] at this,
  linarith
end

lemma prime.factorization_pos_of_dvd {n p : ℕ} (hp : p.prime) (hn : n ≠ 0) (h : p ∣ n) :
  0 < n.factorization p :=
by rwa [←factors_count_eq, count_pos, mem_factors_iff_dvd hn hp]

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
lemma factors_count_eq_of_coprime_right {p a b : ℕ} (hab : coprime a b) (hpb : p ∈ b.factors) :
  list.count p (a * b).factors = list.count p b.factors :=
by { rw mul_comm, exact factors_count_eq_of_coprime_left (coprime_comm.mp hab) hpb }

/-- For `b > 0`, the power of `p` in `a * b` is at least that in `a` -/
lemma le_factors_count_mul_left {p a b : ℕ} (hb : b ≠ 0) :
  list.count p a.factors ≤ list.count p (a * b).factors :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp },
  { rw [perm.count_eq (perm_factors_mul_of_pos ha hb) p, count_append p], simp },
end

/-- For `a > 0`, the power of `p` in `a * b` is at least that in `b` -/
lemma le_factors_count_mul_right {p a b : ℕ} (ha : a ≠ 0) :
  list.count p b.factors ≤ list.count p (a * b).factors :=
by { rw mul_comm, apply le_factors_count_mul_left ha }

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp] lemma prime.factorization {p : ℕ} (hp : prime p) :
  p.factorization = single p 1 :=
begin
  ext q,
  rw [←factors_count_eq, factors_prime hp, single_apply, count_singleton', if_congr eq_comm];
  refl,
end

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
@[simp] lemma prime.factorization_pow {p k : ℕ} (hp : prime p) :
  factorization (p ^ k) = single p k :=
by simp [factorization_pow, hp.factorization]

/-- For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`. -/
lemma factorization_prod {α : Type*} {S : finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
  (S.prod g).factorization = S.sum (λ x, (g x).factorization) :=
begin
  classical,
  ext p,
  apply finset.induction_on' S, { simp },
  { intros x T hxS hTS hxT IH,
    have hT : T.prod g ≠ 0 := prod_ne_zero_iff.mpr (λ x hx, hS x (hTS hx)),
    simp [prod_insert hxT, sum_insert hxT, ←IH, factorization_mul (hS x hxS) hT] }
end

/-! ### Factorizations of pairs of coprime numbers -/

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
lemma factorization_disjoint_of_coprime {a b : ℕ} (hab : coprime a b) :
  disjoint a.factorization.support b.factorization.support :=
by simpa only [support_factorization]
  using disjoint_to_finset_iff_disjoint.mpr (coprime_factors_disjoint hab)

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma factorization_mul_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization = a.factorization + b.factorization :=
begin
  ext q,
  simp only [finsupp.coe_add, add_apply, ←factors_count_eq, count_factors_mul_of_coprime hab],
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma factorization_mul_support_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  rw factorization_mul_of_coprime hab,
  exact support_add_eq (factorization_disjoint_of_coprime hab),
end

lemma factorization_mul_support {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  ext q,
  simp only [finset.mem_union, factor_iff_mem_factorization],
  exact mem_factors_mul_of_ne_zero ha hb q
end

/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ k * a)`,
you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
noncomputable def rec_on_prime_pow {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
  (h : ∀ a p n : ℕ, p.prime → ¬ p ∣ a → P a → P (p ^ n * a)) : ∀ (a : ℕ), P a :=
λ a, nat.strong_rec_on a $ λ n,
  match n with
  | 0     := λ _, h0
  | 1     := λ _, h1
  | (k+2) := λ hk, begin
    let p := (k + 2).min_fac,
    have hp : prime p := min_fac_prime (succ_succ_ne_one k),
    let t := (k+2).factorization p,
    have hpt : p ^ t ∣ k + 2 := pow_factorization_dvd _ _,
    have ht  : 0 < t := hp.factorization_pos_of_dvd (nat.succ_ne_zero (k + 1)) (min_fac_dvd _),

    convert h ((k + 2) / p ^ t) p t hp _ _,
    { rw nat.mul_div_cancel' hpt },
    { rw [nat.dvd_div_iff hpt, ←pow_succ'],
      exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp },

    apply hk _ (nat.div_lt_of_lt_mul _),
    rw [lt_mul_iff_one_lt_left nat.succ_pos', one_lt_pow_iff ht.ne],
    exact hp.one_lt
    end
  end

/-- Given `P 0`, `P 1`, and `P (p ^ k)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
noncomputable def rec_on_pos_prime_coprime {P : ℕ → Sort*} (hp : ∀ p n : ℕ, prime p → 0 < n → P (p ^ n))
  (h0 : P 0) (h1 : P 1) (h : ∀ a b, coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
rec_on_prime_pow h0 h1 $ λ a p n hp' hpa ha,
  h (p ^ n) a ((prime.coprime_pow_of_not_dvd hp' hpa).symm)
  (if h : n = 0 then eq.rec h1 h.symm else hp p n hp' $ nat.pos_of_ne_zero h) ha

/-- Given `P 0`, `P (p ^ k)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
noncomputable def rec_on_prime_coprime {P : ℕ → Sort*} (h0 : P 0) (hp : ∀ p n : ℕ, prime p → P (p ^ n))
  (h : ∀ a b, coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
rec_on_pos_prime_coprime (λ p n h _, hp p n h) h0 (hp 2 0 prime_two) h

/-- Given `P 0`, `P 1`, `P p` for all primes, and a proof that you can extend
`P a` and `P b` to `P (a * b)`, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
noncomputable def rec_on_mul {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
  (hp : ∀ p, prime p → P p) (h : ∀ a b, P a → P b → P (a * b)) : ∀ a, P a :=
let hp : ∀ p n : ℕ, prime p → P (p ^ n) :=
  λ p n hp', match n with
  | 0     := h1
  | (n+1) := by exact h _ _ (hp p hp') (_match _)
  end in
rec_on_prime_coprime h0 hp $ λ a b _, h a b


/-- For any multiplicative function `f` with `f 1 = 1` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
lemma multiplicative_factorization {β : Type*} [comm_monoid β] (f : ℕ → β)
  (h_mult : ∀ x y : ℕ, coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
  ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod (λ p k, f (p ^ k)) :=
begin
  apply' nat.rec_on_pos_prime_coprime,
  { intros p k hp hk hpk, simp [prime.factorization_pow hp, finsupp.prod_single_index _, hf] },
  { simp },
  { rintros -, rw [factorization_one, hf], simp },
  { intros a b hab ha hb hab_pos,
    rw [h_mult a b hab, ha (left_ne_zero_of_mul hab_pos), hb (right_ne_zero_of_mul hab_pos),
        factorization_mul_of_coprime hab, ←prod_add_index_of_disjoint],
    convert (factorization_disjoint_of_coprime hab) },
end

/-- For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
lemma multiplicative_factorization' {β : Type*} [comm_monoid β] (f : ℕ → β)
  (h_mult : ∀ x y : ℕ, coprime x y → f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
  ∀ {n : ℕ}, f n = n.factorization.prod (λ p k, f (p ^ k)) :=
begin
  apply' nat.rec_on_pos_prime_coprime,
  { intros p k hp hk, simp only [hp.factorization_pow], rw prod_single_index _, simp [hf1] },
  { simp [hf0] },
  { rw [factorization_one, hf1], simp },
  { intros a b hab ha hb,
    rw [h_mult a b hab, ha, hb, factorization_mul_of_coprime hab, ←prod_add_index_of_disjoint],
    convert (factorization_disjoint_of_coprime hab) },
end

/-! ### Factorization and divisibility -/

lemma factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
  d.factorization ≤ n.factorization ↔ d ∣ n :=
begin
  split,
  { intro hdn,
    set K := n.factorization - d.factorization with hK,
    use K.prod pow,
    rw [←factorization_prod_pow_eq_self hn, ←factorization_prod_pow_eq_self hd,
        ←finsupp.prod_add_index pow_zero pow_add, hK, add_tsub_cancel_of_le hdn] },
  { rintro ⟨c, rfl⟩, rw factorization_mul hd (right_ne_zero_of_mul hn), simp },
end

end nat
