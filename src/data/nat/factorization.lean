/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.nat.prime
import data.nat.mul_ind

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
  exact prod_factors hn.bot_lt,
end

lemma factorization_eq_count {n p : ℕ} : n.factorization p = n.factors.count p :=
by simp [factorization]
-- TODO: As part of the unification mentioned in the TODO above,
-- consider making this a [simp] lemma from `n.factors.count` to `n.factorization`

/-- Every nonzero natural number has a unique prime factorization -/
lemma factorization_inj : set.inj_on factorization { x : ℕ | x ≠ 0 } :=
λ a ha b hb h, eq_of_count_factors_eq
  (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb) (λ p, by simp [←factorization_eq_count, h])

@[simp] lemma factorization_zero : factorization 0 = 0  :=
by simp [factorization]

@[simp] lemma factorization_one : factorization 1 = 0 :=
by simp [factorization]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : ℕ} :
  n.factorization.support = n.factors.to_finset :=
by simpa [factorization, multiset.to_finsupp_support]

lemma factor_iff_mem_factorization {n p : ℕ} : p ∈ n.factorization.support ↔ p ∈ n.factors :=
by simp only [support_factorization, list.mem_to_finset]

lemma prime_of_mem_factorization {n p : ℕ} : p ∈ n.factorization.support → p.prime :=
(@prime_of_mem_factors n p) ∘ (@factor_iff_mem_factorization n p).mp

lemma pos_of_mem_factorization {n p : ℕ} : p ∈ n.factorization.support → 0 < p :=
(@prime.pos p) ∘ (@prime_of_mem_factorization n p)

/-- The only numbers with empty prime factorization are `0` and `1` -/
lemma factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
by simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization = a.factorization + b.factorization :=
by { ext p, simp only [add_apply, factorization_eq_count,
  count_factors_mul_of_pos (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb)] }

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
lemma factorization_pow {n k : ℕ} :
  factorization (n^k) = k • n.factorization :=
by { ext p, simp [factorization_eq_count, factors_count_pow] }

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp] lemma prime.factorization {p : ℕ} (hp : prime p) :
  p.factorization = single p 1 :=
begin
  ext q,
  rw [factorization_eq_count, factors_prime hp, single_apply, count_singleton', if_congr eq_comm];
  refl,
end

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
@[simp] lemma prime.factorization_pow {p k : ℕ} (hp : prime p) :
  factorization (p^k) = single p k :=
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

/-! ### Bijection between pnats and finsupps `ℕ →₀ ℕ` with support on the primes -/

/-- Any finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factorization of
the product `∏ (a : ℕ) in f.support, a ^ f a`. -/
lemma factorization_prod_pow_inv {f : ℕ →₀ ℕ} (hf : ∀ (p : ℕ), p ∈ f.support → prime p) :
  (f.prod pow).factorization = f :=
begin
  have h : ∀ x : ℕ, x ∈ f.support → x ^ f x ≠ 0 := λ p hp, pow_ne_zero _ (prime.ne_zero (hf p hp)),
  simp only [finsupp.prod, factorization_prod h],
  nth_rewrite_rhs 0 (sum_single f).symm,
  exact sum_congr rfl (λ p hp, prime.factorization_pow (hf p hp)),
end

lemma prime_finsupp_prod_pow_pos {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, prime p) : 0 < f.prod pow :=
prod_pos (λ p hp, (pow_ne_zero _ (hf p hp).ne_zero).bot_lt)

/-- The positive natural numbers are bijective with finsupps `ℕ →₀ ℕ` with support in the primes -/
noncomputable
def factorization_equiv : pnat ≃ {f : ℕ →₀ ℕ | ∀ p ∈ f.support, prime p} :=
{ to_fun    := λ ⟨n, hn⟩, ⟨n.factorization, λ _, prime_of_mem_factorization⟩,
  inv_fun   := λ ⟨f, hf⟩, ⟨f.prod pow, prime_finsupp_prod_pow_pos hf⟩,
  left_inv  := λ ⟨x, hx⟩, subtype.mk_eq_mk.mpr (factorization_prod_pow_eq_self hx.ne.symm),
  right_inv := λ ⟨f, hf⟩, subtype.mk_eq_mk.mpr (factorization_prod_pow_inv hf) }

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
  simp only [finsupp.coe_add, add_apply, factorization_eq_count, count_factors_mul_of_coprime hab],
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma factorization_mul_support_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  rw factorization_mul_of_coprime hab,
  exact support_add_eq (factorization_disjoint_of_coprime hab),
end

lemma factorization_mul_support_of_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  ext q,
  simp only [finset.mem_union, factor_iff_mem_factorization],
  rw mem_factors_mul_of_pos ha.bot_lt hb.bot_lt,
end

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
