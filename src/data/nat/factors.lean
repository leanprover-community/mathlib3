/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.nat.prime
import data.list.prime
import data.list.sort
import tactic.nth_rewrite

/-!
# Prime numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file deals with the factors of natural numbers.

## Important declarations

- `nat.factors n`: the prime factorization of `n`
- `nat.factors_unique`: uniqueness of the prime factorisation

-/

open bool subtype
open_locale nat

namespace nat

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → list ℕ
| 0 := []
| 1 := []
| n@(k+2) :=
  let m := min_fac n in have n / m < n := factors_lemma,
  m :: factors (n / m)

@[simp] lemma factors_zero : factors 0 = [] := by rw factors
@[simp] lemma factors_one : factors 1 = [] := by rw factors

lemma prime_of_mem_factors : ∀ {n p}, p ∈ factors n → prime p
| 0       := by simp
| 1       := by simp
| n@(k+2) := λ p h,
  let m := min_fac n in have n / m < n := factors_lemma,
  have h₁ : p = m ∨ p ∈ (factors (n / m)) :=
    (list.mem_cons_iff _ _ _).1 (by rwa [factors] at h),
  or.cases_on h₁ (λ h₂, h₂.symm ▸ min_fac_prime dec_trivial)
    prime_of_mem_factors

lemma pos_of_mem_factors {n p : ℕ} (h : p ∈ factors n) : 0 < p :=
prime.pos (prime_of_mem_factors h)

lemma prod_factors : ∀ {n}, n ≠ 0 → list.prod (factors n) = n
| 0       := by simp
| 1       := by simp
| n@(k+2) := λ h,
  let m := min_fac n in have n / m < n := factors_lemma,
  show (factors n).prod = n, from
  have h₁ : n / m ≠ 0 := λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [factors, list.prod_cons, prod_factors h₁, nat.mul_div_cancel' (min_fac_dvd _)]

lemma factors_prime {p : ℕ} (hp : nat.prime p) : p.factors = [p] :=
begin
  have : p = (p - 2) + 2 := (tsub_eq_iff_eq_add_of_le hp.two_le).mp rfl,
  rw [this, nat.factors],
  simp only [eq.symm this],
  have : nat.min_fac p = p := (nat.prime_def_min_fac.mp hp).2,
  split,
  { exact this, },
  { simp only [this, nat.factors, nat.div_self (nat.prime.pos hp)], },
end

lemma factors_chain : ∀ {n a}, (∀ p, prime p → p ∣ n → a ≤ p) → list.chain (≤) a (factors n)
| 0       := λ a h, by simp
| 1       := λ a h, by simp
| n@(k+2) := λ a h,
  let m := min_fac n in have n / m < n := factors_lemma,
  begin
    rw factors,
    refine list.chain.cons ((le_min_fac.2 h).resolve_left dec_trivial) (factors_chain _),
    exact λ p pp d, min_fac_le_of_dvd pp.two_le (d.trans $ div_dvd_of_dvd $ min_fac_dvd _),
  end

lemma factors_chain_2 (n) : list.chain (≤) 2 (factors n) := factors_chain $ λ p pp _, pp.two_le

lemma factors_chain' (n) : list.chain' (≤) (factors n) :=
@list.chain'.tail _ _ (_::_) (factors_chain_2 _)

lemma factors_sorted (n : ℕ) : list.sorted (≤) (factors n) :=
list.chain'_iff_pairwise.1 (factors_chain' _)

/-- `factors` can be constructed inductively by extracting `min_fac`, for sufficiently large `n`. -/
lemma factors_add_two (n : ℕ) :
  factors (n+2) = min_fac (n+2) :: factors ((n+2) / min_fac (n+2)) :=
by rw factors

@[simp]
lemma factors_eq_nil (n : ℕ) : n.factors = [] ↔ n = 0 ∨ n = 1 :=
begin
  split; intro h,
  { rcases n with (_ | _ | n),
    { exact or.inl rfl },
    { exact or.inr rfl },
    { rw factors at h, injection h }, },
  { rcases h with (rfl | rfl),
    { exact factors_zero },
    { exact factors_one }, }
end

lemma eq_of_perm_factors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.factors ~ b.factors) : a = b :=
by simpa [prod_factors ha, prod_factors hb] using list.perm.prod_eq h

section
open list

lemma mem_factors_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : prime p) : p ∈ factors n ↔ p ∣ n :=
⟨λ h, prod_factors hn ▸ list.dvd_prod h,
  λ h, mem_list_primes_of_dvd_prod
    (prime_iff.mp hp)
    (λ p h, prime_iff.mp (prime_of_mem_factors h))
    ((prod_factors hn).symm ▸ h)⟩

lemma dvd_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ∣ n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { exact dvd_zero p },
  { rwa ←mem_factors_iff_dvd hn.ne' (prime_of_mem_factors h) }
end

lemma mem_factors {n p} (hn : n ≠ 0) : p ∈ factors n ↔ prime p ∧ p ∣ n :=
⟨λ h, ⟨prime_of_mem_factors h, dvd_of_mem_factors h⟩,
 λ ⟨hprime, hdvd⟩, (mem_factors_iff_dvd hn hprime).mpr hdvd⟩

lemma le_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ≤ n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { rw factors_zero at h, cases h },
  { exact le_of_dvd hn (dvd_of_mem_factors h) },
end

/-- **Fundamental theorem of arithmetic**-/
lemma factors_unique {n : ℕ} {l : list ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, prime p) :
  l ~ factors n :=
begin
  refine perm_of_prod_eq_prod _ _ _,
  { rw h₁,
    refine (prod_factors _).symm,
    rintro rfl,
    rw prod_eq_zero_iff at h₁,
    exact prime.ne_zero (h₂ 0 h₁) rfl },
  { simp_rw ←prime_iff, exact h₂ },
  { simp_rw ←prime_iff, exact (λ p, prime_of_mem_factors) },
end

lemma prime.factors_pow {p : ℕ} (hp : p.prime) (n : ℕ) :
  (p ^ n).factors = list.replicate n p :=
begin
  symmetry,
  rw ← list.replicate_perm,
  apply nat.factors_unique (list.prod_replicate n p),
  intros q hq,
  rwa eq_of_mem_replicate hq,
end

lemma eq_prime_pow_of_unique_prime_dvd {n p : ℕ} (hpos : n ≠ 0)
  (h : ∀ {d}, nat.prime d → d ∣ n → d = p) :
  n = p ^ n.factors.length :=
begin
  set k := n.factors.length,
  rw [← prod_factors hpos, ← prod_replicate k p,
    eq_replicate_of_mem (λ d hd, h (prime_of_mem_factors hd) (dvd_of_mem_factors hd))],
end

/-- For positive `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
lemma perm_factors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factors ~ a.factors ++ b.factors :=
begin
  refine (factors_unique _ _).symm,
  { rw [list.prod_append, prod_factors ha, prod_factors hb] },
  { intros p hp,
    rw list.mem_append at hp,
    cases hp;
    exact prime_of_mem_factors hp },
end

/-- For coprime `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
lemma perm_factors_mul_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factors ~ a.factors ++ b.factors :=
begin
  rcases a.eq_zero_or_pos with rfl | ha,
  { simp [(coprime_zero_left _).mp hab] },
  rcases b.eq_zero_or_pos with rfl | hb,
  { simp [(coprime_zero_right _).mp hab] },
  exact perm_factors_mul ha.ne' hb.ne',
end

lemma factors_sublist_right {n k : ℕ} (h : k ≠ 0) : n.factors <+ (n * k).factors :=
begin
  cases n,
  { rw zero_mul },
  apply sublist_of_subperm_of_sorted _ (factors_sorted _) (factors_sorted _),
  rw (perm_factors_mul n.succ_ne_zero h).subperm_left,
  exact (sublist_append_left _ _).subperm,
end

lemma factors_sublist_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors <+ k.factors :=
begin
  obtain ⟨a, rfl⟩ := h,
  exact factors_sublist_right (right_ne_zero_of_mul h'),
end

lemma factors_subset_right {n k : ℕ} (h : k ≠ 0) : n.factors ⊆ (n * k).factors :=
(factors_sublist_right h).subset

lemma factors_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors ⊆ k.factors :=
(factors_sublist_of_dvd h h').subset

lemma dvd_of_factors_subperm {a b : ℕ} (ha : a ≠ 0) (h : a.factors <+~ b.factors) : a ∣ b :=
begin
  rcases b.eq_zero_or_pos with rfl | hb,
  { exact dvd_zero _ },
  rcases a with (_|_|a),
  { exact (ha rfl).elim },
  { exact one_dvd _ },
  use (b.factors.diff a.succ.succ.factors).prod,
  nth_rewrite 0 ←nat.prod_factors ha,
  rw [←list.prod_append,
      list.perm.prod_eq $ list.subperm_append_diff_self_of_count_le $ list.subperm_ext_iff.mp h,
      nat.prod_factors hb.ne']
end

end

lemma mem_factors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {p : ℕ} :
  p ∈ (a * b).factors ↔ p ∈ a.factors ∨ p ∈ b.factors :=
begin
  rw [mem_factors (mul_ne_zero ha hb), mem_factors ha, mem_factors hb, ←and_or_distrib_left],
  simpa only [and.congr_right_iff] using prime.dvd_mul
end

/-- The sets of factors of coprime `a` and `b` are disjoint -/
lemma coprime_factors_disjoint {a b : ℕ} (hab : a.coprime b) : list.disjoint a.factors b.factors :=
begin
  intros q hqa hqb,
  apply not_prime_one,
  rw ←(eq_one_of_dvd_coprimes hab (dvd_of_mem_factors hqa) (dvd_of_mem_factors hqb)),
  exact prime_of_mem_factors hqa
end

lemma mem_factors_mul_of_coprime {a b : ℕ} (hab : coprime a b) (p : ℕ):
  p ∈ (a * b).factors ↔ p ∈ a.factors ∪ b.factors :=
begin
  rcases a.eq_zero_or_pos with rfl | ha,
  { simp [(coprime_zero_left _).mp hab] },
  rcases b.eq_zero_or_pos with rfl | hb,
  { simp [(coprime_zero_right _).mp hab] },
  rw [mem_factors_mul ha.ne' hb.ne', list.mem_union]
end

open list

/-- If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0` -/
lemma mem_factors_mul_left {p a b : ℕ} (hpa : p ∈ a.factors) (hb : b ≠ 0) : p ∈ (a*b).factors :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simpa using hpa },
  apply (mem_factors_mul ha hb).2 (or.inl hpa),
end

/-- If `p` is a prime factor of `b` then `p` is also a prime factor of `a * b` for any `a > 0` -/
lemma mem_factors_mul_right {p a b : ℕ} (hpb : p ∈ b.factors) (ha : a ≠ 0) : p ∈ (a*b).factors :=
by { rw mul_comm, exact mem_factors_mul_left hpb ha }

lemma eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) :
  (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, nat.prime p ∧ p ∣ n ∧ odd p :=
(eq_or_ne n 0).elim
  (λ hn, (or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩))
  (λ hn, or_iff_not_imp_right.mpr
    (λ H, ⟨n.factors.length, eq_prime_pow_of_unique_prime_dvd hn
      (λ p hprime hdvd, hprime.eq_two_or_odd'.resolve_right
        (λ hodd, H ⟨p, hprime, hdvd, hodd⟩))⟩))

end nat

assert_not_exists multiset
