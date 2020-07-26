/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
 -/

import data.finsupp.lattice
import data.pnat.factors
import order.order_iso
import tactic.omega

/-!
# Factor Finsupps

A new version of prime factorisation and some facts about lattice isomorphisms

## Main Definitions
* `factor_finsupp` sends a `pnat` to its prime factorization,
  expressed as a function from the primes to their multiplicities.

* `coprime_part` defines the largest factor of a `pnat` not divisible by a certain prime

* `odd_part` is `coprime_part` where the prime is 2

* Functions satisfying `is_multiplicative` are multiplicative in the arithmetic sense,
  in that `f(mn) = f(m) * f(n)` when `m` and `n` are `coprime`. These can be evaluated using
  `finsupp.prod` over their `factor_finsupp`.

## Implementation Notes
* `factor_finsupp` is based on `pnat.factor_multiset`.

* Many facts about it are proved by constructing a lattice isomorphism between `multiset`s
  and `finsupp`s to ℕ.

* `coprime_part` and `odd_part` are implemented with `finsupp.erase`

-/

set_option old_structure_cmd true

open_locale classical
open_locale big_operators
open finsupp

noncomputable theory

instance : canonically_linear_ordered_add_monoid ℕ :=
{ ..nat.canonically_ordered_comm_semiring, ..nat.decidable_linear_order }

section basics

instance finsupp.coe_primes_to_pnat : has_coe (nat.primes →₀ ℕ) (ℕ+ →₀ ℕ) :=
⟨map_domain coe⟩

lemma prime_multiset.to_pnat_multiset_to_multiset (x : nat.primes →₀ ℕ) :
  prime_multiset.to_pnat_multiset x.to_multiset = (x : ℕ+ →₀ ℕ).to_multiset :=
x.to_multiset_map coe

/-- Take the product of a function of prime powers with exponents given by a finsupp. -/
def finsupp.primes_prod_apply_pow {α : Type} [comm_monoid α] (x : nat.primes →₀ ℕ) (f : ℕ+ → α) : α :=
x.prod (λ p : nat.primes, λ k : ℕ, f (p ^ k))

/-- Take the product of prime powers with exponents given by a finsupp. -/
def finsupp.primes_prod_pow (x : nat.primes →₀ ℕ) := x.primes_prod_apply_pow id

lemma finsupp.primes_prod_pow_eq (x : nat.primes →₀ ℕ) :
  x.primes_prod_pow= x.prod (λ p : nat.primes, λ k : ℕ, (p ^ k)) := rfl

lemma finsupp.primes_prod_pow_eq_coe_prod_pow (x : nat.primes →₀ ℕ) :
  x.primes_prod_pow= (x : ℕ+ →₀ ℕ).prod pow :=
begin
  change x.primes_prod_pow = (finsupp.map_domain coe x).prod pow,
  rw [finsupp.prod_map_domain_index, finsupp.primes_prod_pow_eq], simp,
  intros, rw pow_add,
end

lemma finsupp.primes_prod_pow_eq_prod_to_multiset (x : nat.primes →₀ ℕ) :
  x.primes_prod_pow= prime_multiset.prod x.to_multiset :=
begin
  rw [prime_multiset.prod, finsupp.primes_prod_pow_eq_coe_prod_pow,
    ← finsupp.prod_to_multiset, ← prime_multiset.to_pnat_multiset_to_multiset], refl
end

/-- The value of this finsupp at a prime is the multiplicity of that prime in n. -/
def factor_finsupp (n : ℕ+) : nat.primes →₀ ℕ := n.factor_multiset.to_finsupp

@[simp]
lemma factor_finsupp_to_multiset_eq_factor_multiset {n : ℕ+} :
  (factor_finsupp n).to_multiset = n.factor_multiset :=
by { unfold factor_finsupp, simp }

end basics

section finsupp_lattice_iso_multiset
-- to data.finsupp or a related file?

@[simp]
lemma finsupp.order_iso_multiset_factor_finsupp {n : ℕ+} :
  (factor_finsupp n).order_iso_multiset = n.factor_multiset :=
by { simp [order_iso_multiset, equiv_multiset] }

@[simp]
lemma finsupp.order_iso_multiset_symm_factor_multiset {n : ℕ+} :
  finsupp.order_iso_multiset.symm n.factor_multiset = factor_finsupp n :=
by { apply order_iso_multiset.to_order_embedding.injective, simp }

end finsupp_lattice_iso_multiset

section prime_finsupp_lattice_iso_multiset
/-- Factorization is a bijection from ℕ+ to finsupp.primes_ -/
def pnat.prime_finsupp_equiv : ℕ+ ≃ (nat.primes →₀ ℕ) :=
equiv.trans pnat.factor_multiset_equiv order_iso_multiset.to_equiv.symm

@[simp]
lemma pnat.prime_finsupp_equiv_eq_factor_finsupp :
  ⇑pnat.prime_finsupp_equiv = factor_finsupp :=
begin
  transitivity of_multiset ∘ pnat.factor_multiset, refl,
  ext, unfold factor_finsupp, simp,
end

@[simp]
lemma pnat.prime_finsupp_equiv_symm_eq_prod_pow :
  ⇑pnat.prime_finsupp_equiv.symm = finsupp.primes_prod_pow :=
begin
  transitivity prime_multiset.prod ∘ to_multiset, refl,
  ext, rw finsupp.primes_prod_pow_eq_prod_to_multiset,
end

end prime_finsupp_lattice_iso_multiset

section basic_number_theory_definitions

lemma dvd_iff_le_factor_finsupps {m n : ℕ+} :
  m ∣ n ↔ factor_finsupp m ≤ factor_finsupp n :=
begin
  rw order_iso_multiset.ord, simp [pnat.factor_multiset_le_iff],
end

@[simp]
lemma factor_finsupp_mul {m n : ℕ+} :
  factor_finsupp (m * n) = factor_finsupp m + factor_finsupp n :=
begin
  apply equiv_multiset.injective,
  change (factor_finsupp (m * n)).to_multiset = (factor_finsupp m + factor_finsupp n).to_multiset,
  simp [to_multiset_add, factor_finsupp, pnat.factor_multiset_mul]
end

lemma factor_finsupp_gcd_eq_inf_factor_finsupps {m n : ℕ+} :
  factor_finsupp (m.gcd n) = (factor_finsupp m) ⊓ (factor_finsupp n) :=
begin
  repeat {rw ← finsupp.order_iso_multiset_symm_factor_multiset},
  rw [pnat.factor_multiset_gcd, order_iso.map_inf],
end

@[simp]
lemma factor_finsupp_one : factor_finsupp 1 = 0 :=
begin
  apply equiv_multiset.injective,
  change (factor_finsupp 1).to_multiset = finsupp.to_multiset 0,
  rw [to_multiset_zero, factor_finsupp_to_multiset_eq_factor_multiset, pnat.factor_multiset_one]
end

lemma coprime_iff_disjoint_factor_finsupps {m n : ℕ+} :
  m.coprime n ↔ disjoint (factor_finsupp m) (factor_finsupp n) :=
begin
  rw [pnat.coprime, disjoint, le_bot_iff, finsupp.bot_eq_zero,
  ← factor_finsupp_one, ← factor_finsupp_gcd_eq_inf_factor_finsupps],
  split; intro h, {rw h}, {apply pnat.prime_finsupp_equiv.injective, simpa,}
end

lemma coprime_iff_disjoint_supports {m n : ℕ+} :
  m.coprime n ↔ disjoint (factor_finsupp m).support (factor_finsupp n).support :=
begin
  rw [coprime_iff_disjoint_factor_finsupps, finsupp.disjoint_iff],
  repeat { rw [disjoint, le_bot_iff] },
  split; intro h; rw ← h; ext; simp,
end

end basic_number_theory_definitions

/-- Just wraps to_multiset in the prime_multiset type for the next lemma to typecheck. -/
def finsupp.to_prime_multiset (f : nat.primes →₀ ℕ) : prime_multiset := f.to_multiset

lemma coe_pnat_commute_to_multiset {f : nat.primes →₀ ℕ} :
(↑f : ℕ+ →₀ ℕ).to_multiset =  prime_multiset.to_pnat_multiset f.to_prime_multiset :=
begin
  unfold prime_multiset.to_pnat_multiset, unfold finsupp.to_prime_multiset,
  rw finsupp.to_multiset_map, refl
end

lemma prod_pow_factor_finsupp (n : ℕ+) :
  (factor_finsupp n).primes_prod_pow = n :=
begin
  rw finsupp.primes_prod_pow_eq_prod_to_multiset,
  rw factor_finsupp_to_multiset_eq_factor_multiset,
  rw pnat.prod_factor_multiset
end

lemma factor_finsupp_prod_pow (f : nat.primes →₀ ℕ) :
factor_finsupp (f.primes_prod_pow) = f :=
begin
  unfold factor_finsupp, conv_rhs {rw ← f.to_multiset_to_finsupp},
  rw ← prime_multiset.factor_multiset_prod f.to_multiset,
  rw finsupp.primes_prod_pow_eq_prod_to_multiset
end

lemma factor_finsupp_inj : function.injective factor_finsupp :=
begin
  unfold function.injective, intros a b h,
  rw [← prod_pow_factor_finsupp a, ← prod_pow_factor_finsupp b, h]
end

section prime_powers

variables {p : nat.primes} {n : ℕ+} {k : ℕ}

@[simp]
lemma factor_finsupp_prime : factor_finsupp ↑p = finsupp.single p 1 :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factor_finsupp ↑p) = finsupp.to_multiset (finsupp.single p 1),
  rw [finsupp.to_multiset_single, factor_finsupp_to_multiset_eq_factor_multiset,
    pnat.factor_multiset_of_prime, prime_multiset.of_prime],
  simp
end

@[simp]
lemma factor_finsupp_pow : factor_finsupp (n ^ k) = k • factor_finsupp n :=
begin
  induction k, simp,
  rw [pow_succ, nat.succ_eq_add_one, add_smul, ← k_ih, mul_comm], simp
end


@[simp]
lemma nat.smul_one : k • 1 = k := by { rw nat.smul_def, simp }

@[simp]
lemma factor_finsupp_pow_prime : factor_finsupp (p ^ k) = finsupp.single p k := by simp

end prime_powers


section coprime_part

variables (p : nat.primes) (n : ℕ+)

/-- The greatest divisor n coprime to prime p. -/
def coprime_part : ℕ+ :=
finsupp.primes_prod_pow ((factor_finsupp n).erase p)

variables {p} {n}

@[simp]
lemma factor_finsupp_coprime_part_eq_erase_factor_finsupp :
  factor_finsupp (coprime_part p n) = (factor_finsupp n).erase p :=
by { rw coprime_part, apply factor_finsupp_prod_pow _, }

variable (p)
lemma factor_finsupp_coprime_part_add_single_eq_self :
  factor_finsupp (coprime_part p n) + finsupp.single p ((factor_finsupp n) p) = factor_finsupp n :=
by { simp [finsupp.erase_add_single] }

variables {p} (n)
lemma pow_mult_coprime_part_eq_self : (coprime_part p n) * p ^ ((factor_finsupp n) p) = n :=
begin
  apply factor_finsupp_inj, rw factor_finsupp_mul,
  rw factor_finsupp_pow_prime,
  rw factor_finsupp_coprime_part_add_single_eq_self
end

variable {n}

lemma prime_dvd_iff_mem_support_factor_finsupp : ↑p ∣ n ↔ p ∈ (factor_finsupp n).support :=
begin
  rw dvd_iff_le_factor_finsupps, rw finsupp.le_iff, simp [finsupp.mem_support_single],
  cases (factor_finsupp n) p, simp, omega
end

lemma prime_dvd_iff_factor_finsupp_pos : ↑p ∣ n ↔ 0 < factor_finsupp n p :=
by { rw prime_dvd_iff_mem_support_factor_finsupp, simp [nat.pos_iff_ne_zero] }

lemma not_dvd_coprime_part : ¬ (↑p ∣ (coprime_part p n)) :=
begin
  rw [dvd_iff_le_factor_finsupps, finsupp.le_iff], push_neg, existsi p,
  rw [factor_finsupp_prime, factor_finsupp_coprime_part_eq_erase_factor_finsupp],
  simp,
end

lemma coprime_pow_coprime_part {k : ℕ} (pos : 0 < k): ((p : ℕ+) ^ k).coprime (coprime_part p n) :=
begin
  rw coprime_iff_disjoint_supports,
  rw [factor_finsupp_pow, factor_finsupp_prime, factor_finsupp_coprime_part_eq_erase_factor_finsupp],
  simp only [finsupp.support_erase, nat.smul_one, finsupp.smul_single],
  rw finsupp.support_single_ne_zero, simp, omega
end

lemma coprime_of_prime_not_dvd (h : ¬ ↑p ∣ n) : n.coprime p :=
begin
  rw coprime_iff_disjoint_supports,
  rw prime_dvd_iff_factor_finsupp_pos at h,
  rw factor_finsupp_prime, rw finsupp.support_single_ne_zero, swap, omega,
  rw finset.disjoint_singleton, simp only [finsupp.mem_support_iff, classical.not_not],
  simp only [nat.pos_iff_ne_zero, classical.not_not] at h, apply h
end

lemma dvd_coprime_part_of_coprime_dvd {m : ℕ+} (hmn : has_dvd.dvd m n) (hmp : ¬ ↑p ∣ m) :
  m ∣ (coprime_part p n) :=
begin
  rw prime_dvd_iff_mem_support_factor_finsupp at hmp,
  rw dvd_iff_le_factor_finsupps at *, rw finsupp.le_iff at *, intro q,
  intro h, simp only [factor_finsupp_coprime_part_eq_erase_factor_finsupp],
  rw finsupp.erase_ne, apply hmn q h, intro qp, rw qp at h, apply hmp h
end

@[simp]
lemma coprime_part_prime_mul_eq_coprime_part : coprime_part p (p * n) = coprime_part p n :=
by { apply factor_finsupp_inj, simp }

/-- 2 as an element of nat.primes. -/
def two_prime : nat.primes := ⟨2, nat.prime_two⟩

variable (n)
/-- The greatest odd factor of a pnat. -/
def odd_part : ℕ+ := coprime_part two_prime n
variable {n}

lemma dvd_odd_part_of_odd_dvd {m : ℕ+} (hmn : has_dvd.dvd m n) (hmp : ¬ 2 ∣ m) :
  m ∣ (odd_part n) :=
begin
  apply dvd_coprime_part_of_coprime_dvd hmn, apply hmp
end

lemma coprime_pow_odd_part {k : ℕ} (pos : 0 < k) : ((2 : ℕ+) ^ k).coprime (odd_part n) :=
begin
  have h : pnat.coprime (↑two_prime ^ k) (coprime_part two_prime n) := coprime_pow_coprime_part pos,
  apply h
end

variable (n)
lemma pow_mult_odd_part_eq_self : (odd_part n) * 2 ^ (factor_finsupp n two_prime) = n :=
begin
  rw odd_part,
  --conv_rhs {rw ← prod_pow_factor_finsupp n},
  change coprime_part two_prime n * ↑two_prime ^ (factor_finsupp n) two_prime = n,
  rw pow_mult_coprime_part_eq_self n,
end

variable {n}

@[simp]
lemma odd_part_two_mul_eq_odd_part : odd_part (2 * n) = odd_part n :=
coprime_part_prime_mul_eq_coprime_part

end coprime_part

section multiplicative

variables {α : Type} [comm_monoid α]

/-- Determines if a function is multiplicative (in the number-theoretic sense). -/
def is_multiplicative (f : ℕ+ → α): Prop :=
f 1 = 1 ∧ ∀ m n : ℕ+, nat.coprime m n → f (m * n) = f m * f n

variables {f : ℕ+ → α}

lemma multiplicative_prod_eq_prod_multiplicative
  (h : is_multiplicative f) {x : nat.primes →₀ ℕ} {s : finset nat.primes} :
  f (∏ (a : nat.primes) in s, ↑a ^ x a) = ∏ (a : nat.primes) in s, f (↑a ^ x a) :=
begin
  apply finset.induction_on s, simp [h.left],
  intros a s anins ih, repeat {rw finset.prod_insert anins}, rw [h.right, ih],
  rw pnat.coprime_coe, rw ← pow_one (∏ (x_1 : nat.primes) in s, ↑x_1 ^ x x_1),
  apply pnat.coprime.pow, apply finset.prod_induction, swap, simp,
  { intros, apply pnat.coprime.symm, apply pnat.coprime.mul a_2.symm a_3.symm, },
  { intros p hp, rw ← pnat.coprime_coe, rw ← nat.pow_one ↑↑a, rw pnat.pow_coe,
    apply nat.coprime_pow_primes,
    rw nat.primes.coe_pnat_nat, apply a.property,
    rw nat.primes.coe_pnat_nat, apply p.property,
    intro ap, apply anins, rw nat.primes.coe_nat_inj a p _, apply hp,
    repeat {rw nat.primes.coe_pnat_nat at ap}, apply ap,
  }
end

lemma multiplicative_from_prime_pow (h : is_multiplicative f) :
  ∀ n : ℕ+, f(n) = (factor_finsupp n).primes_prod_apply_pow f :=
begin
  intro n, rw finsupp.primes_prod_apply_pow,
  conv_lhs {rw ← prod_pow_factor_finsupp n}, rw finsupp.primes_prod_pow_eq, unfold finsupp.prod,
  apply multiplicative_prod_eq_prod_multiplicative h,
end

end multiplicative
