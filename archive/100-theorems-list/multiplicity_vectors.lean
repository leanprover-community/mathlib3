/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import data.finsupp
import data.pnat.factors
import order.conditionally_complete_lattice
import order.lattice
import tactic.pi_instances

/-
# Factor Finsupps

## Notations

## Implementation Notes
A new notion of factorisation, similar to pnat.factor_multiset, but a finsupp.
Most of the sorries will be solved by proving some facts about lattice isomorphisms.

## References 

-/

set_option old_structure_cmd true

open_locale classical
open_locale big_operators


noncomputable theory

def pnat.coprime (m n : ℕ+) : Prop := m.gcd n = 1

def mult (n : ℕ+) (p : nat.primes) : ℕ := (pnat.factor_multiset n).count p

def prime_finsupp : Type := nat.primes →₀ ℕ

@[instance]
instance prime_finsupp.has_coe_to_fun : has_coe_to_fun prime_finsupp := { ..finsupp.has_coe_to_fun}


def prime_finsupp.prod_apply_pow {α : Type} [comm_monoid α] (x : prime_finsupp) (f : ℕ+ → α) : α :=
x.prod (λ p : nat.primes, λ k : ℕ, f (p ^ k))

def prime_finsupp.prod_coe_pow (x : prime_finsupp) := x.prod_apply_pow id

lemma prime_finsupp.prod_pow_eq (x : prime_finsupp) :
  x.prod_coe_pow= x.prod (λ p : nat.primes, λ k : ℕ, (p ^ k)) := rfl

lemma prime_finsupp.prod_pow_eq_prod_to_multiset (x : prime_finsupp) :
  x.prod_coe_pow= prime_multiset.prod x.to_multiset :=
begin
  rw prime_finsupp.prod_pow_eq, rw prime_multiset.prod,
  sorry
end

def factor_finsupp (n : ℕ+) : prime_finsupp := n.factor_multiset.to_finsupp

@[simp]
lemma inf_zero_iff {m n : ℕ} : m ⊓ n = 0 ↔ m = 0 ∨ n = 0 :=
begin
  split, swap, intro h, cases h; rw h; simp,
  unfold has_inf.inf, unfold semilattice_inf.inf, unfold lattice.inf, unfold min,
  intro hmin, by_cases m = 0, left, apply h,
  rw if_neg _ at hmin, right, apply hmin, contrapose hmin,
  simp only [not_lt, not_le] at hmin, rw if_pos hmin, apply h
end

lemma nat.zero_eq_bot : (0 : ℕ) = ⊥ := rfl

variable {α : Type}

instance finsupp.has_inf :
  has_inf (α →₀ ℕ) :=
begin
  refine ⟨_⟩, intros v1 v2,
  refine ⟨v1.support ∩ v2.support, (λ (a : α), (v1 a ⊓ v2 a)), _⟩,
  intro a, simp only [finsupp.mem_support_iff, ne.def, finset.mem_inter],
  symmetry, rw not_iff_comm, push_neg, rw inf_zero_iff,
end

@[simp]
lemma finsupp.inf_apply {a : α} {f g : α →₀ ℕ} : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp]
lemma finsupp.support_inf {f g : α →₀ ℕ} : (f ⊓ g).support = f.support ⊓ g.support := rfl

instance finsupp.has_sup :
  has_sup (α →₀ ℕ) :=
begin
  refine ⟨_⟩, intros v1 v2,
  refine ⟨v1.support ∪ v2.support, (λ (a : α), (v1 a ⊔ v2 a)), _⟩,
  intro a, simp only [finsupp.mem_support_iff, ne.def, finset.mem_inter],
  symmetry, rw not_iff_comm, simp only [finsupp.mem_support_iff, ne.def, finset.mem_union],
  push_neg, repeat {rw nat.zero_eq_bot}, rw sup_eq_bot_iff,
end

@[simp]
lemma finsupp.sup_apply {a : α} {f g : α →₀ ℕ} : (f ⊔ g) a = f a ⊔ g a := rfl

@[simp]
lemma finsupp.support_sup {f g : α →₀ ℕ} : (f ⊔ g).support = f.support ⊔ g.support := rfl

-- finsupp.to_multiset_strict_mono

lemma nat.bot_eq_zero : (⊥ : ℕ) = 0 := rfl

@[instance]
instance finsupp.lattice : lattice (α →₀ ℕ) :=
begin
  refine lattice.mk has_sup.sup has_le.le has_lt.lt _ _ _ _ _ _ _ has_inf.inf _ _ _,
  exact (finsupp.preorder).le_refl,
  exact (finsupp.preorder).le_trans,
  { simp only [auto_param_eq], intros a b, apply lt_iff_le_not_le,
  },
  exact (finsupp.partial_order).le_antisymm,
  intros, rw finsupp.le_iff, intros, simp,
  intros, rw finsupp.le_iff, intros, simp,
  { intros, rw finsupp.le_iff at *,
    intros, rw finsupp.sup_apply, apply sup_le,
    { by_cases s ∈ a.support, apply a_1 s h,
      simp only [finsupp.mem_support_iff, classical.not_not] at h, rw h, simp },
    { by_cases s ∈ b.support, apply a_2 s h,
      simp only [finsupp.mem_support_iff, classical.not_not] at h, rw h, simp }
    },
  intros, rw finsupp.le_iff, intros, simp,
  intros, rw finsupp.le_iff, intros, simp,
  { intros, rw finsupp.le_iff at *, intros,
    rw finsupp.inf_apply, apply le_inf, apply a_1 s H, apply a_2 s H }
end

@[instance]
instance prime_finsupp.lattice : lattice prime_finsupp :=
{ ..finsupp.lattice}

@[instance]
instance finsupp.semilattice_inf_bot : semilattice_inf_bot (α →₀ ℕ) :=
{ bot := 0,
  bot_le := by { intro a, simp [finsupp.le_iff] },
..finsupp.lattice}

@[instance]
instance prime_finsupp.semilattice_inf_bot : semilattice_inf_bot prime_finsupp :=
{ ..finsupp.semilattice_inf_bot}

@[instance]
instance prime_finsupp.add_comm_monoid : add_comm_monoid prime_finsupp :=
{ ..finsupp.add_comm_monoid}

@[simp]
lemma factor_finsupp_to_multiset_eq_factor_multiset {n : ℕ+} :
  (factor_finsupp n).to_multiset = n.factor_multiset :=
by { unfold factor_finsupp, simp }

lemma finsupp.of_multiset_strict_mono : strict_mono (@finsupp.of_multiset α) :=
begin
  unfold strict_mono, intros, rw lt_iff_le_and_ne at *, split,
  { rw finsupp.le_iff, intros s hs, repeat {rw finsupp.of_multiset_apply},
    rw multiset.le_iff_count at a_1, apply a_1.left },
  { have h := a_1.right, contrapose h, simp at *,
    apply finsupp.equiv_multiset.symm.injective h }
end

section basic_number_theory_definitions

lemma dvd_iff_le_factor_finsupps {m n : ℕ+} :
  m ∣ n ↔ factor_finsupp m ≤ factor_finsupp n := sorry

@[simp]
lemma factor_finsupp_mul {m n : ℕ+} :
  factor_finsupp (m * n) = factor_finsupp m + factor_finsupp n :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factor_finsupp (m * n)) =
    finsupp.to_multiset (factor_finsupp m + factor_finsupp n),
  simp [finsupp.to_multiset_add, factor_finsupp, pnat.factor_multiset_mul]
end

lemma factor_finsupp_gcd_eq_inf_factor_finsupps {m n : ℕ+} :
  factor_finsupp (m.gcd n) = has_inf.inf (factor_finsupp m) (factor_finsupp n) :=
begin
  sorry
end

lemma coprime_iff_disjoint_supports {m n : ℕ+} :
  m.coprime n ↔ disjoint (factor_finsupp m).support (factor_finsupp n).support :=
begin
  sorry
end

lemma coprime_iff_disjoint_factor_finsupps {m n : ℕ+} :
  m.coprime n ↔ disjoint (factor_finsupp m) (factor_finsupp n) :=
begin
  sorry
end

end basic_number_theory_definitions

@[instance]
def prime_finsupp_coe_pnat : has_coe (nat.primes →₀ ℕ) (ℕ+ →₀ ℕ) :=
{ coe := finsupp.map_domain coe }

-- Just wraps to_multiset in the prime_multiset type for the next lemma to typecheck
def finsupp.to_prime_multiset (f : nat.primes →₀ ℕ) : prime_multiset := f.to_multiset

lemma coe_pnat_commute_to_multiset {f : nat.primes →₀ ℕ} :
(↑f : ℕ+ →₀ ℕ).to_multiset =  prime_multiset.to_pnat_multiset f.to_prime_multiset :=
begin
  unfold prime_multiset.to_pnat_multiset, unfold finsupp.to_prime_multiset,
  rw finsupp.to_multiset_map, refl
end

lemma prod_pow_factor_finsupp (n : ℕ+) :
  (factor_finsupp n).prod_coe_pow = n :=
begin
  rw prime_finsupp.prod_pow_eq_prod_to_multiset,
  rw factor_finsupp_to_multiset_eq_factor_multiset,
  rw pnat.prod_factor_multiset
end

lemma factor_finsupp_prod_pow (f : prime_finsupp) :
factor_finsupp (f.prod_coe_pow) = f :=
begin
  unfold factor_finsupp, conv_rhs {rw ← f.to_multiset_to_finsupp},
  rw ← prime_multiset.factor_multiset_prod f.to_multiset,
  rw prime_finsupp.prod_pow_eq_prod_to_multiset
end

lemma factor_finsupp_inj : function.injective factor_finsupp :=
begin
  unfold function.injective, intros a b h,
  rw [← prod_pow_factor_finsupp a, ← prod_pow_factor_finsupp b, h]
end

section prime_powers

@[simp]
lemma factor_finsupp_one : factor_finsupp 1 = 0 :=
begin 
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factor_finsupp 1) = finsupp.to_multiset 0,
  rw [finsupp.to_multiset_zero, factor_finsupp_to_multiset_eq_factor_multiset,
    pnat.factor_multiset_one]
 end

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
lemma prime_finsupp.smul_eq_smul {b : ℕ} :
  (k • finsupp.single p b : prime_finsupp) = (k • finsupp.single p b : nat.primes →₀ ℕ) := 
begin
  rw nat.smul_def,
  induction k, simp, rw [succ_nsmul, nat.succ_eq_add_one, k_ih, add_smul, add_comm], simp
end

@[simp]
lemma nat.smul_one : k • 1 = k := by { rw nat.smul_def, simp }

@[simp]
lemma factor_finsupp_pow_prime : factor_finsupp (p ^ k) = finsupp.single p k := by simp

end prime_powers

section pnat_facts

@[simp]
lemma pnat.eq_iff {m n : ℕ+} :
(m : ℕ) = ↑n ↔ m = n := by { split, apply pnat.eq, intro h, rw h }

@[simp]
def pnat.coprime_coe {m n : ℕ+} : nat.coprime ↑m ↑n ↔ m.coprime n :=
by { unfold pnat.coprime, unfold nat.coprime, rw ← pnat.eq_iff, simp }

lemma pnat.gcd_eq_left_iff_dvd {m n : ℕ+} : m ∣ n ↔ m.gcd n = m :=
by { rw pnat.dvd_iff, rw nat.gcd_eq_left_iff_dvd, rw ← pnat.eq_iff, simp }

lemma pnat.coprime.gcd_mul_right_cancel (m : ℕ+) {n k : ℕ+} :
  k.coprime n → (m * k).gcd n = m.gcd n :=
begin
  intro h, apply pnat.eq, simp only [pnat.gcd_coe, pnat.mul_coe],
  apply nat.coprime.gcd_mul_right_cancel, simpa
end

lemma pnat.gcd_comm {m n : ℕ+} : m.gcd n = n.gcd m :=
by { apply pnat.eq, simp only [pnat.gcd_coe], apply nat.gcd_comm }

lemma pnat.coprime.symm {m n : ℕ+} : m.coprime n → n.coprime m :=
by { unfold pnat.coprime, rw pnat.gcd_comm, simp }

lemma pnat.coprime.coprime_dvd_left {m k n : ℕ+} :
  m ∣ k → k.coprime n → m.coprime n :=
by { rw pnat.dvd_iff, repeat {rw ← pnat.coprime_coe}, apply nat.coprime.coprime_dvd_left }

lemma coprime_factor_eq_gcd_left {a b m n : ℕ+} (cop : m.coprime n) (am : a ∣ m) (bn : b ∣ n):
  a = (a * b).gcd m :=
begin
  rw pnat.gcd_eq_left_iff_dvd at am,
  conv_lhs {rw ← am}, symmetry,
  apply pnat.coprime.gcd_mul_right_cancel a,
  apply pnat.coprime.coprime_dvd_left bn cop.symm,
end

lemma pnat.coprime.gcd_mul (k : ℕ+) {m n : ℕ+} (h: m.coprime n) :
  k.gcd (m * n) = k.gcd m * k.gcd n :=
begin
  rw ← pnat.coprime_coe at h, apply pnat.eq,
  simp only [pnat.gcd_coe, pnat.mul_coe], apply nat.coprime.gcd_mul k h
end

lemma pnat.gcd_eq_left {m n : ℕ+} : m ∣ n → m.gcd n = m :=
by { rw pnat.dvd_iff, intro h, apply pnat.eq, simp only [pnat.gcd_coe], apply nat.gcd_eq_left h }

def pnat.coprime.pow {m n : ℕ+} (k l : ℕ) (h : m.coprime n) : (m ^ k).coprime (n ^ l) :=
begin
  rw ← pnat.coprime_coe at *, simp only [pnat.pow_coe], apply nat.coprime.pow, apply h
end

end pnat_facts

section coprime_part

variables (p : nat.primes) (n : ℕ+)

/--
The greatest divisor n coprime to prime p
-/
def coprime_part : ℕ+ :=
prime_finsupp.prod_coe_pow ((factor_finsupp n).erase p)

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
  simp only [prime_finsupp.smul_eq_smul, finsupp.support_erase, nat.smul_one, finsupp.smul_single],
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

def two_prime : nat.primes := ⟨2, nat.prime_two⟩

variable (n)
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

def is_multiplicative {α : Type} [comm_monoid α] (f : ℕ+ → α): Prop :=
f(1) = 1 ∧ ∀ m n : ℕ+, nat.coprime m n → f(m * n) = f(m) * f(n)

lemma multiplicative_from_prime_pow {α : Type} [comm_monoid α] {f : ℕ+ → α} (h : is_multiplicative f) :
∀ n : ℕ+, f(n) = (factor_finsupp n).prod_apply_pow f :=
begin
  sorry
end

end multiplicative

