/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import data.nat.totient
import number_theory.quadratic_reciprocity
import number_theory.lucas_lehmer
import multiplicity_vectors


/-
# Perfect Numbers

## Notations

## Implementation Notes
I have used pnats in this version most of the time.

## References 
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/

open_locale classical
open_locale big_operators

section definitions

variable (n : ℕ+)

/--
The finset of (positive) divisors of n
-/
def divisors : finset ℕ+ := (pnat.Ico 1 (n + 1)).filter (λ x : ℕ+, x ∣ n)

/--
The finset of proper (positive) divisors of n
-/
def proper_divisors : finset ℕ+ := (pnat.Ico 1 n).filter (λ x : ℕ+, x ∣ n)

lemma not_proper_self : ¬ n ∈ proper_divisors n := by simp [proper_divisors]

variable {n}
lemma pnat.le_of_dvd {m : ℕ+} : m ∣ n → m ≤ n :=
by { rw pnat.dvd_iff', intro h, rw ← h, apply (pnat.mod_le n m).left }

@[simp]
lemma mem_divisors {m : ℕ+} : m ∈ divisors n ↔ m ∣ n :=
begin
  rw divisors,
  simp only [true_and, pnat.one_le, pnat.Ico.mem, finset.mem_filter],
  split, intro hyp, exact hyp.right,
  intro hyp, split, swap, exact hyp,
  rw pnat.lt_add_one_iff, apply pnat.le_of_dvd hyp
end

lemma divisor_le {m : ℕ+}:
m ∈ divisors n → m ≤ n := by {rw mem_divisors, exact pnat.le_of_dvd}

@[simp]
lemma mem_proper_divisors {m : ℕ+} : m ∈ proper_divisors n ↔ m ∣ n ∧ m ≠ n :=
begin
  rw proper_divisors,
  simp only [true_and, pnat.one_le, ne.def, pnat.Ico.mem, finset.mem_filter],
  split, intro hyp, split, exact hyp.right, 
  { intro contra, rw contra at hyp, apply lt_irrefl n hyp.left },
  { intro hyp, split, swap, exact hyp.left, apply lt_of_le_of_ne,
    apply pnat.le_of_dvd hyp.left, apply hyp.right }
end

variable (n)

----pnat.dvd_refl should be a simp lemma!
lemma divisors_eq_proper_divisors_insert_self :
  divisors n = has_insert.insert n (proper_divisors n) :=
begin
  ext, rw [finset.mem_insert, mem_divisors, mem_proper_divisors], split,
  { intro hdvd, by_cases a = n, left, exact h,
    right, split, exact hdvd, exact h },
  { intro hyp, cases hyp, rw hyp, apply pnat.dvd_refl, apply hyp.left }
end

def sum_divisors : ℕ := ∑ i in divisors n, i

def sum_proper_divisors : ℕ := ∑ i in proper_divisors n, i

lemma sum_divisors_eq_sum_proper_divisors_add_self :
  sum_divisors n = sum_proper_divisors n + n :=
begin
  rw sum_divisors,
  rw sum_proper_divisors,
  rw divisors_eq_proper_divisors_insert_self,
  rw finset.sum_insert, rw add_comm,
  apply not_proper_self
end

/--
A perfect number is one that is equal to the sum of its proper divisors
-/
def perfect : Prop := sum_proper_divisors n = n

end definitions

section basic_lemmas

---- should two_mul be a simp lemma?
lemma perfect_iff_sum_divisors_twice {n : ℕ+} : perfect n ↔ sum_divisors n = 2 * n :=
begin
  rw sum_divisors_eq_sum_proper_divisors_add_self,
  rw perfect, rw two_mul, simp
end

@[simp] 
lemma divisors_one : divisors 1 = ({1} : finset ℕ+) :=
by { ext, rw mem_divisors, simp [pnat.dvd_one_iff] } ---  pnat.dvd_one_iff should be a simp lemma

@[simp]
lemma mem_one_divisors {n : ℕ+}: (1 : ℕ+) ∈ divisors n :=
by { rw mem_divisors, apply pnat.one_dvd }

lemma mem_self_divisors {n : ℕ+} : n ∈ divisors n :=
by { rw mem_divisors, apply pnat.dvd_refl }

lemma pos_sum_divisors {n : ℕ+} : 0 < sum_divisors n :=
begin
  unfold sum_divisors,
  have h : ∑ i in divisors n, 0 = 0, rw finset.sum_eq_zero_iff, simp,
  rw ← h,
  apply finset.sum_lt_sum, simp,
  existsi (1 : ℕ+), simp only [nat.succ_pos', exists_prop, and_true],
  simp
end

@[simp]
lemma divisors_pow_prime {p : ℕ+} (pp : p.prime) (k : ℕ)  {x : ℕ+} :
  x ∈ divisors (p ^ k) ↔  ∃ (j : ℕ) (H : j ≤ k), x = p ^ j :=
begin
  rw mem_divisors,
  rw pnat.dvd_iff, simp only [pnat.pow_coe],
  --rw nat.primes.coe_pnat_nat, -- simp this?
  --change ↑x ∣ p.val ^ k ↔ ∃ (j : ℕ) (H : j ≤ k), x = p ^ j, --changing ↑ to .val is a pain
  rw nat.dvd_prime_pow pp,
  split; intro h; cases h; cases h_h; existsi h_w; existsi h_h_w,
  { apply pnat.eq, rw h_h_h, simp only [nat.primes.coe_pnat_nat, pnat.pow_coe] },   --- pnat.eq? not coe_inj?
  { rw h_h_h, simp only [nat.primes.coe_pnat_nat, pnat.pow_coe] }
end

lemma divisors_pow_prime_insert {p : ℕ+} (pp : p.prime) (k : ℕ)  :
  divisors (p ^ (k + 1)) = has_insert.insert (p ^ (k + 1)) (divisors (p ^ k)) :=
begin
  ext,
  simp [divisors_pow_prime pp],
  split,
  { intro h, cases h, cases h_h, 
    by_cases h_w = k + 1,
    { left, rw h at h_h_right, exact h_h_right },
    { right, existsi h_w, split, omega, exact h_h_right }
  },
  { intro h, cases h, existsi k + 1, tauto,
    cases h, existsi h_w, split, linarith, exact h_h.right }
end

@[simp]
lemma add_one_sub_one_prime {p : ℕ+} (pp : p.prime): (p : ℕ) - 1 + 1 = p :=
by { apply nat.succ_pred_prime pp }

lemma pnat.mul_lt_mul_left (a : ℕ+) {b c : ℕ+}: b < c → a * b < a * c :=
begin
  intro bc,
  apply nat.mul_lt_mul_of_pos_left, apply bc, apply a.property,
end

lemma pnat.mul_lt_mul_right (a : ℕ+) {b c : ℕ+}: b < c → b * a < c * a :=
begin
  intro bc,
  apply nat.mul_lt_mul_of_pos_right, apply bc, apply a.property,
end

lemma pnat.prime.one_lt {p : ℕ+} : p.prime → 1 < p := nat.prime.one_lt

lemma sum_divisors_pow_prime {p : ℕ+} (pp : p.prime) (k : ℕ)  :
  sum_divisors (p ^ k) * (p - 1)= (p ^ (k + 1) - 1) :=
begin
  rw sum_divisors,
  induction k, simp,
  rw divisors_pow_prime_insert pp,
  rw finset.sum_insert, 
  { rw add_mul, rw k_ih,
    rw nat.pow_succ p (k_n.succ), rw nat.succ_eq_add_one,
    rw ← nat.add_sub_assoc,
    { refine congr (congr rfl _) rfl,
    have h := add_one_sub_one_prime pp,
    conv_rhs {rw ← h, rw mul_add, rw h}, simp },
    { rw ← pnat.one_coe, rw ← pnat.pow_coe, rw pnat.coe_le_coe, apply pnat.one_le }
  },
  { intro contra, have h := divisor_le contra,
    have g1 :=  pnat.mul_lt_mul_right (p ^ k_n) (pnat.prime.one_lt pp),
    rw pow_succ at h, rw one_mul at g1, apply not_lt_of_ge h g1, -- linarith for nats
  }
end

lemma sum_divisors_prime {p : ℕ+} (pp : p.prime) : sum_divisors p = p + 1 :=
begin
  have h1 := sum_divisors_pow_prime pp 1,
  rw pow_one at h1, --- had to switch which pow, lol
  have h2 : ((p + 1) * (p - 1) : ℕ) = p ^ 2 - 1, -- have to make type declarations
  { rw nat.mul_sub_left_distrib, repeat {rw add_mul},
    rw nat.pow_two, simp only [mul_one, one_mul],
    rw add_comm, rw nat.add_sub_add_left },
  rw ← h2 at h1,
  apply nat.eq_of_mul_eq_mul_right _ h1,
  apply nat.prime.pred_pos pp
end

lemma pnat.prime_two : (2 : ℕ+).prime := nat.prime_two

lemma sum_divisors_pow_two (k : ℕ) : sum_divisors (2 ^ k) = (2 ^ (k + 1) - 1) :=
begin
  have h := sum_divisors_pow_prime pnat.prime_two k,
  change sum_divisors (2 ^ k) * (2 - 1) = 2 ^ (k + 1) - 1 at h, -- couldn't find anything to do but change
  rw mul_one at h,
  apply h,
end

lemma odd_sum_divisors_pow_two (k : ℕ) : ¬ has_dvd.dvd 2 (sum_divisors (2 ^ k)) :=
begin
  rw sum_divisors_pow_two k,
  intro contra,
  have h : 2 ∣ 2 ^ (k + 1) - 1 + 1,
  { existsi 2 ^ k,
    rw [← nat.pred_eq_sub_one, ← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos _],
    { rw [mul_comm, nat.pow_succ] },
    apply nat.pos_pow_of_pos, omega,
  },
  rw ← nat.dvd_add_iff_right contra at h,
  have h:= nat.le_of_dvd _ h; linarith,
end

@[simp]
lemma pnat.coe_eq_one_iff {m : ℕ+} :
(m : ℕ) = 1 ↔ m = 1 := by { split; intro h; try { apply pnat.eq}; rw h; simp }

@[simp]
lemma pnat.eq_iff {m n : ℕ+} :
(m : ℕ) = ↑n ↔ m = n := by { split, apply pnat.eq, intro h, rw h }


lemma pnat.dvd_prime {p m : ℕ+} (pp : p.prime) :
(m ∣ p ↔ m = 1 ∨ m = p) := by { rw pnat.dvd_iff, rw nat.dvd_prime pp, simp }

lemma divisors_prime {p : ℕ+} (pp : p.prime) : divisors p = {p, 1} :=
begin
  ext,
  simp only [mem_divisors, ne.def, finset.mem_insert, finset.mem_singleton],
  split; intro h, rw pnat.dvd_prime pp at h, apply h.symm,
  cases h; rw h, apply pnat.dvd_refl, apply pnat.one_dvd
end

lemma card_pair_eq_two {α : Type} {x y : α} (neq : x ≠ y) : ({x, y} : finset α).card = 2 :=
begin
  rw finset.card_insert_of_not_mem, rw finset.card_singleton, rw finset.mem_singleton, apply neq,
end

----why can't I use the above????
lemma pnat.card_pair_eq_two {x y : ℕ+} (neq : x ≠ y) : ({x, y} : finset ℕ+).card = 2 := 
begin
  rw finset.card_insert_of_not_mem, rw finset.card_singleton, rw finset.mem_singleton, apply neq,
end

lemma pnat.prime.ne_one {p : ℕ+} : p.prime → p ≠ 1 :=
by { intro pp, intro contra, apply nat.prime.ne_one pp, rw pnat.coe_eq_one_iff, apply contra }

lemma pnat.eq_one_of_lt_two {n : ℕ+} : n < 2 → n = 1 := 
begin
  intro h, apply le_antisymm, swap, apply pnat.one_le,
  change n < 1 + 1 at h, rw pnat.lt_add_one_iff at h, apply h
end

@[simp]
lemma pnat.one_val : (1 : ℕ+).val = 1 := rfl

@[simp]
lemma pnat.not_prime_one : ¬ (1: ℕ+).prime :=  nat.not_prime_one

lemma pnat.prime.not_dvd_one {p : ℕ+} :
p.prime →  ¬ p ∣ 1 := λ pp : p.prime, nat.prime.not_dvd_one pp

lemma pnat.exists_prime_and_dvd {n : ℕ+} : 2 ≤ n → (∃ (p : ℕ+), p.prime ∧ p ∣ n) := 
begin
  intro h, cases nat.exists_prime_and_dvd h with p hp,
  existsi (⟨p, nat.prime.pos hp.left⟩ : ℕ+), apply hp
end

lemma prime_iff_two_divisors {n : ℕ+} : n.prime ↔ (divisors n).card = 2 :=
begin
  split,
  { intro np, rw divisors_prime np, apply pnat.card_pair_eq_two (pnat.prime.ne_one np),},
  { intro h,
    have ge2 : 2 ≤ n,
    { contrapose h, simp at h, have  h' := pnat.eq_one_of_lt_two h, rw h',
      simp only [divisors_one, finset.card_singleton], omega },
    have ex := pnat.exists_prime_and_dvd ge2, cases ex with p hp,
    have subs : {n, (1 : ℕ+)} ⊆ divisors n,
    { rw finset.subset_iff, intro x, simp only [finset.mem_insert, finset.mem_singleton],
      intro h, cases h; rw h_1, apply mem_self_divisors, apply mem_one_divisors },
    have seteq : {n, (1 : ℕ+)} = divisors n,
    { apply finset.eq_of_subset_of_card_le subs _, rw h, rw pnat.card_pair_eq_two _, 
      contrapose hp, simp only [classical.not_not] at hp, rw hp,
      simp only [not_and], apply pnat.prime.not_dvd_one },
    have pdvd : p ∈ divisors n, rw mem_divisors, apply hp.right,
    rw ← seteq at pdvd, simp only [finset.mem_insert, finset.mem_singleton] at pdvd,
    cases pdvd, rw ← pdvd, apply hp.left,
    exfalso, rw pdvd at hp, apply nat.not_prime_one hp.left
  }
end

lemma subset_eq_divisors_of_sum_eq_sum {n : ℕ+} {s : finset ℕ+} (hsub: ∀ (x : ℕ+), x ∈ s → x ∣ n) :
  ∑ i in s, ↑i = sum_divisors n → s = divisors n :=
begin
  have subs : s ⊆ divisors n,
  { rw finset.subset_iff, intros x hx, rw mem_divisors, apply (hsub x hx) },
  intro h,
  apply finset.subset.antisymm subs _,
  contrapose h, rw finset.subset_iff at h, simp only [classical.not_forall, classical.not_imp] at h,
  intro contra, apply nat.lt_irrefl (s.sum (coe : ℕ+ → ℕ)),
  cases h with x hx, rw mem_divisors at hx,
  --have posx : 0 < id x,
  --{ rw id.def, apply nat.pos_of_ne_zero, intro contra, apply nonzero,
  --  rw contra at hx, apply nat.eq_zero_of_zero_dvd,
  --  rw mem_divisors at hx, apply hx.left.left },
  have h : s.sum coe < (divisors n).sum coe := 
    (finset.sum_lt_sum_of_subset subs) (by simpa) (pnat.pos x) (by simp),
    rw sum_divisors at contra, simp only [id.def] at h, rw ← contra at h, apply h,
end


lemma prime_and_one_of_sum_two_divisors_eq_sum_divisors {x y : ℕ+} (hneq : x ≠ y) (hdvd : y ∣ x) (hsum : ↑(x + y) = sum_divisors x) :
  x.prime ∧ y = 1 :=
begin
  have hdivs : {x, y} = divisors x,
  { apply subset_eq_divisors_of_sum_eq_sum,
    { intro z, simp only [finset.mem_insert, finset.mem_singleton], intro h,
      cases h; rw h, refl, apply hdvd },
    { rw ← hsum, apply finset.sum_pair hneq } },
  have card2 := pnat.card_pair_eq_two hneq, rw hdivs at card2, rw ← prime_iff_two_divisors at card2,
  split, apply card2,
  rw divisors_prime card2 at hdivs,
  have memy : y ∈ ({x, y} : finset ℕ+), simp,
  rw hdivs at memy, simp only [finset.mem_insert, finset.mem_singleton] at memy,
  cases memy, exfalso, apply hneq, symmetry, apply memy,
  apply memy
end

--def pnat.coprime (m n : ℕ+) : Prop := m.gcd n = 1

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

lemma sum_divisors_multiplicative (m n : ℕ+) :
  m.coprime n → sum_divisors (m * n) = (sum_divisors m) * (sum_divisors n) :=
begin
  intro cop,
  repeat {rw sum_divisors},
  rw finset.sum_mul_sum,
  symmetry,
  apply finset.sum_bij (λ x : ℕ+ × ℕ+, λ (h : x ∈ _), x.fst * x.snd),
  { simp only [prod.forall], intros a b hab, dsimp, simp only [finset.mem_product] at hab,
    repeat {rw mem_divisors at hab}, rw mem_divisors,
    apply mul_dvd_mul hab.left hab.right },
  { simp only [prod.forall], intros a b hab, dsimp, simp only [finset.mem_product] at hab },
  { simp only [prod.forall], intros a b c hab h1 h2, 
    dsimp at *, rw finset.mem_product at *, repeat {rw mem_divisors at *},
    ext; dsimp,
    { transitivity (a * b).gcd m,
      { apply coprime_factor_eq_gcd_left cop hab.left hab.right },
      { rw h2, symmetry, apply coprime_factor_eq_gcd_left cop h1.left h1.right } },
    { transitivity (b * a).gcd n,
      { apply coprime_factor_eq_gcd_left cop.symm hab.right hab.left },
      { rw mul_comm, rw h2, rw mul_comm, symmetry,
      apply coprime_factor_eq_gcd_left cop.symm h1.right h1.left } } },
  { simp only [exists_prop, prod.exists, finset.mem_product],
    intros c hc,
    existsi c.gcd m, existsi c.gcd n, split,
    { split; rw mem_divisors; apply nat.gcd_dvd_right _, },
    { rw ← pnat.coprime.gcd_mul c cop,
      symmetry, apply pnat.gcd_eq_left,
      rw mem_divisors at hc, apply hc } }
end

end basic_lemmas

section mersenne_to_perfect

/--
A version of ``mersenne'' from number_theory/lucas_lehmer for pnats
-/
def pmersenne (p : ℕ+) : ℕ+ := ⟨ mersenne p, mersenne_pos p.pos ⟩

def nat.mersenne_succ (n : ℕ) : ℕ+ := ⟨mersenne (n + 1), mersenne_pos n.succ_pos⟩

@[simp]
lemma pmersenne_val (p : ℕ+) : ↑(pmersenne p) = mersenne (↑ p) := rfl

/-
theorem two_le_exponent_of_prime_mersenne {p : ℕ+} : nat.prime (pmersenne p) → 2 ≤ p :=
begin
  intro np,
  cases p, cases p_val, exfalso, apply lt_irrefl 0 p_property,
  cases p_val,
  { exfalso, simp only [mersenne, pnat.mk_one, nat.succ_sub_succ_eq_sub,
    pmersenne_val, pnat.one_coe, nat.sub_zero, nat.pow_one] at np,
    apply nat.not_prime_one np },
  { rw ← pnat.coe_le_coe, simp only [pnat.mk_coe, pnat.coe_bit0, pnat.one_coe],
    apply nat.succ_le_succ, apply nat.succ_le_succ, apply nat.zero_le }
end
-/

theorem two_le_exponent_of_prime_mersenne {p : ℕ} : nat.prime (2 ^ p - 1) → 2 ≤ p :=
begin
  intro np, -- rw mersenne at np,
  cases p, exfalso, apply nat.not_prime_zero np,
  cases p, exfalso, apply nat.not_prime_one np,
  omega
end

/--
Euclid's theorem that Mersenne primes induce perfect numbers
-/
theorem mersenne_to_perfect (p : ℕ+) :
  (pmersenne p).prime → perfect ((2 ^ (↑p - 1)) * (pmersenne p)) :=
begin
  intro mp,
  have hp : 2 ≤ p := two_le_exponent_of_prime_mersenne mp,
  rw [perfect_iff_sum_divisors_twice, sum_divisors_multiplicative],
  { rw [sum_divisors_pow_two, sum_divisors_prime mp],
    repeat {rw ← nat.pred_eq_sub_one},
    repeat {rw ← nat.succ_eq_add_one},
    have pps : (p : ℕ).pred.succ = p := nat.succ_pred_eq_of_pos p.property,
    rw pps, simp only [pnat.coe_bit0, pnat.mul_coe, pmersenne_val, pnat.one_coe, pnat.pow_coe],
    rw [← mul_assoc, mul_comm],
    refine congr (congr rfl _) rfl,
    rw [← pps, mersenne, nat.pred_succ, nat.pow_succ, mul_comm,
      ← nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos ],
    apply nat.mul_pos, omega, apply nat.pow_pos, omega },
  { have h := pow_one (pmersenne p),
    rw [← h, ← pnat.coprime_coe, pnat.pow_coe, pnat.pow_coe],
    apply nat.coprime_pow_primes _ _ nat.prime_two mp _,
    apply ne_of_lt,
    simp only [pmersenne_val, mersenne],
    rw [← nat.pred_eq_sub_one, ← nat.pred_succ 2],
    apply nat.pred_lt_pred, omega,
    rw nat.pred_succ 2,
    change 2 ^ 2 ≤ 2 ^ ↑p,
    apply nat.pow_le_pow_of_le_right, omega, apply hp }
end

end mersenne_to_perfect


section perfect_to_mersenne


/--
  Euler's proof that all even perfect numbers come from Mersenne primes
-/
theorem even_perfect_to_mersenne {n : ℕ+} (even : 2 ∣ n) (perf : perfect n):
  ∃ (k : ℕ), n = (2 ^ k) * k.mersenne_succ ∧ k.mersenne_succ.prime :=
begin
  let k := (factorisation n) two_prime, existsi k,
  let x := odd_part n,
  have hxk : x * 2 ^ k = n := (pow_mult_odd_part_eq_self n),
  --change  at hxk,
  have posk : 0 < k, rw ← prime_dvd_iff_factorisation_pos, apply even,
  
  have hiff : n = 2 ^ k * k.mersenne_succ ↔ 2 * n = 2 * (2 ^ k * k.mersenne_succ),
  { split; intro h, rw h, apply mul_left_cancel h },
  rw [hiff, ← mul_assoc, ← pow_succ (2 : ℕ+)],
  
  rw perfect_iff_sum_divisors_twice at perf,
  rw ← pnat.eq_iff, simp only [pnat.coe_bit0, pnat.mul_coe, pnat.one_coe, pnat.pow_coe],
  rw ← perf,
  rw ← hxk at perf,
  change sum_divisors (x * 2 ^ k) = 2 * ↑(x * 2 ^ k) at perf,
  rw sum_divisors_multiplicative at perf, swap, apply pnat.coprime.symm (coprime_pow_odd_part posk),
  symmetry' at perf,

  rw hxk at perf,
  have dvd2n : sum_divisors (2 ^ k) ∣ 2 * n, {existsi (sum_divisors x), rw perf, rw mul_comm},
  have dvdn : sum_divisors (2 ^ k) ∣ n, 
  { apply nat.coprime.dvd_of_dvd_mul_left (nat.coprime.symm _) dvd2n,
    rw nat.prime.coprime_iff_not_dvd nat.prime_two, apply odd_sum_divisors_pow_two k },
  have dvdx : sum_divisors (2 ^ k) ∣ x := dvd_odd_part_of_odd_dvd dvdn (odd_sum_divisors_pow_two k),
  let y := x / sum_divisors (2 ^ k),
  have ysdpow : y * sum_divisors (2 ^ k) = x := pnat.mul_div_exact dvdx,

  rw ← hxk at perf,
  change 2 * (x * 2 ^ k) = sum_divisors x * sum_divisors (2 ^ k) at perf,
  rw mul_comm at perf,
  rw mul_assoc at perf,
  rw ← nat.pow_succ 2 k at perf,
  rw ← ysdpow at perf,
  rw mul_comm at perf,
  rw ← mul_assoc at perf,
  have h := pnat.mul_right_cancel perf,
  rw ysdpow at *,

  have xneqy : x ≠ y,
  { symmetry, rw ← ysdpow, rw sum_divisors_pow_two, rw ← mul_one y, rw mul_assoc, rw one_mul,
    intro contra, have h := nat.eq_of_mul_eq_mul_left _ contra,
    { have h'' := nat.le_succ_of_pred_le (nat.le_of_eq h.symm),
      have h' := nat.pow_lt_pow_of_lt_right (by omega : 2 > 1) posk,
      change 2 ^ k * 2 ≤ 2 * 1 at h'', rw mul_comm at h'',
      have h3 :=  nat.le_of_mul_le_mul_left h'' (nat.prime.pos nat.prime_two),
      rw nat.pow_zero at h', linarith },
    { by_cases y = 0, swap, apply nat.pos_of_ne_zero h,
      rw h at ysdpow, rw zero_mul at ysdpow, rw ← ysdpow at hxk, rw zero_mul at hxk,
      exfalso, rw hxk at posn, linarith } },
  have hxy : x.prime ∧ y = 1,
  { apply prime_and_one_of_sum_two_divisors_eq_sum_divisors xnonzero xneqy _, swap,
    { existsi sum_divisors (2 ^ k), rw ysdpow },
    rw [← h, ← ysdpow, sum_divisors_pow_two],
    have powpos : 2 ^ k.succ > 0, apply nat.pos_pow_of_pos, linarith,
    symmetry, rw ← nat.succ_pred_eq_of_pos powpos, rw nat.succ_eq_add_one, rw add_mul,
    simp only [nat.add_succ_sub_one, add_zero, one_mul, add_left_inj], rw mul_comm },

  have xeq : x = sum_divisors (2 ^ k), rw ← ysdpow, rw hxy.right, simp,
  have xp : x.prime := hxy.left,

  split, swap, rw sum_divisors_pow_two at xeq, rw ← xeq, apply xp,
  rw ← (pow_fin_mult_coprime_part_eq_self nat.prime_two posn),
  rw sum_divisors_multiplicative, swap,
  { apply nat.prime.coprime_pow_of_not_dvd nat.prime_two (not_dvd_coprime_part nat.prime_two posn)},
  rw [sum_divisors_prime xp, xeq, sum_divisors_pow_two],
  refine congr (congr rfl _) rfl,
  apply nat.succ_pred_eq_of_pos, simp only [nat.nat_zero_eq_zero, gt_iff_lt],
  apply nat.pos_pow_of_pos (k + 1) (nat.prime.pos nat.prime_two)
end

end perfect_to_mersenne

section perfect_iff_mersenne

/--
The Euclid-Euler Theorem, characterizing perfect numbers in terms of Mersenne primes
-/
theorem even_perfect_iff_mersenne {n : ℕ+}:
  2 ∣ n ∧ perfect n ↔ ∃ (p : ℕ+), n = (2 ^ (↑p - 1)) * (pmersenne p) ∧ (pmersenne p).prime :=
begin
  split, intro even_perf, exact even_perfect_to_mersenne even_perf.left even_perf.right,
  intro h, cases h with p hp, rw hp.left, split, swap, apply mersenne_to_perfect p hp.right,
  rw nat.prime.dvd_mul nat.prime_two, left,
  rw nat.dvd_prime_pow nat.prime_two, existsi 1,
  simp only [exists_prop, and_true, eq_self_iff_true, nat.pow_one],
  have gt2 := two_le_exponent_of_prime_mersenne hp.right, omega
end

end perfect_iff_mersenne