/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import data.nat.totient
import number_theory.quadratic_reciprocity
import number_theory.lucas_lehmer
import multiplicity_vectors


/-!
# Perfect Numbers

We define perfect numbers and prove the Euclid-Euler theorem relating them to Mersenne primes

## Notations

## Implementation Notes
I have used pnats in this version most of the time.
As a result, there are many new pnat facts and definitions in multiplicity_vectors.lean

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

/--The sum (nat) of the divisors of a pnat n-/
def sum_divisors : ℕ := ∑ i in divisors n, i

/--The sum (pnat) of the divisors of a pnat n-/
def psum_divisors : ℕ+ := ⟨sum_divisors n,
begin
  have h : ∑ i in divisors n, 0 = 0, rw finset.sum_eq_zero_iff, simp,
  rw ← h,
  apply finset.sum_lt_sum, simp,
  existsi (1 : ℕ+), simp only [nat.succ_pos', exists_prop, and_true],
  simp [pnat.one_dvd]
end⟩

@[simp]
lemma coe_psum_divisors : ↑(psum_divisors n) = sum_divisors n := rfl

/--The sum (nat) of the proper divisors (less than n) of a pnat n-/
def sum_proper_divisors : ℕ := ∑ i in proper_divisors n, i

lemma sum_divisors_eq_sum_proper_divisors_add_self :
  sum_divisors n = sum_proper_divisors n + n :=
begin
  rw sum_divisors,
  rw sum_proper_divisors, dsimp,
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


lemma perfect_iff_sum_divisors_twice {n : ℕ+} : perfect n ↔ sum_divisors n = 2 * n :=
by { rw [perfect, sum_divisors_eq_sum_proper_divisors_add_self], simp [two_mul] }

@[simp]
lemma divisors_one : divisors 1 = ({1} : finset ℕ+) :=
by { ext, rw mem_divisors, simp [pnat.dvd_one_iff] } ---  pnat.dvd_one_iff should be a simp lemma

@[simp]
lemma mem_one_divisors {n : ℕ+}: (1 : ℕ+) ∈ divisors n :=
by { rw mem_divisors, apply pnat.one_dvd }

lemma mem_self_divisors {n : ℕ+} : n ∈ divisors n :=
by { rw mem_divisors, apply pnat.dvd_refl }


@[simp]
lemma divisors_pow_prime {p : ℕ+} (pp : p.prime) (k : ℕ)  {x : ℕ+} :
  x ∈ divisors (p ^ k) ↔  ∃ (j : ℕ) (H : j ≤ k), x = p ^ j :=
begin
  rw mem_divisors,
  rw pnat.dvd_iff, simp only [pnat.pow_coe],
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
    { right, existsi h_w, split, omega, exact h_h_right } },
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

lemma geom_series_succ {α : Type} [semiring α] (x : α) (k : ℕ) :
  geom_series x k.succ = geom_series x k + x ^ k :=
begin
  unfold geom_series, rw add_comm, simp [finset.sum_range_succ],
end

lemma sum_divisors_pow_prime {p : ℕ+} (pp : p.prime) (k : ℕ)  :
  sum_divisors (p ^ k) = geom_series p (k + 1) :=
begin
  rw sum_divisors,
  induction k, simp,
  rw divisors_pow_prime_insert pp,
  rw finset.sum_insert,
  { rw k_ih, conv_rhs {rw geom_series_succ}, rw add_comm, simp },
  { intro contra,
    have h := divisor_le contra,
    have g1 :=  nat.mul_lt_mul_of_pos_left (nat.prime.one_lt pp) (nat.pos_pow_of_pos (k_n) (nat.prime.pos pp)),
    apply not_lt_of_le h, rw pow_add, rw ← pnat.coe_lt_coe, revert g1, simp }
end

lemma sum_divisors_prime {p : ℕ+} (pp : p.prime) : sum_divisors p = p + 1 :=
begin
  have h := sum_divisors_pow_prime pp 1, rw pow_one at h, rw h, unfold geom_series,
  simp [finset.sum_range_succ]
end

lemma pnat.prime_two : (2 : ℕ+).prime := nat.prime_two

lemma geom_series_two (k : ℕ): geom_series 2 k = 2 ^ k - 1 :=
begin
  induction k with k hk, simp,
  rw [geom_series_succ, hk, nat.pow_succ, mul_two, add_comm, nat.add_sub_assoc, nat.pow_eq_pow],
  apply nat.pos_pow_of_pos, omega
end

lemma sum_divisors_pow_two (k : ℕ) : sum_divisors (2 ^ k) = (2 ^ (k + 1) - 1) :=
begin
  induction k with k hk, simp [sum_divisors],
  rw sum_divisors_pow_prime pnat.prime_two k.succ, simp [geom_series_two]
end

lemma odd_mersenne_succ (k : ℕ) : ¬  2 ∣ (2 ^ (k + 1) - 1) :=
begin
  intro contra,
  have h : 2 ∣ 2 ^ (k + 1) - 1 + 1,
  { existsi 2 ^ k,
    rw [← nat.pred_eq_sub_one, ← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos _],
    { rw [mul_comm, nat.pow_succ] },
    apply nat.pos_pow_of_pos, omega },
  rw ← nat.dvd_add_iff_right contra at h,
  have h:= nat.le_of_dvd _ h; linarith,
end

lemma odd_sum_divisors_pow_two (k : ℕ) : ¬  2 ∣ (sum_divisors (2 ^ k)) :=
begin
  rw sum_divisors_pow_two k, apply odd_mersenne_succ,
end

@[simp]
lemma pnat.coe_eq_one_iff {m : ℕ+} :
(m : ℕ) = 1 ↔ m = 1 := by { split; intro h; try { apply pnat.eq}; rw h; simp }


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
  have h : s.sum coe < (divisors n).sum coe :=
    (finset.sum_lt_sum_of_subset subs) (by simpa) (pnat.pos x) (by simp),
  rw sum_divisors at contra, simp only [id.def] at h, rw ← contra at h, apply h,
end


lemma prime_and_one_of_sum_two_divisors_eq_sum_divisors {x y : ℕ+}
  (hneq : x ≠ y) (hdvd : y ∣ x) (hsum : x + y = psum_divisors x) :
  x.prime ∧ y = 1 :=
begin
  have hdivs : {x, y} = divisors x,
  { apply subset_eq_divisors_of_sum_eq_sum,
    { intro z, simp only [finset.mem_insert, finset.mem_singleton], intro h,
      cases h; rw h, refl, apply hdvd },
    { rw ← pnat.eq_iff at hsum, rw coe_psum_divisors at hsum,
      rw ← hsum, apply finset.sum_pair hneq } },
  have card2 := pnat.card_pair_eq_two hneq, rw hdivs at card2, rw ← prime_iff_two_divisors at card2,
  split, apply card2,
  rw divisors_prime card2 at hdivs,
  have memy : y ∈ ({x, y} : finset ℕ+), simp,
  rw hdivs at memy, simp only [finset.mem_insert, finset.mem_singleton] at memy,
  cases memy, exfalso, apply hneq, symmetry, apply memy,
  apply memy
end


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

lemma psum_divisors_multiplicative (m n : ℕ+) :
  m.coprime n → psum_divisors (m * n) = (psum_divisors m) * (psum_divisors n) :=
by { intro h, apply pnat.eq, apply sum_divisors_multiplicative m n h }

end basic_lemmas

section mersenne_to_perfect

/--A modification of mersenne from number_theory/lucas_lehmer-/
def nat.mersenne_succ (n : ℕ) : ℕ+ := ⟨mersenne (n + 1), mersenne_pos n.succ_pos⟩

@[simp]
lemma nat.coe_mersenne_succ (n : ℕ) : ↑(n.mersenne_succ) = mersenne (n + 1) := rfl

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
theorem mersenne_to_perfect (k : ℕ) :
  k.mersenne_succ.prime → perfect ((2 ^ k) * k.mersenne_succ) :=
begin
  intro pr,
  have hk : 0 < k, cases k, contrapose pr, simp [nat.mersenne_succ, mersenne], simp,
  rw [perfect_iff_sum_divisors_twice, sum_divisors_multiplicative],
  { rw [sum_divisors_pow_two, sum_divisors_prime pr],
    repeat {rw ← nat.pred_eq_sub_one}, repeat {rw ← nat.succ_eq_add_one},
    simp only [pnat.coe_bit0, pnat.mul_coe, pnat.one_coe, pnat.pow_coe],
    rw [← mul_assoc, mul_comm], refine congr (congr rfl _) rfl,
    rw nat.mersenne_succ, dsimp, rw mersenne, conv_rhs { rw mul_comm, rw ← nat.pow_succ },
    apply nat.succ_pred_eq_of_pos, apply nat.pow_pos, omega },
  { rw ← pow_one (k.mersenne_succ), apply pnat.coprime.pow, apply pnat.coprime.symm,
    change k.mersenne_succ.coprime ↑two_prime, apply coprime_of_prime_not_dvd,
    apply odd_mersenne_succ,
  }
end

end mersenne_to_perfect


section perfect_to_mersenne


/--
  Euler's proof that all even perfect numbers come from Mersenne primes
-/
theorem even_perfect_to_mersenne {n : ℕ+} (even : 2 ∣ n) (perf : perfect n):
  ∃ (k : ℕ), n = (2 ^ k) * k.mersenne_succ ∧ k.mersenne_succ.prime :=
begin
  let k := (factor_finsupp n) two_prime, existsi k,
  let x := odd_part n,
  have hxk : x * 2 ^ k = n := (pow_mult_odd_part_eq_self n),
  have posk : 0 < k, rw ← prime_dvd_iff_factor_finsupp_pos, apply even,

  have hiff : n = 2 ^ k * k.mersenne_succ ↔ 2 * n = 2 * (2 ^ k * k.mersenne_succ),
  { split; intro h, rw h, apply mul_left_cancel h },
  rw [hiff, ← mul_assoc, ← pow_succ (2 : ℕ+)],

  rw perfect_iff_sum_divisors_twice at perf,
  have pperf : psum_divisors n = (2 : ℕ+) * n, apply pnat.eq, apply perf,
  rw ← hxk at pperf,
  rw psum_divisors_multiplicative at pperf, swap, apply pnat.coprime.symm (coprime_pow_odd_part posk),
  symmetry' at pperf,

  rw hxk at pperf,
  have dvd2n : psum_divisors (2 ^ k) ∣ (2 : ℕ+) * n,
  { apply pnat.dvd_intro (psum_divisors x), rw pperf, rw mul_comm },
  have odd := odd_sum_divisors_pow_two k,
  have xodd2n : odd_part (2 * n) = x := odd_part_two_mul_eq_odd_part,
  have dvdx : psum_divisors (2 ^ k) ∣ odd_part (2 * n) := dvd_odd_part_of_odd_dvd dvd2n odd,
  rw xodd2n at dvdx,
  let y := pnat.div_exact dvdx,
  have ysdpow : psum_divisors (2 ^ k) * y = x := pnat.mul_div_exact dvdx, rw mul_comm at ysdpow,

  rw [← hxk, mul_comm, mul_assoc, mul_comm _ (2 : ℕ+), ← pow_succ _ k, ← ysdpow, mul_comm,
    ← mul_assoc] at pperf,
  have h := mul_right_cancel pperf, rw ysdpow at *,

  have xneqy : x ≠ y,
  { symmetry, rw ← mul_one y, rw ← ysdpow, intro contra,
    have h := mul_left_cancel contra, revert h,
    rw [← pnat.eq_iff, coe_psum_divisors, pnat.one_coe, sum_divisors_pow_two],
    apply ne_of_lt, rw nat.sub_one, rw ← nat.pred_succ 1,
    apply nat.pred_lt_pred, apply nat.succ_ne_zero,
    simp only [nat.pred_succ, nat.succ_eq_add_one], norm_num,
    conv_lhs {rw ← nat.pow_one 2},
    apply nat.pow_lt_pow_of_lt_right _, apply nat.lt_add_of_pos_left posk, omega, },
  have hxy : x.prime ∧ y = 1,
  { apply prime_and_one_of_sum_two_divisors_eq_sum_divisors xneqy _,
    swap, apply pnat.dvd_intro (psum_divisors (2 ^ k)) ysdpow,
    rw ← h, transitivity psum_divisors (2 ^ k) * y + y, rw [mul_comm, ysdpow],
    transitivity psum_divisors (2 ^ k) * y + 1 * y, rw one_mul,
    rw ← add_mul, refine congr (congr rfl _) rfl,
    apply pnat.eq, simp only [sum_divisors_pow_two, coe_psum_divisors, pnat.coe_bit0, pnat.one_coe, pnat.pow_coe, pnat.add_coe],
    apply nat.succ_pred_eq_of_pos, apply nat.pos_pow_of_pos (k + 1) (nat.prime.pos nat.prime_two)
  },

  have xeq : x = k.mersenne_succ,
  { rw [← ysdpow, hxy.right], apply pnat.eq, simp [mersenne, sum_divisors_pow_two] },
  split, swap, rw ← xeq, apply hxy.left,
  rw [← hxk, ← xeq, pow_add, ← mul_assoc, mul_comm, ← mul_assoc, pow_one],
end

end perfect_to_mersenne

section perfect_iff_mersenne

/--
The Euclid-Euler Theorem, characterizing perfect numbers in terms of Mersenne primes
-/
theorem even_perfect_iff_mersenne {n : ℕ+}:
  2 ∣ n ∧ perfect n ↔ ∃ (k : ℕ), n = (2 ^ k) * k.mersenne_succ ∧ k.mersenne_succ.prime  :=
begin
  split; intro h, cases h with even perf, apply even_perfect_to_mersenne even perf,
  cases h with k hk, cases hk with hn pr, rw hn, split, swap, apply mersenne_to_perfect _ pr,
  cases k, contrapose pr, simp [nat.mersenne_succ, mersenne],
  apply pnat.dvd_intro (2 ^ k * k.succ.mersenne_succ), rw [← mul_assoc, pow_succ],
end

end perfect_iff_mersenne
