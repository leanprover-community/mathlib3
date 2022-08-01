/-
Copyright (c) 2022 Bolton Bailey, Sean Golinski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Sean Golinski
-/

import data.fintype.basic
import group_theory.order_of_element
import tactic.zify
import data.nat.totient
import data.zmod.basic
import field_theory.finite.basic
import data.fintype.basic
import algebra.big_operators.intervals

/-!
# Lemmas and definitions that will be used in proving the Miller-Rabin primality test.

Since we only need to test odd numbers for primality, let `n-1 = 2^e * k`, where
`e := (n-1).factorization 2` and `k := odd_part (n-1)`. Then we can factor the polynomial
`x^(n-1) - 1 = x^(2^e * k) - 1 = (x^k - 1) *  ∏ i in Ico 0 e, (x^(2^i * k) + 1)`.
For prime `n` and any `0 < x < n`, Fermat's Little Theorem gives `x^(n-1) - 1 = 0 (mod n)`,
so we have either `(x^k - 1) = 0 (mod n)` or `(x^(2^i * k) + 1) = 0 (mod n)` for some `0 ≤ i < e`.
Conversely, then, if there is an `0 < a < n` such that `(a^k - 1) ≠ 0 (mod n)` and
`(a^(2^i * k) + 1) ≠ 0 (mod n)` for all `0 ≤ i < e` then this demonstrates that `n` is not prime.
Such an `a` is called a **Miller–Rabin witness** for `n`.

Of course, the existence of a witness can only demonstrate that `n` is not prime. But if we check
several candidates — i.e. several numbers `0 < a < n` — and find that none of them are witnesses
then this increases our confidence that `n` is a prime. This confidence is supported by the
theorem that for any odd composite `n`, at least 3/4 of numbers `1 < a < n-1` are witnesses for `n`.
Thus if `n` is not a prime there is a high probability that randomly sampling these numbers will
produce a witness. For any given confidence threshold `P < 100%` we can repeatedly sample until
the probability of finding a witness (if one exists) is at least `P`. This is the essence of the
Miller-Rabin primality test.

-- TODO add reference to [this](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf)

-/

open nat finset zmod

open_locale big_operators
-- open_locale classical

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- Lemmas to PR elsewhere
---------------------------------------------------------------------------------------------------
lemma square_roots_of_one {p : ℕ} [fact (p.prime)] {x : zmod p} (root : x^2 = 1) :
  x = 1 ∨ x = -1 :=
begin
  have diffsquare : (x + 1) * (x - 1) = 0, { ring_nf, simp [root] },
  have zeros : (x + 1 = 0) ∨ (x - 1 = 0) := mul_eq_zero.1 diffsquare,
  cases zeros with zero1 zero2,
  { right, exact eq_neg_of_add_eq_zero_left zero1 },
  { left, exact sub_eq_zero.mp zero2 },
end

lemma nat.even_two_pow_iff (n : ℕ) : even (2 ^ n) ↔ 0 < n :=
⟨λ h, zero_lt_iff.2 (even_pow.1 h).2, λ h, (even_pow' h.ne').2 even_two⟩

lemma sub_one_dvd_pow_sub_one (p a : ℕ) (hp_pos : 0 < p) : (p - 1) ∣ (p ^ a - 1) :=
begin
  induction a with a IH, { simp },
  rcases IH with ⟨c, hc⟩,
  use p^a + c,
  rw [pow_succ, mul_add, ←hc, tsub_mul, one_mul],
  apply tsub_eq_of_eq_add,
  rw add_assoc,
  have h1 : 1 ≤ p ^ a,
  { exact succ_le_iff.2 (pow_pos hp_pos a) },
  have h2 : p ^ a ≤ p * p ^ a,
  { exact (le_mul_iff_one_le_left (pow_pos hp_pos a)).2 (succ_le_iff.2 hp_pos) },
  rw tsub_add_cancel_of_le h1,
  rw tsub_add_cancel_of_le h2,
end

lemma coprime_add_one (b : ℕ) : (b + 1).coprime b :=
by simp [nat.coprime_self_add_left]

lemma coprime_self_sub_one (a : ℕ) (ha : 0 < a) : a.coprime (a - 1) :=
begin
  nth_rewrite_lhs 0 ←tsub_add_cancel_of_le (succ_le_iff.2 ha),
  apply coprime_add_one,
end

theorem nat.sq_sub_sq' (a b : ℕ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) :=
by { rw [mul_comm, nat.sq_sub_sq] }

lemma factorise_pow_two_pow_sub_one (x m : ℕ) :
  x^(2^m) - 1 = (x - 1) *  ∏ i in Ico 0 m, (x^(2^i) + 1) :=
begin
  induction m with m IH, { simp },
  rcases eq_or_ne m 0 with rfl | he0, { simpa using nat.sq_sub_sq' x 1 },
  rw [pow_succ, Ico_succ_right_eq_insert_Ico zero_le', prod_insert right_not_mem_Ico],
  nth_rewrite_rhs 0 ←mul_assoc,
  nth_rewrite_rhs 0 ←mul_rotate,
  nth_rewrite_rhs 1 mul_comm,
  rw [←IH, ←nat.sq_sub_sq', one_pow, ←pow_mul, mul_comm],
end

-- TODO: Find a better name for this!
protected
lemma factorize_poly (x k e : ℕ) :
  x ^ (2^e * k) - 1 = (x^k - 1) *  ∏ i in Ico 0 e, (x^(2^i * k) + 1) :=
begin
  rw [mul_comm, pow_mul, factorise_pow_two_pow_sub_one (x^k) e],
  apply congr_arg,
  simp_rw [←pow_mul, mul_comm],
end

-- TODO: Find a better name for this!
protected
lemma factorize_poly' {R : Type*} [comm_ring R] (a : R) (k e : ℕ) :
  a ^ (2^e * k) - 1 = (a^k - 1) *  ∏ i in Ico 0 e, (a^(2^i * k) + 1) :=
begin
  simp_rw [mul_comm, pow_mul],
  set x := a^k with hx,
  induction e with m IH, { simp },
  rcases eq_or_ne m 0 with rfl | he0, { simp [mul_comm, ←sq_sub_sq x 1] },

  rw [pow_succ, Ico_succ_right_eq_insert_Ico zero_le', prod_insert right_not_mem_Ico],
  nth_rewrite_rhs 0 ←mul_assoc,
  nth_rewrite_rhs 0 ←mul_rotate,
  nth_rewrite_rhs 1 mul_comm,
  rw [←IH],
  rw [mul_comm, pow_mul, mul_comm],
  simpa using sq_sub_sq (x ^ 2 ^ m) 1,
end

lemma factorization_two_pos_of_even_of_pos {n : ℕ} (hn : even n) (hn0 : n ≠ 0) :
  0 < n.factorization 2 :=
begin
  rcases hn with ⟨k, rfl⟩,
  simp only [ne.def, add_self_eq_zero] at hn0,
  rw ←two_mul,
  simp [nat.factorization_mul _ hn0, prime_two.factorization],
end

lemma factorization_two_pos_sub_one {n : ℕ} (hn : odd n) (hn1 : n ≠ 1) :
  0 < (n - 1).factorization 2 :=
begin
  rcases hn with ⟨k, rfl⟩,
  simp only [ne.def, add_left_eq_self, nat.mul_eq_zero, bit0_eq_zero, nat.one_ne_zero, false_or]
    at hn1,
  simp [nat.factorization_mul _ hn1, prime_two.factorization],
end

---------------------------------------------------------------------------------------------------
-- PR'ed in #15793
---------------------------------------------------------------------------------------------------
lemma ord_proj_dvd_ord_proj_of_dvd {a b p : ℕ} (hab : a ∣ b) (hb0 : b ≠ 0) :
  ord_proj[p] a ∣ ord_proj[p] b := sorry

lemma ord_compl_dvd_ord_compl_of_dvd {a b p : ℕ} (hab : a ∣ b) :
  ord_compl[p] a ∣ ord_compl[p] b := sorry
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-! ## Lemmas about `even_part` and `odd_part` which may be factored out in a later revision -/

/-- The greatest multiple of 2 that divides `n`. -/
def even_part (n : ℕ) := ord_proj[2] n

/-- The greatest odd divisor of `n`. -/
def odd_part (n : ℕ) := ord_compl[2] n

@[simp] lemma odd_part_zero : odd_part 0 = 0 := rfl

lemma odd_of_odd_part (n : ℕ) (hn0: n ≠ 0) : odd (odd_part n) :=
begin
  rw odd_iff_not_even,
  unfold odd_part,
  intro H,
  obtain ⟨k, hk⟩ := H,
  rw ←two_mul at hk,
  apply pow_succ_factorization_not_dvd hn0 prime_two,
  rw [pow_add, pow_one, dvd_iff_exists_eq_mul_left],
  use k,
  rw [mul_rotate', mul_comm, ←hk, mul_comm, nat.mul_div_cancel' (ord_proj_dvd n 2)],
end

lemma even_part_mul_odd_part (n : ℕ) : (even_part n) * (odd_part n) = n :=
begin
  simp only [even_part, odd_part, ord_proj_mul_ord_compl_eq_self n 2],
end

lemma mul_even_part (n m : ℕ) (hn0 : n ≠ 0) (hm0 : m ≠ 0) :
  even_part (n * m) = even_part(n) * even_part(m) :=
begin
  simp only [even_part, mul_ord_proj 2 hn0 hm0],
end

lemma mul_odd_part (n m : ℕ) : odd_part (n * m) = odd_part(n) * odd_part(m) :=
begin
  simp only [odd_part, mul_ord_compl n m 2],
end

/-! ## Lemmas about Miller–Rabin witnesses and strong probable primes -/

/-- Letting `k := odd_part (n-1)`, if there is an `0 < a < n` such that `(a^k - 1) ≠ 0 (mod n)` and
`(a^(2^i * k) + 1) ≠ 0 (mod n)` for all `0 ≤ i < (n-1).factorization 2` then this demonstrates
that `n` is not prime. Such an `a` is called a **Miller–Rabin witness** for `n`. We formulate this
in terms of `a : zmod n` to take care of the bounds on `a` and the congruences `mod n`. -/
def nat.miller_rabin_witness (n : ℕ) (a : zmod n) : Prop :=
  a^odd_part (n-1) ≠ 1 ∧
  ∀ i ∈ range ((n-1).factorization 2), a^(2^i * odd_part (n-1)) ≠ -1

/-- `n` is a **strong probable prime** relative to base `a : zmod n` iff
`a` is not a Miller-Rabin witness for `n`. -/
def strong_probable_prime (n : nat) (a : zmod n) : Prop :=
  a^(odd_part (n-1)) = 1 ∨
  (∃ r : ℕ, r < (n-1).factorization 2 ∧ a^(2^r * odd_part(n-1)) = -1)

lemma strong_probable_prime_iff_nonwitness (n : nat) (a : (zmod n)) :
  strong_probable_prime n a ↔ ¬ n.miller_rabin_witness a :=
by simp [nat.miller_rabin_witness, strong_probable_prime, not_and_distrib]

instance {n : ℕ} {a : zmod n} : decidable (strong_probable_prime n a) := or.decidable


-- A proof of `strong_probable_prime_of_prime` using the factorisation of the
-- polymomial discussed in the introduction rather than `repeated_halving_of_exponent`.
/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime'' (p : ℕ) (pp : p.prime) (a : zmod p) (ha0 : a ≠ 0) :
  strong_probable_prime p a :=
begin
  haveI : fact (p.prime) := fact_iff.2 pp,
  have fermat := zmod.pow_card_sub_one_eq_one ha0,
  rw [←even_part_mul_odd_part (p-1), even_part] at fermat,
  set e := (p-1).factorization 2 with he,
  set k := odd_part (p-1) with hk,
  have h1 := factorize_poly' a k e,
  simp only [fermat, sub_self, Ico_zero_eq_range, zero_eq_mul] at h1,
  apply or.imp (λ h, sub_eq_zero.mp h) (λ h, _) h1,
  rcases finset.prod_eq_zero_iff.1 h with ⟨i, hi1, hi2⟩,
  refine ⟨i, mem_range.1 hi1, _⟩,
  have : a ^ (2 ^ i * k) + 1 - 1 = -1, { simp [hi2] },
  simpa using this,
end


/-! ## Lemmas about Miller–Rabin sequences -/

/-- Letting `e := (n-1).factorization 2` and `k := odd_part (n-1)`, the **Miller-Rabin sequence**
for `n` generated by `a : zmod n` is the sequence of values `[a^k, a^2k, a^4k, ..., a^(2^(e-1)*k)]`.
Read in reverse, it is the sequence obtained by repeatedly taking the square root of
`a^(n-1) = a^(2^e * k)` until we reach an odd power of `a`.
-/
def nat.miller_rabin_sequence (n : ℕ) (a : zmod n) : list (zmod n) :=
  list.map (λ i, a^(2^i * odd_part (n-1))) (list.range ((n-1).factorization 2))

-- #eval nat.miller_rabin_sequence 57 (2 : zmod 57)    -- = [2^7, 2^14, 2^28] = [14, 25, 55]
-- #eval to_bool (1 ∈ nat.miller_rabin_sequence 57 (2 : zmod 57))
-- #eval to_bool (-1 ∈ nat.miller_rabin_sequence 57 (2 : zmod 57))
-- #eval to_bool (-1 ∈ nat.miller_rabin_sequence 1373653 (2 : zmod 1373653))

lemma length_miller_rabin_sequence (n : ℕ) (a : zmod n) :
  (n.miller_rabin_sequence a).length = (n-1).factorization 2 :=
by simp [nat.miller_rabin_sequence]

lemma nat.mem_miller_rabin_sequence (n : ℕ) (a b : zmod n) :
  b ∈ n.miller_rabin_sequence a ↔
  ∃ i ∈ range ((n-1).factorization 2), a^(2^i * odd_part (n-1)) = b :=
by simp [nat.miller_rabin_sequence]

/-- The Miller-Rabin sequence for `n` generated by `a` determines whether `a` is a witness for `n`.
Specifically, `a` is not a witness for `n` iff every element of the sequence is `1`
or if the sequence contains `-1`. -/
lemma strong_probable_prime_iff_miller_rabin_sequence {n : ℕ} (a : zmod n)
  (hn : odd n) (hn1 : n ≠ 1) :
  strong_probable_prime n a ↔
    (∀ x ∈ n.miller_rabin_sequence a, x = ↑1) ∨ ((-1 : zmod n) ∈ n.miller_rabin_sequence a) :=
begin
  rw strong_probable_prime_iff_nonwitness,
  unfold nat.miller_rabin_witness,
  unfold nat.miller_rabin_sequence,
  rw not_and_distrib,
  simp only [not_not, mem_range, not_forall, exists_prop, list.mem_map, list.mem_range, cast_one,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  split,
  { apply or.imp_left,
    intros h x hx,
    simp [mul_comm, pow_mul, h] },
  { intros h,
    cases h with h3 h4,
    { left, simpa using h3 0 (factorization_two_pos_sub_one hn hn1) },
    { simp [h4] } },
end

lemma one_not_miller_rabin_witness (n : ℕ) : ¬ n.miller_rabin_witness (1 : zmod n) :=
by simp [nat.miller_rabin_witness]

lemma minus_one_not_miller_rabin_witness {n : ℕ} (hn : odd n) (hn1 : n ≠ 1) :
  ¬ n.miller_rabin_witness (-1 : zmod n) :=
begin
  rw [←strong_probable_prime_iff_nonwitness,
      strong_probable_prime_iff_miller_rabin_sequence (-1 : zmod n) hn hn1,
      nat.mem_miller_rabin_sequence],
  refine or.inr ⟨0, mem_range.2 (factorization_two_pos_sub_one hn hn1), _⟩,
  obtain ⟨k, rfl⟩ := hn,
  apply odd.neg_one_pow,
  simp only [pow_zero, add_succ_sub_one, add_zero, one_mul],
  apply odd_of_odd_part,
  simpa using hn1,
end


/-! ## An alternative route to proving that every prime is a strong probable prime -/

/-- Let `a^e = 1 (mod p)`. (e.g. for prime `p` we have `a^(p-1) = 1` by Fermat's Little Theorem.)
Let `s := e.factorization 2` and `d := odd_part e` as in the definition of `strong_probable_prime`.
Consider the sequence `⟨a^e = a^(2^(s)*d), a^(2^(s-1)*d), a^(2^(s-2)*d), ..., a^(2*d), a^(d)⟩`.
Each term is a square root of the prevous one. Since `a^e = 1`, the 2nd term is congruent to `±1`.
If it is `+1` then the next term, being a square root, is again congruent to `±1`.
By iteration, then, either all terms including `a^d` are congruent to `+1`,
or there is a member of the sequence congruent to `-1`, i.e. `∃ r < s` such that `a^(2^(r)*d) = -1`.
-/
lemma repeated_halving_of_exponent {p : ℕ} [fact (p.prime)] {a : zmod p} {e : ℕ} (h : a ^ e = 1) :
  a^(odd_part e) = 1 ∨
  (∃ r : ℕ, r < e.factorization 2 ∧ a^(2^r * odd_part e) = -1) :=
begin
  rw ←even_part_mul_odd_part e at h,
  rw even_part at h,
  revert h,
  set d := odd_part e with hd,
  induction e.factorization 2 with i IH,
  { simp },
  { intro h,
    rw [pow_succ, mul_assoc, pow_mul'] at h,
    cases (square_roots_of_one h) with h1 h2,
    { rcases (IH h1) with h3 | ⟨r', hr', har'⟩, { simp [h3] },
      exact or.inr ⟨r', nat.lt.step hr', har'⟩ },
    { exact or.inr ⟨i, lt_add_one i, h2⟩ } },
end


-- An alternative proof of `strong_probable_prime_of_prime` not using `repeated_halving_of_exponent`
/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime' (p : ℕ) (pp : p.prime) (a : zmod p) (ha0 : a ≠ 0) :
  strong_probable_prime p a :=
begin
  rcases prime.eq_two_or_odd' pp with rfl | hp,
  { fin_cases a,
    { simpa using ha0 },
    { simpa [strong_probable_prime, odd_part] } },
  haveI : fact (p.prime) := fact_iff.2 pp,
  have fermat := zmod.pow_card_sub_one_eq_one ha0,
  unfold strong_probable_prime,
  rw [←even_part_mul_odd_part (p-1), mul_comm, pow_mul, even_part] at fermat,
  revert fermat,
  induction (p-1).factorization 2 with i IH, { simp },
  intro fermat,
  rw [pow_succ, pow_mul'] at fermat,
  cases (square_roots_of_one fermat) with h1 h2,
  { rcases (IH h1) with h3 | ⟨r', hr', har'⟩, { simp [h3] },
    exact or.inr ⟨r', nat.lt.step hr', har'⟩ },
  { rw [←pow_mul, mul_comm] at h2,
    refine or.inr ⟨i, lt_add_one i, h2⟩ } ,
end

/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a  :=
begin
  rw strong_probable_prime,
  apply repeated_halving_of_exponent (zmod.pow_card_sub_one_eq_one ha),
end

/-! ## Lemmas about Fermat witnesses and Fermat candidate-primes -/

/-- Fermat's Little Theorem (`zmod.pow_card_sub_one_eq_one`) says that for prime `p` and for all
nonzero `a : zmod p` we have `a^(p-1) = 1`.  Thus for (odd) `n : ℕ` if we have nonzero `a : zmod n`
such that `a^(n-1) ≠ 1` then this demonstrates that `n` is not prime.  Such an `a` is called a
**Fermat witness** for `n`. -/
def nat.fermat_witness (n : ℕ) (a : zmod n) : Prop := a ^ (n - 1) ≠ 1

/-- `n` is a **Fermat candidate-prime** relative to base `a : zmod n` iff `a` is not a
Fermat witness for `n`. Note that Conrad calls these "Fermat pseudoprimes", but the word
"pseudoprime" is standarly reserved for *composite* numbers that pass some primality test. -/
def fermat_cprime (n : nat) (a : zmod n) : Prop := a ^ (n - 1) = 1

lemma fermat_cprime_iff_nonwitness (n : nat) (a : (zmod n)) :
  fermat_cprime n a ↔ ¬ n.fermat_witness a :=
by simp [fermat_cprime, nat.fermat_witness]

/-- If `a : zmod n` is a Fermat witness for `n` then it is also a Miller-Rabin witness for `n`. -/
lemma nat.miller_rabin_witness_of_fermat_witness (n : ℕ) (a : zmod n) (h : n.fermat_witness a) :
  n.miller_rabin_witness a :=
begin
  simp only [nat.miller_rabin_witness, nat.fermat_witness] at *,
  refine ⟨_, _⟩,
  { contrapose! h, rw [←even_part_mul_odd_part (n-1), mul_comm, pow_mul, h, one_pow] },
  { rintros i hi,
    rw mem_range at hi,
    rcases exists_pos_add_of_lt hi with ⟨j, hj0, hj⟩,
    contrapose! h,
    rw [←even_part_mul_odd_part (n-1)],
    rw [mul_comm, pow_mul] at *,
    rw [even_part, ←hj, pow_add, pow_mul, h],
    exact even.neg_one_pow ((nat.even_two_pow_iff j).2 hj0) },
end

/-- If there is a base `a : zmod n` relative to which `n` is a strong probable prime
then `n` is a Fermat candidate-prime relative to base `a`. -/
lemma fermat_cprime_of_strong_probable_prime (n : ℕ) (a : zmod n)
  (h : strong_probable_prime n a) : fermat_cprime n a :=
begin
  have := mt (nat.miller_rabin_witness_of_fermat_witness n a),
  rw [←fermat_cprime_iff_nonwitness, ←strong_probable_prime_iff_nonwitness] at this,
  exact this h,
end


--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

open_locale nat  -- to use `φ` for `nat.totient`

/-- Theorem 3.4 of Conrad -/
lemma strong_probable_prime_of_prime_power_iff (p α : ℕ) (hα0 : 0 < α) (hp : nat.prime p)
  (a : zmod (p^α)) : strong_probable_prime (p^α) a ↔ a^(p-1) = 1 :=
begin
  have two_le_p : 2 ≤ p := nat.prime.two_le hp,
  have one_lt_n : 1 < p ^ α :=
    nat.succ_le_iff.mp (two_le_p.trans (le_self_pow hp.one_lt.le (succ_le_iff.mpr hα0))),
  have zero_lt_n : 0 < p^α := pos_of_gt one_lt_n,
  haveI : fact (0 < p ^ α), { exact {out := zero_lt_n}, },
  have hp_sub1_dvd := sub_one_dvd_pow_sub_one p α hp.pos,

  split,
  { -- Given that `a` is a Miller-Rabin nonwitness for `n = p^α`, prove `a^(p-1) = 1`
    intro hspp,
    -- Euler's theorem tells us that `a^φ(n) = 1`.
    have euler : a ^ φ(p^α) = 1,
    { have a_unit : is_unit a,
      { apply is_unit_of_pow_eq_one _ (p^α - 1),
        { exact fermat_cprime_of_strong_probable_prime _ _ hspp },
        { simp only [tsub_pos_iff_lt, one_lt_n] } },
      have coe_this := congr_arg coe (zmod.pow_totient (is_unit.unit a_unit)),
      rw units.coe_one at coe_this,
      rw [←coe_this, units.coe_pow],
      congr },

    -- Since p^α is a strong probable prime to base a, we have a^(p^α - 1) = 1
    have h2 := fermat_cprime_of_strong_probable_prime (p^α) a hspp,
    rw fermat_cprime at h2,

    -- Thus the order of a mod n divides gcd(φ(n), n-1)
    rw ← order_of_dvd_iff_pow_eq_one at euler h2 ⊢,

    -- So all that remains is to show that this gcd(φ(n), n-1) is p-1
    suffices : (φ(p^α)).gcd (p^α - 1) = p - 1, { rw ←this, exact nat.dvd_gcd euler h2 },

    rw nat.totient_prime_pow hp hα0,
    refine nat.gcd_mul_of_coprime_of_dvd _ hp_sub1_dvd,

    -- p is relatively prime to p^α - 1
    apply nat.coprime.pow_left,
    rw ←nat.coprime_pow_left_iff hα0,
    exact coprime_self_sub_one (p^α) zero_lt_n },


  { -- Given that `a^(p-1) = 1`, prove `a` is a Miller-Rabin nonwitness for `n = p^α`
    intro h,

    set f := (p-1).factorization 2 with hf,
    set l := odd_part (p - 1) with hl,
    have hl_odd : odd l, { apply odd_of_odd_part, simp [hp.one_lt] },

    set e := (p^α - 1).factorization 2 with he,
    set k := odd_part (p^α - 1) with hk,
    have hk_odd : odd k, { apply odd_of_odd_part, simp [one_lt_n] },

    have hfe : f ≤ e,
    { refine (factorization_le_iff_dvd (by simp [hp.one_lt]) _).2 hp_sub1_dvd 2, simp [one_lt_n] },

    have hlk : l ∣ k,
    { simp_rw [hl, hk], apply ord_compl_dvd_ord_compl_of_dvd hp_sub1_dvd },

    -- Since (a^l)^(2^f) = 1, the order of (a^l) is 2^j for some 0 ≤ j ≤ f
    have H : ∃ (j : ℕ) (H : j ≤ f), order_of (a^l) = 2^j,
    { have H1 : (a^l)^(even_part (p-1)) = 1,
      { rw [← pow_mul, mul_comm, even_part_mul_odd_part (p-1), h],},
      rw ←nat.dvd_prime_pow nat.prime_two,
      exact order_of_dvd_of_pow_eq_one H1 },
    rcases H with ⟨j, hjf, hj⟩,
    rcases eq_or_ne j 0 with rfl | hj0,
    -- If j=0 then a^l = 1. So since l ∣ k, we have a^k = 1 and so `a` is a Miller-Rabin nonwitness.
    { rw [pow_zero, order_of_eq_one_iff] at hj,
      left,
      rcases hlk with ⟨q, hq⟩,
      rw [←hk, hq, pow_mul, hj, one_pow],},
    -- In the case where j ≥ 1 we will show that (a^k)^(2^(j-1)) = -1, and so `a` is a nonwitness.
    {
      right,
      rw [←he, ←hk],

      -- Since j ≤ f ≤ e we have j-1 < e,
      -- so all that remains is to show that a ^ (2^(j-1) * k) = -1 (mod p^α)
      refine ⟨j-1, lt_of_lt_of_le (pred_lt hj0) (hjf.trans hfe), _⟩,

      have h_order : (a^l)^(2^j) = 1, { rw ←hj, apply pow_order_of_eq_one },


      set x := (a^l)^(2^(j-1)) with hx,

      have hx1 : x ≠ 1, {
        intro H,
        rw [H, eq_comm] at hx,
        apply @pow_ne_one_of_lt_order_of' _ (a^l) (2^(j-1)) _ _ _ hx,
        { apply pow_ne_zero (j-1) (show 2 ≠ 0, by linarith) },
        { rw hj, exact pow_lt_pow (show 1 < 2, by linarith) (pred_lt hj0) } },

      have hx2 : x^2 = 1, {
        rw hx,
        rw ←pow_mul,
        apply order_of_dvd_iff_pow_eq_one.1,
        rw hj,
        have : 2 ^ (j - 1) * 2 = 2^j,
        { nth_rewrite_rhs 0 ←(tsub_add_cancel_of_le (succ_le_iff.mpr hj0.bot_lt)),
          simp [pow_add] },
        rw this },

      have hx1' : ¬ (p^l : zmod (p^α)) ∣ x - 1, { sorry },
      have hx2' : (p^l : zmod (p^α)) ∣ x^2 - 1, { sorry },

      have h3 : (p^l : zmod (p^α)) ∣ (x+1) * (x-1),
      { simpa [←_root_.sq_sub_sq] using hx2' },

      have h4 : (p^l : zmod (p^α)) ∣ x + 1 ∨ (p : zmod (p^α))^l ∣ x - 1, { sorry },
      have h4' : (p^l : zmod (p^α)) ∣ x + 1 := (or_iff_left hx1').1 h4,
      have h5 : (p^α : zmod (p^α)) ∣ x + 1, { sorry },
      have h6 : x = -1, {
        suffices : x + 1 = 0, { rw [←add_sub_cancel x 1, this], simp },
        cases h5 with i hi,
        rw hi,
        have : ((p^α) : zmod (p^α)) = 0, {
          have := @zmod.nat_cast_self (p^α),
          convert this,
          rw eq_comm,
          -- have := coe_pow



          sorry },
        rw this,
        simp, },

      rw [hx, ←pow_mul, mul_comm, pow_mul] at h6,
      rw pow_mul,
      cases hlk with q hq,
      rw [hq, pow_mul, h6],
      rw [hq, odd_mul] at hk_odd,
      exact odd.neg_one_pow hk_odd.2,
    },
  },
end

    -- by_cases j = 0,
    -- { rw strong_probable_prime,
    --   have hfoo : a ^ odd_part (p - 1) = 1,
    --   { have stuff : order_of (a ^ odd_part (p - 1)) = 1,
    --     rw hj,
    --     rw h,
    --     rw pow_zero,
    --     rw order_of_eq_one_iff at stuff,
    --     rw stuff },
    --   left,
    --   have thing := sub_one_dvd_pow_sub_one p α hp.one_lt.le,
    --   rw dvd_iff_exists_eq_mul_left at thing,
    --   rcases thing with ⟨c, hc⟩,
    --   rw [hc, mul_odd_part, mul_comm, pow_mul, hfoo, one_pow] },




#exit


--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------


-- https://leanprover.zulipchat.com/#narrow/stream/217875/near/277098292
def pow_eq_one_subgroup (n e : ℕ) [fact (0 < n)] : subgroup ((zmod n)ˣ) :=
{ carrier := ((finset.univ : finset ((zmod n)ˣ)).filter (λ (a : (zmod n)ˣ), a^e = 1)),
  one_mem' := by simp,
  mul_mem' := begin
    simp,
    intros a b ha hb,
    rw [mul_pow, ha, hb, mul_one],
  end,
  inv_mem' := begin
    simp,
  end }

def pow_alt_subgroup (n e : ℕ) [fact (0 < n)] : subgroup ((zmod n)ˣ) :=
{ carrier := ((finset.univ : finset ((zmod n)ˣ)).filter (λ (a : (zmod n)ˣ), a^e = 1 ∨ a^e = -1)),
  one_mem' := by simp,
  mul_mem' := begin
    simp,
    intros a b ha hb,
    cases ha with ha1 ha2,
    cases hb with hb1 hb2,
    simp_rw [mul_pow, ha1, hb1, mul_one, eq_self_iff_true, true_or],
    simp_rw [mul_pow, ha1, hb2, one_mul, eq_self_iff_true, or_true],
    cases hb with hb1 hb2,
    simp_rw [mul_pow, ha2, hb1, mul_one, eq_self_iff_true, or_true],
    simp_rw [mul_pow, ha2, hb2, mul_neg, mul_one, neg_neg, eq_self_iff_true, true_or],
  end,
  inv_mem' := begin
    simp,
    intros a ha,
    cases ha with ha1 ha2,
    simp_rw [ha1, eq_self_iff_true, true_or],
    simp_rw [ha2, inv_neg'],
    simp,
  end }

/-- Every positive natural is of the form of one of the rec_on_prime_coprime recursors. -/
lemma coprime_factorization_or_prime_power (n : ℕ) (h : 0 < n) :
  (∃ (n0 n1 : ℕ), nat.coprime n0 n1 ∧ n0 * n1 = n ∧ 1 < n0 ∧ 1 < n1) ∨
  (∃ (p k : ℕ), p.prime ∧ p^k = n) :=
begin
  revert h,
  refine nat.rec_on_prime_coprime _ _ _ n,
  { simp, },
  { intros p k hp hn,
    right,
    use p,
    use k,
    split,
    exact hp,
    refl },
  { intros n0 n1 hn0 hn1 hn0n1 hn0' hn1' hmul,
    clear hn0' hn1',
    left,
    use n0,
    use n1,
    split,
    exact hn0n1,
    split,
    rw eq_self_iff_true,
    trivial,
    split,
    exact hn0,
    exact hn1 }
end

lemma one_or_coprime_factorization_or_prime_power (n : ℕ) (h : 0 < n) :
  (n = 1) ∨
  (∃ (n0 n1 : ℕ), nat.coprime n0 n1 ∧ n0 * n1 = n ∧ 1 < n0 ∧ 1 < n1) ∨
  (∃ (p k : ℕ), 1 ≤ k ∧ p.prime ∧ p^k = n) :=
begin
  by_cases is_one : n = 1,
  left,
  exact is_one,
  rcases coprime_factorization_or_prime_power n h with ⟨n0, n1, h01⟩,
  -- cases one with roo too,
  right,
  left,
  use n0,
  use n1,
  exact h01,
  right,
  right,
  rcases h_1 with ⟨p, k, hpk⟩,
  use p,
  use k,
  split,
  by_contra hk,
  simp at hk,
  rw hk at *,
  clear hk,
  simp at *,
  work_on_goal 1 { cases hpk, induction hpk_right, simp at *, assumption }, assumption,
end

-- noncomputable instance subgroup_fintype {G : Type} [fintype G] [group G] {H : subgroup G} :
  -- fintype H := subgroup.fintype H
-- begin
--   -- library_search
--   tidy,
--   sorry,
-- end

-- lemma card_finite_subgroup_eq_card_carrier {α : Type} [fintype α] [group α] (s : finset α)
--   (hmul : ∀ a b ∈ s, a * b ∈ s) (hid : (1 : α) ∈ s)
--   (hinv : ∀ a ∈ s, a⁻¹ ∈ s)  :
--   finset.card s = fintype.card (subgroup.mk (s : set α) (by tidy) (by tidy) (by tidy)) :=
-- begin
--   -- simp, -- fails
--   -- rw subgroup.card_coe_sort, -- doesn't exist
--   tidy,
--   rw ← subgroup.mem_carrier,
--   sorry,
-- end

-- Version of Lagrange's theorem using the formalism of a closed subset
lemma card_closed_subset_dvd_card {α : Type} [fintype α] [group α] (s : finset α)
  (closed_under_mul : ∀ a b ∈ s, a * b ∈ s) (closed_under_inv : ∀ a ∈ s, a⁻¹ ∈ s)
  (id_mem : (1 : α) ∈ s)  :
  finset.card s ∣ fintype.card α :=
begin
  let s_subgroup : subgroup α := subgroup.mk (s : set α) _ _ _,
  classical,
  have : s.card = fintype.card s_subgroup,
  { unfold_coes,
    simp only [subgroup.mem_mk, finset.mem_coe] at *,
    rw fintype.card_subtype,
    congr,
    ext,
    simp_rw [finset.mem_filter, finset.mem_univ, true_and] },
  rw this,
  convert subgroup.card_subgroup_dvd_card s_subgroup,
  { intros a b ha hb, simp only [finset.mem_coe] at *, solve_by_elim, },
  { assumption, },
  { assumption, },
end

noncomputable
instance fintype.of_subgroup {G : Type} [fintype G] [group G] {H : subgroup G} : fintype H :=
fintype.of_finite ↥H

lemma card_le_half_of_proper_subgroup {G : Type} [fintype G] [group G] {H : subgroup G}
-- [fintype H]
  (x : G) (proper : x ∉ H) : (fintype.card H) * 2 ≤ (fintype.card G) :=
begin
  rcases subgroup.card_subgroup_dvd_card H with ⟨index, hindex⟩,
  by_cases h0 : index = 0,
  { exfalso,
    rw h0 at hindex,
    simp at hindex,
    have thing2 : 0 < fintype.card G,
    exact fintype.card_pos,
    rw hindex at thing2,
    exact nat.lt_asymm thing2 thing2 },
  by_cases h1 : index = 1,
  { by_contra,
    rw h1 at hindex,
    simp at hindex,
    clear h h0 h1 index,
    have htop := subgroup.eq_top_of_card_eq H hindex.symm,
    clear hindex,
    rw htop at *,
    clear htop,
    apply proper,
    simp only [subgroup.mem_top] },
  have two_le_index : 2 ≤ index,
  { by_contra,
    simp at h,
    interval_cases index,
    exact h0 rfl,
    exact h1 rfl },
  rw hindex,
  exact mul_le_mul_left' two_le_index (fintype.card ↥H),
end


instance (n : ℕ) [hn_pos : fact (0 < n)] :
  decidable_pred (@is_unit (zmod n) _) :=
λ a, begin
  exact fintype.decidable_exists_fintype,
end

/-- The finset of units of zmod n -/
def finset_units (n : ℕ) [hn_pos : fact (0 < n)] : finset (zmod n) :=
(finset.univ : finset (zmod n)).filter is_unit


-- -- finite subgroup

-- -- the cardinality of a subgroup is the cardinality of its carrier
-- lemma card_subgroup_eq_card_carrier {G : Type} [group G] [fintype G] {H : subgroup G} :
--   fintype.card H = finset.card (H.carrier : finset G) :=
-- begin

-- end

-- lemma foocard (n e : ℕ) [fact (0 < n)] :
--   (fintype.card (↥(pow_alt_subgroup n e)) : ℕ)
--   = finset.card ((finset.univ : finset ((zmod n)ˣ)).filter
  -- (λ (a : (zmod n)ˣ), a^e = 1 ∨ a^e = -1))
--   :=
-- begin
--   rw fintype.card,
--   -- simp,
-- end


lemma unlikely_strong_probable_prime_of_coprime_mul (n : ℕ) [hn_pos : fact (0 < n)]
  (h : (∃ (n0 n1 : ℕ), nat.coprime n0 n1 ∧ n0 * n1 = n ∧ 1 < n0 ∧ 1 < n1))
  (not_prime : ¬ n.prime) :
  ((finset_units n).filter (λ a, strong_probable_prime n a)).card * 2 ≤ (finset_units n).card :=
begin
  rcases h with ⟨n0, n1, h_coprime, h_mul, hn0, hn1⟩,
  let i0 := ((finset.range (odd_part (n-1))).filter (λ i, ∃ a_0 : zmod n, a_0^(2^i) = -1)).max'
  ( by
    { rw finset.filter_nonempty_iff,
      use 0,
      simp only [finset.mem_range, pow_zero, pow_one, exists_apply_eq_apply, and_true],
      by_contra,
      simp at h,
      have hn' : n - 1 ≠ 0,
      { rw [ne.def, tsub_eq_zero_iff_le, not_le, ← h_mul],
        exact one_lt_mul hn0.le hn1 },
      apply hn',
      clear hn',
      rw ← even_part_mul_odd_part (n - 1),
      rw [h, mul_zero] } ),
  have h_proper : ∃ x, x ∉ (pow_alt_subgroup n (i0 * odd_part(n - 1))),
  { -- nat.chinese_remainder'_lt_lcm
    -- nat.chinese_remainder_lt_mul
    sorry },
  rcases h_proper with ⟨x, hx⟩,
  have hsubgroup :
    (finset.filter (λ (a : zmod n), strong_probable_prime n a) (finset_units n)).card * 2
    ≤ fintype.card ↥(pow_alt_subgroup n (i0 * odd_part (n - 1))) * 2,
  { simp [mul_le_mul_right],
    -- rw foocard,
    sorry,  },
  apply trans hsubgroup,
  clear hsubgroup,
  convert card_le_half_of_proper_subgroup x hx using 1,
  { -- TODO(Bolton):
    sorry, },

end

lemma unlikely_strong_probable_prime_of_prime_power (n : ℕ) [hn_pos : fact (0 < n)] (h1 : 1 < n)
  (h : (∃ (p k : ℕ), p.prime ∧ p^k = n)) (not_prime : ¬ n.prime) :
  ((finset_units n).filter (λ a, strong_probable_prime n a)).card * 2 ≤ (finset_units n).card :=
begin
  rcases h with ⟨p, k, p_prime, n_pow⟩,
  have n_pos : 0 < n, exact hn_pos.out,
  have one_lt_k : 1 < k,
  { by_contra,
    simp at h,
    interval_cases k,
    simp at n_pow,
    rw n_pow at h1,
    exact nat.lt_asymm h1 h1,
    { apply not_prime,-- TODO(Sean)
      sorry } },
  sorry,
end


lemma unlikely_strong_probable_prime_of_composite (n : ℕ) [hn_pos : fact (0 < n)] (hn1 : 1 < n)
  (not_prime : ¬ n.prime) :
  ((finset_units n).filter (λ a, strong_probable_prime n a)).card * 2 ≤ (finset_units n).card :=
begin
  cases one_or_coprime_factorization_or_prime_power n (hn_pos.out),
  { exfalso,
    -- TODO(Sean)
    sorry },
  -- clear hn1,
  cases h,
  { apply unlikely_strong_probable_prime_of_coprime_mul,
    exact h,
    exact not_prime },
  { -- n is a prime power
    -- TODO(Sean): unlikely_strong_probable_prime_of_prime_power should be able to finish this
    sorry },
end
