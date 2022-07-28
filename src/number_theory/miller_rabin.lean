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
-- import number_theory.padics.padic_norm
import field_theory.finite.basic
import data.fintype.basic

/-!
# Lemmas and definitions that will be used in proving the Miller-Rabin primality test.

-- TODO add reference to [this](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf)

-/

open nat
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
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

def even_part (n : ℕ) := ord_proj[2] n

def odd_part (n : ℕ) := ord_compl[2] n

@[simp] lemma odd_part_zero : odd_part 0 = 0 := rfl

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

/-- Let `n = 2^s * d + 1`, where `s := (n-1).factorization 2` and `d := odd_part (n-1)`.
Then `n` is a **strong probable prime** relative to a base `a : zmod n` if either
`a^d = 1 (mod n)` or `a ^ (2^r * d) = -1 (mod n)` for some `0 ≤ r < s`. -/
def strong_probable_prime (n : nat) (a : (zmod n)) : Prop :=
  a^(odd_part (n-1)) = 1 ∨
  (∃ r : ℕ, r < (n-1).factorization 2 ∧ a^(2^r * odd_part(n-1)) = -1)

instance {n : ℕ} {a : zmod n} : decidable (strong_probable_prime n a) := or.decidable

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

/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a  :=
begin
  rw strong_probable_prime,
  apply repeated_halving_of_exponent (zmod.pow_card_sub_one_eq_one ha),
end

/-- Fermat's Little Theorem says that this property holds for all primes.
Note that elsewhere the word "pseudoprime" is often reserved for numbers that are not actual primes.
-/
def fermat_pseudoprime (n : nat) (a : zmod n) : Prop :=
a^(n-1) = 1

/-- If there is a base `a` relative to which `n` is a strong probable prime
then `n` is a Fermat pseudoprime. -/
lemma fermat_pseudoprime_of_strong_probable_prime (n : ℕ) (a : zmod n)
  (h : strong_probable_prime n a) : fermat_pseudoprime n a :=
begin
  unfold strong_probable_prime at h,
  unfold fermat_pseudoprime,
  cases h,
  { rw [←even_part_mul_odd_part (n - 1), mul_comm, pow_mul, h, one_pow] },
  { rcases h with ⟨r, hr, hpow⟩,
    have H : a ^ (n - 1) = (-1) ^ 2 ^ (((n - 1).factorization) 2 - r),
    {
      have h := congr_arg (^(2^((n - 1).factorization 2 - r))) hpow,
      simp only at h,
      rw [←h, ←pow_mul a, mul_comm, ←mul_assoc, ←pow_add, nat.sub_add_cancel (le_of_lt hr),
        odd_part, ord_proj_mul_ord_compl_eq_self (n-1) 2],
    },
    rw H,
    apply even.neg_one_pow,
    rw nat.even_two_pow_iff,
    exact tsub_pos_of_lt hr },
end

lemma sub_one_dvd_pow_sub_one (p α : ℕ) (one_le_p : 1 ≤ p) : (p - 1) ∣ (p^α - 1) :=
begin
  induction α with a ih,
  { simp, },
  { rw dvd_iff_exists_eq_mul_left at *,
    rcases ih with ⟨c, hc⟩,
    use p^a + c,
    rw add_mul,
    rw ← hc,
    rw mul_tsub,
    rw mul_one,
    zify,
    rw int.coe_nat_sub (one_le_pow_of_one_le one_le_p a),
    rw int.coe_nat_sub (le_mul_of_one_le_right' one_le_p),
    rw int.coe_nat_sub (one_le_pow_of_one_le one_le_p (nat.succ a)),
    rw pow_succ',
    ring, },
end

lemma coprime_add_one (b : ℕ) : (b + 1).coprime b :=
begin
  simp only [nat.coprime_one_left_iff, nat.coprime_self_add_left],
end

lemma coprime_self_sub_one (a : ℕ) (ha : 0 < a) : a.coprime (a - 1) :=
begin
  have h : a = a - 1 + 1,
  { zify,
    simp, },
    rw [h, nat.add_succ_sub_one, add_zero, nat.coprime_self_add_left, nat.coprime_one_left_iff],
    trivial,
  -- didn't have to use coprime_add_one
end

/-- Theorem 3.4 of Conrad -/
lemma strong_probable_prime_prime_power_iff (p α : ℕ) (hα : 1 ≤ α) (hp : nat.prime p)
  (a : zmod (p^α)) : strong_probable_prime (p^α) a ↔ a^(p-1) = 1 :=
begin
  have two_le_p : 2 ≤ p,
  exact nat.prime.two_le hp,
  have one_le_p : 1 ≤ p,
  exact nat.le_of_succ_le two_le_p,
  have one_lt_n : 1 < p ^ α,
  { clear a,
    exact nat.succ_le_iff.mp (le_trans two_le_p (le_self_pow (nat.le_of_succ_le two_le_p) hα)) },
  have zero_lt_n : 0 < p^α,
  exact pos_of_gt one_lt_n,
  haveI : fact (0 < p ^ α),
  { exact {out := zero_lt_n}, },
  split,
  { -- a is a Miller-Rabin nonwitness for n = p^α
    intro hspp,
    -- Euler's theorem tells us that `a^φ(n) = 1`.
    have euler : a ^ nat.totient (p^α) = 1,
    { have a_unit : is_unit a,
      { apply is_unit_of_pow_eq_one _ (p^α - 1),
        apply fermat_pseudoprime_of_strong_probable_prime,
        assumption,
        simp only [tsub_pos_iff_lt],
        assumption, },
      have := zmod.pow_totient (is_unit.unit a_unit),
      have coe_this := congr_arg coe this,
      rw units.coe_one at coe_this,
      rw <-coe_this,
      rw units.coe_pow,
      congr, },
    rw nat.totient_prime_pow hp (nat.succ_le_iff.mp hα) at euler,
    -- ... both cases imply a^n-1 = 1
    have h2 : a ^ (p^α - 1) = 1,
    { -- since a is a nonwitness, we have either ...
      cases hspp,
      { -- ... a^k = 1
        rw ← even_part_mul_odd_part (p ^ α - 1),
        rw [mul_comm, pow_mul, hspp, one_pow] },
      { -- ... or a^(2^i k) = -1
          rcases hspp with ⟨r, hrlt, hrpow⟩,
          rw lt_iff_exists_add at hrlt,
          rcases hrlt with ⟨c, Hc, hc⟩,
          replace hrpow := congr_arg (^(2^c)) hrpow,
          simp only [] at hrpow,
          convert hrpow using 1,
          { rw [mul_comm (2^r), ← pow_mul, mul_assoc, ← pow_add 2, mul_comm, ← hc,
                ← even_part,
              even_part_mul_odd_part], },
          { simp at Hc,
            rw nat.lt_iff_add_one_le at Hc,
            simp at Hc,
            rw le_iff_exists_add at Hc,
            rcases Hc with ⟨d, hd⟩,
            rw [hd, pow_add 2, pow_one, pow_mul],
            simp }, }, },
    -- Thus the order of a mod n divides (φ(n), n-1)
    rw ← order_of_dvd_iff_pow_eq_one at euler h2 ⊢,
    have order_gcd := nat.dvd_gcd euler h2,
    have gcd_eq : (p ^ (α - 1) * (p - 1)).gcd (p ^ α - 1) = p - 1,
    { apply nat.gcd_mul_of_coprime_of_dvd,
      { -- p is relatively prime to p^α - 1
        apply nat.coprime.pow_left,
        rw ←nat.coprime_pow_left_iff (hα),
        exact coprime_self_sub_one (p ^ α) zero_lt_n },
      {exact sub_one_dvd_pow_sub_one p α one_le_p,} },
    rwa gcd_eq at order_gcd },
  { -- a ^ (p-1) = 1
    intro h,
    have foo : (a ^ (odd_part (p - 1)))^(even_part (p - 1)) = 1,
    { rw [← pow_mul, mul_comm, even_part_mul_odd_part (p - 1), h],},
    have goo : ∃ (j : ℕ) (H : j ≤ (p-1).factorization 2), order_of (a ^ (odd_part (p - 1))) = 2^j,
    { have := order_of_dvd_of_pow_eq_one foo,
      rw even_part at this,
      rw nat.dvd_prime_pow at this,
      exact this,
      exact nat.prime_two },
    rcases goo with ⟨j, H, hj⟩,
    by_cases j = 0,
    { rw strong_probable_prime,
      have hfoo : a ^ odd_part (p - 1) = 1,
      { have stuff : order_of (a ^ odd_part (p - 1)) = 1,
        rw hj,
        rw h,
        rw pow_zero,
        rw order_of_eq_one_iff at stuff,
        rw stuff },
      left,
      have thing := sub_one_dvd_pow_sub_one p α one_le_p,
      rw dvd_iff_exists_eq_mul_left at thing,
      rcases thing with ⟨c, hc⟩,
      rw [hc, mul_odd_part, mul_comm, pow_mul, hfoo, one_pow] },
    { sorry } },
end

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
