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
import number_theory.padics.padic_norm
import field_theory.finite.basic
import data.fintype.basic

-- TODO add reference to [this](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf)

def two_power_part (n : ℕ) := 2 ^ (padic_val_nat 2 n)

def odd_part (n : ℕ) := n / two_power_part n

lemma mul_two_power_part_odd_part (n : ℕ) : (two_power_part n) * (odd_part n) = n :=
begin
  have : two_power_part n ∣ n,
  { rw two_power_part,
    exact pow_padic_val_nat_dvd, },
  rw odd_part,
  exact nat.mul_div_cancel' this,
end

def strong_probable_prime (n : nat) (a : zmod n) : Prop :=
a^(odd_part (n-1)) = 1 ∨ (∃ r : ℕ, r < padic_val_nat 2 (n-1) ∧ a^(2^r * odd_part(n-1)) = -1)

instance {n : ℕ} {a : zmod n} : decidable (strong_probable_prime n a) := or.decidable

def binpow {M} [has_one M] [has_mul M] (m : M) : ℕ → M :=
nat.binary_rec 1 (λ b _ ih, let ih2 := ih * ih in cond b (m * ih2) ih2)

def fast_strong_probable_prime (n : nat) (a : zmod n) : Prop :=
binpow a (odd_part (n-1)) = 1
∨ (∃ r : ℕ, r < padic_val_nat 2 (n-1) ∧ binpow a (2^r * odd_part(n-1)) = -1)

instance {n : ℕ} {a : zmod n} : decidable (fast_strong_probable_prime n a) := or.decidable

lemma strong_probable_prime_iff_fast_strong_probable_prime (n : nat) (a : zmod n) :
  strong_probable_prime n a ↔ fast_strong_probable_prime n a :=
begin
  unfold strong_probable_prime,
  unfold fast_strong_probable_prime,
  sorry,
end

-- TODO(Bolton): Find a way of making modular exponentiation faster
-- set_option profiler true
-- #eval to_bool (fast_strong_probable_prime 100003 2)
-- #eval to_bool (fast_strong_probable_prime 1000003 2)
-- #eval to_bool (nat.prime 1000003)
-- #eval to_bool (fast_strong_probable_prime 99999997 4)
-- #eval to_bool (nat.prime 104)

def fermat_pseudoprime (n : nat) (a : zmod n) : Prop :=
a^(n-1) = 1

lemma square_roots_of_one {p : ℕ} [fact (p.prime)] {x : zmod p} (root : x^2 = 1) :
  x = 1 ∨ x = -1 :=
begin
  have root2 : x^2 -1 = 0,
  rw root,
  simp,
  have diffsquare : (x + 1) * (x - 1) = 0,
  ring_nf,
  exact root2,
  have zeros : (x + 1 = 0) ∨ (x - 1 = 0),
  exact zero_eq_mul.mp (eq.symm diffsquare),
  cases zeros with zero1 zero2,
  right,
  exact eq_neg_of_add_eq_zero zero1,
  left,
  exact sub_eq_zero.mp zero2,
end

lemma repeated_halving_of_exponent (p : ℕ) [fact (p.prime)] (a : zmod p)
  (e : ℕ) (h : a ^ e = 1) :
  a^(odd_part e) = 1 ∨ (∃ r : ℕ, r < padic_val_nat 2 e ∧ a^(2^r * odd_part e) = -1) :=
begin
  rw <-mul_two_power_part_odd_part e at h,
  rw two_power_part at h,
  revert h,
  induction padic_val_nat 2 e with i hi,
  { simp, },
  { intros h,
    simp [pow_succ, mul_assoc] at h,
    rw pow_mul' at h,
    have foo := square_roots_of_one h,
    cases foo with h1 h2,
    have roo := hi h1,
    cases roo with h3 h4,
    left,
    exact h3,
    right,
    cases h4 with r' hoo,
    use r',
    cases hoo with rr' a2,
    split,
    exact nat.lt.step rr',
    exact a2,
    right,
    use i,
    split,
    exact lt_add_one i,
    exact h2,
     },
end

lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a :=
begin
  have fermat := zmod.pow_card_sub_one_eq_one ha, -- you'll need this lemma for this
  rw strong_probable_prime,
  apply repeated_halving_of_exponent,
  exact fermat,
end

lemma fermat_pseudoprime_of_strong_probable_prime (n : ℕ) (a : zmod n)
  (h : strong_probable_prime n a) : fermat_pseudoprime n a :=
begin
  unfold strong_probable_prime at h,
  unfold fermat_pseudoprime,
  cases h,
  {
  rw [← mul_two_power_part_odd_part (n - 1), mul_comm, pow_mul, h, one_pow],
  },
  {
    rcases h with ⟨r, hrlt, hpow⟩,
    have h := congr_arg (^(2^(padic_val_nat 2 (n - 1) - r))) hpow,
    simp at h,
    sorry, -- this one seems hard, I would skip it unless you're feeling very confident
  },

end

lemma strong_probable_prime_prime_power_iff (p α : ℕ) (hα : 1 ≤ α) (hp : nat.prime p)
  (a : zmod (p^α)) : strong_probable_prime (p^α) a ↔ a^(p-1) = 1 :=
begin
  have one_lt_n : 1 < p^α,
  {
  clear a,
    -- if p is prime and α ≥ 1, then p^α should always be greater than 1, because p will be at
    -- least two. See if library search finds facts to tell you that p is at least two or that if
    -- you raise a ℕ to a power at least one, it gives a number at least as big.
  have pgeq2 : 2 ≤ p,
  exact nat.prime.two_le hp,
  --have thing1 : p ≤ p ^ 1,
  --have thing2 : 2 ≤ p ^ α,
  have waa : 1 ≤ p,
  exact nat.le_of_succ_le pgeq2,
  have thing3 : p ^ 1 ≤ p ^ α,
  exact pow_mono waa hα,
  -- wait for le_pow to be approved

  sorry,
  },
  have zero_lt_n : 0 < p^α,
  exact pos_of_gt one_lt_n,
  haveI : fact (0 < p ^ α),
  { exact {out := zero_lt_n}, },
  split,
  { intro hspp,
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
    rw nat.totient_prime_pow at euler,
    {
      sorry,
    },
    exact hp,
    exact nat.succ_le_iff.mp hα,
  },
  {
    intro h,
    have foo : (a ^ (odd_part (p - 1)))^(two_power_part (p - 1)) = 1,
    { rw [← pow_mul, mul_comm, mul_two_power_part_odd_part (p - 1), h],},
    have goo : ∃ (j : ℕ) (H : j ≤ padic_val_nat 2 (p-1)), order_of (a ^ (odd_part (p - 1))) = 2^j,
    { have := order_of_dvd_of_pow_eq_one foo,
      rw two_power_part at this,
      rw nat.dvd_prime_pow at this,
      exact this,
      exact nat.prime_two,
    },
    rcases goo with ⟨j, H, hj⟩,
    by_cases j = 0,
    { rw strong_probable_prime,
      sorry,
    },
    {
      sorry,
    },
  },
end

def pow_alt_subgroup (n e : ℕ) [fact (0 < n)] : subgroup ((zmod n)ˣ) :=
{ carrier := ((finset.univ : finset ((zmod n)ˣ)).filter (λ (a : (zmod n)ˣ), a^e = 1 ∨ a^e = -1)),
  one_mem' := by simp,
  mul_mem' := begin
    simp,
    intros a b ha hb,
    sorry, -- TODO(Sean): This should be doable following the lean cheat sheet and using mul_pow
  end,
  inv_mem' := begin
    simp,
    intros a ha,
    sorry, -- TODO(Sean): This should be doable following the lean cheat sheet and using inv_neg' and one_inv,
  end,
}

lemma unlikely_strong_probable_prime_of_composite (n : ℕ) [fact (0 < n)] (not_prime : ¬ n.prime) :
  ((finset.univ : finset (zmod n)).filter (strong_probable_prime n)).card ≤ n / 4 :=
begin
  -- TODO(Bolton): This will be a harder proof. Find some sublemmas that will be needed and
  -- extract them. subgroup.card_subgroup_dvd_card is lagrange's thm
  by_cases h : ∃ (p q : ℕ), p.prime ∧ q.prime ∧ p ∣ n ∧ q ∣ n,
  {
    rcases h with ⟨p, q, p_prime, q_prime, p_dvd, q_dvd⟩,
    let i0 := ((finset.range (odd_part (n-1))).filter (λ i, ∃ a_0 : zmod n, a_0^(2^i) = -1)).max' (
      by {
        rw finset.filter_nonempty_iff,
        use 0,
        simp,
        by_contra,
        simp * at *,
        have hn : 0 < n,
        {
          exact _inst_1.out,
        },
        have hn' : n ≠ 0,
        {
          simp,
          exact ne_of_gt hn,
        },
        apply hn',
        clear hn hn',
        sorry, -- TODO(Sean): Prove this using mul_two_power_part_odd_part
      }
    ),
    let G : subgroup ((zmod n)ˣ) :=
  },
  {
    sorry,
  },
end
