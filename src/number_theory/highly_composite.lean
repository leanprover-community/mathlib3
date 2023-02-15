/-
Copyright (c) 2023 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/

import number_theory.divisors
import tactic

namespace nat

/--
A natural number `n` is highly composite if it has more divisors than any smaller natural number.
Note that `1` and `2` are `highly_composite` despite not actually being composite, and that `0` is
considered highly_composite as a special case.
-/
def highly_composite (n : ℕ) : Prop :=
∀ (m : ℕ), m < n → m.divisors.card < n.divisors.card

instance (n : ℕ) : decidable n.highly_composite :=
nat.decidable_ball_lt n _

lemma zero_highly_composite : highly_composite 0 := dec_trivial

lemma one_highly_composite : highly_composite 1 := dec_trivial

lemma two_highly_composite : highly_composite 2 := dec_trivial

lemma four_highly_composite : highly_composite 4 := dec_trivial

/--
The only prime number which is highly composite is 2.
-/
lemma highly_composite.eq_two_of_prime {n : ℕ} (h₁ : n.highly_composite) (h₂ : n.prime) : n = 2 :=
begin
  by_cases h₃ : 2 < n,
  { have hc : 2 < n.divisors.card := h₁ 2 h₃,
    have : ({1, n} : finset ℕ).card = 2 := finset.card_doubleton (ne_of_lt (lt_of_succ_lt h₃)),
    rw [h₂.divisors, this] at hc,
    exact absurd rfl (ne_of_lt hc) },
  { rcases n with n | n | n,
    { exact absurd h₂ not_prime_zero },
    { exact absurd h₂ not_prime_one },
    { rw le_zero_iff.mp (le_of_succ_le_succ (le_of_succ_le_succ (not_lt.mp h₃))) } }
end

lemma mul_prime_same_factors (n : ℕ) {p q : ℕ} (hp : p.prime) (hq : q.prime) :
  (n * p).divisors.card = (n * q).divisors.card :=
begin
  have transforms : (n * p).divisors.image (λ k, if p ∣ k then k / p * q else k) = (n * q).divisors,
  {
    ext d,
    rw finset.mem_image,
    split,
    {
      rintro ⟨a, H, rfl⟩,
      rw mem_divisors at H ⊢,
      replace H := H.left,
      refine ⟨_, sorry⟩,
      by_cases ha : p ∣ a,
      { simp [ha], -- TODO: Remove non-terminal simp
        rcases ha with ⟨b, rfl⟩,
        rw nat.mul_div_cancel_left _ hp.pos,
        rw mul_comm at H,
        have := nat.dvd_of_mul_dvd_mul_right hp.pos H,
        exact (nat.mul_dvd_mul_iff_right hq.pos).mpr this },
      { simp [ha],
        sorry,
      }
    },
    {
      intro hd,
      rw mem_divisors at hd,
      by_cases ha : p ∣ d,
      {

      },
      sorry
     }
  },
  have inj : set.inj_on (λ k, if p ∣ k then k / p * q else k) ↑(n * p).divisors := sorry,
  rw ←transforms,
  exact (finset.card_image_of_inj_on inj).symm,
end

lemma div_mul_prime_same_factors {n p q : ℕ} (hp : p.prime) (hq : q.prime) (hn : p ∣ n) :
  (n / p * q).divisors.card = n.divisors.card :=
begin
  rcases hn with ⟨k, rfl⟩,
  rw nat.mul_div_cancel_left k hp.pos,
  rw mul_comm p k,
  exact (mul_prime_same_factors k hp hq).symm
end

lemma highly_composite.smaller_prime_dvd {n : ℕ} (hn : n.highly_composite) {p q : ℕ} (hp : p.prime)
  (hq : q.prime) (ha : p ∣ n) (hb : q < p) : q ∣ n :=
begin
  by_contra,
  have hm₁ : (n / p * q).divisors.card = n.divisors.card := div_mul_prime_same_factors hp hq ha,
  have hm₂ : (n / p * q) < n := sorry,
  exact absurd hm₁ (ne_of_lt (hn _ hm₂)),
end

end nat
