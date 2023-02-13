/-
Copyright (c) 2023 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/

import number_theory.divisors

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

/--
The only prime number which is highly composite is 2.
-/
lemma eq_two_of_prime {n : ℕ} (h₁ : n.highly_composite) (h₂ : n.prime) : n = 2 :=
begin
  by_cases h₃ : 2 < n,
  { have hc : 2 < n.divisors.card := h₁ 2 h₃,
    have : ({1, n} : finset ℕ).card = 2 := by simp [ne_of_lt (lt_of_succ_lt h₃)],
    rw [h₂.divisors, this] at hc,
    exact absurd rfl (ne_of_lt hc) },
  { rcases n with n | n | n,
    { exact absurd h₂ not_prime_zero },
    { exact absurd h₂ not_prime_one },
    { rw le_zero_iff.mp (le_of_succ_le_succ (le_of_succ_le_succ (not_lt.mp h₃))) } }
end

end nat
