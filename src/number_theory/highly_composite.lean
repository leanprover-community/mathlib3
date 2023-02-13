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

lemma highly_composite.smaller_prime_dvd {n : ℕ} (hn : n.highly_composite) {p q : ℕ} (hp : p.prime)
  (hq : q.prime) (ha : p ∣ n) (hb : q < p) : q ∣ n :=
begin
  by_contra,
  let m := (n / p) * q,
  have hm₁ : m.divisors.card = n.divisors.card,
  { let embed : ℕ → ℕ := λ d, if p ∣ d then (d / p) * q else d,
    have embed_inj : function.injective embed := sorry,
    have map_embed : n.divisors.map ⟨embed, embed_inj⟩ = m.divisors,
    {
      ext d,
      rw mem_divisors,
      rw finset.mem_map,
      split,
      {
        intro hd,
        rcases hd with ⟨r, hr₁, hr₂⟩,
        rw mem_divisors at hr₁,
        -- change embed r = d at hr₂,
        change (if p ∣ r then (r / p) * q else r) = d at hr₂,
        --rw ite_eq_iff at hr₂,
        by_cases hr₃ : p ∣ r,
        {
          --replace hr₂ := (hr₂.resolve_right sorry).right,
          have : (r / p) * q = d := by sorry; cc,
          rw ← this,
          sorry
        },
        { sorry }
      },
      {
        intro hd,
        sorry
      }
    },
    rw ←map_embed,
    exact finset.card_map ⟨embed, embed_inj⟩ },
  have hm₂ : m < n := sorry,
  exact absurd hm₁ (ne_of_lt (hn m hm₂)),
  /-have ha' : p ∈ n.factors := (nat.mem_factors_iff_dvd sorry hp).mpr ha,
  let smaller_factors : list ℕ := q :: (n / p).factors,
  have : smaller_factors.prod = (n / p) * q := sorry,
  have : smaller_factors.prod < n := sorry,
  have smaller_factors-/
end

end nat
