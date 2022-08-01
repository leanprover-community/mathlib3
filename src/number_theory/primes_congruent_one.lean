/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.polynomial.cyclotomic.eval

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/

namespace nat

open polynomial nat filter

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
lemma exists_prime_ge_modeq_one {k : ℕ} (n : ℕ) (hpos : 0 < k) :
  ∃ (p : ℕ), nat.prime p ∧ n ≤ p ∧ p ≡ 1 [MOD k] :=
begin
  let b := 3 * (k * n.factorial),
  have hgt : 1 < (eval ↑b (cyclotomic k ℤ)).nat_abs,
  { have hkey : ∀ l : ℕ, 2 < 3 * (l.succ * n.factorial) := λ l, lt_mul_of_lt_of_one_le
          (2 : ℕ).lt_succ_self (le_mul_of_le_of_one_le (nat.succ_pos _) n.factorial_pos),
    rcases k with _ | _ | k,
    { simpa using hpos, },
    { simv only [one_mul, int.coe_nat_mul, int.coe_nat_succ, int.coe_nat_zero, zero_add,
        cyclotomic_one, eval_sub, eval_X, eval_one],
      convert int.nat_abs_lt_nat_abs_of_nonneg_of_lt int.one_nonneg _,
      rw lt_sub_iff_add_lt,
      specialize hkey 0,
      norm_cast,
      rwa one_mul at hkey, },
    calc 1 ≤ _ : by { rw le_tsub_iff_left (one_le_two.trans (hkey _).le), exact (hkey _).le, }
       ... < _ : sub_one_lt_nat_abs_cyclotomic_eval (one_lt_succ_succ k)
                   (one_lt_two.trans (hkey k.succ)).ne.symm, },
  let p := min_fac (eval ↑b (cyclotomic k ℤ)).nat_abs,
  haveI hprime : fact p.prime := ⟨min_fac_prime (ne_of_lt hgt).symm⟩,
  have hroot : is_root (cyclotomic k (zmod p)) (cast_ring_hom (zmod p) b),
  { rw [is_root.def, ← map_cyclotomic_int k (zmod p), eval_map, coe_cast_ring_hom,
    ← int.cast_coe_nat, ← int.coe_cast_ring_hom, eval₂_hom, int.coe_cast_ring_hom,
      zmod.int_coe_zmod_eq_zero_iff_dvd _ _],
    apply int.dvd_nat_abs.1,
    exact_mod_cast min_fac_dvd (eval ↑b (cyclotomic k ℤ)).nat_abs },
  refine ⟨p, hprime.1, _, _⟩,
  { by_contra habs,
    exact (prime.dvd_iff_not_coprime hprime.1).1
      (dvd_factorial (min_fac_pos _) (le_of_not_ge habs))
      (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_left_right },
  { have hdiv := order_of_dvd_of_pow_eq_one (zmod.units_pow_card_sub_one_eq_one p
      (zmod.unit_of_coprime b (coprime_of_root_cyclotomic hpos hroot))),
    have : ¬p ∣ k := hprime.1.coprime_iff_not_dvd.1
      (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_right_right,
    haveI := ne_zero.of_not_dvd (zmod p) this,
    have : k = order_of (b : zmod p) := (is_root_cyclotomic_iff.mp hroot).eq_order_of,
    rw [←order_of_units, zmod.coe_unit_of_coprime, ←this] at hdiv,
    exact ((modeq_iff_dvd' hprime.1.pos).2 hdiv).symm }
end

lemma frequently_at_top_modeq_one {k : ℕ} (hpos : 0 < k) :
  ∃ᶠ p in at_top, nat.prime p ∧ p ≡ 1 [MOD k] :=
begin
  refine frequently_at_top.2 (λ n, _),
  obtain ⟨p, hp⟩ := exists_prime_ge_modeq_one n hpos,
  exact ⟨p, ⟨hp.2.1, hp.1, hp.2.2⟩⟩
end

lemma infinite_set_of_prime_modeq_one {k : ℕ} (hpos : 0 < k) :
  set.infinite {p : ℕ | nat.prime p ∧ p ≡ 1 [MOD k]} :=
frequently_at_top_iff_infinite.1 (frequently_at_top_modeq_one hpos)

end nat
