/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import data.nat.prime_fin
import ring_theory.polynomial.cyclotomic.eval

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/

namespace nat

open polynomial nat filter
open_locale nat

/-- For any positive `k : ℕ` there exists an arbitrarily large prime `p` such that
`p ≡ 1 [MOD k]`. -/
lemma exists_prime_gt_modeq_one {k : ℕ} (n : ℕ) (hk0 : k ≠ 0) :
  ∃ (p : ℕ), nat.prime p ∧ n < p ∧ p ≡ 1 [MOD k] :=
begin
  rcases (one_le_iff_ne_zero.2 hk0).eq_or_lt with rfl | hk1,
  { rcases exists_infinite_primes (n + 1) with ⟨p, hnp, hp⟩,
    exact ⟨p, hp, hnp, modeq_one⟩ },
  let b := k * n!,
  have hgt : 1 < (eval ↑b (cyclotomic k ℤ)).nat_abs,
  { rcases le_iff_exists_add'.1 hk1.le with ⟨k, rfl⟩,
    have hb : 2 ≤ b := le_mul_of_le_of_one_le hk1 n.factorial_pos,
    calc 1 ≤ b - 1 : le_tsub_of_add_le_left hb
    ... < (eval (b : ℤ) (cyclotomic (k + 1) ℤ)).nat_abs :
      sub_one_lt_nat_abs_cyclotomic_eval hk1 (succ_le_iff.1 hb).ne' },
  let p := min_fac (eval ↑b (cyclotomic k ℤ)).nat_abs,
  haveI hprime : fact p.prime := ⟨min_fac_prime (ne_of_lt hgt).symm⟩,
  have hroot : is_root (cyclotomic k (zmod p)) (cast_ring_hom (zmod p) b),
  { rw [is_root.def, ← map_cyclotomic_int k (zmod p), eval_map, coe_cast_ring_hom,
      ← int.cast_coe_nat, ← int.coe_cast_ring_hom, eval₂_hom, int.coe_cast_ring_hom,
      zmod.int_coe_zmod_eq_zero_iff_dvd _ _],
    apply int.dvd_nat_abs.1,
    exact_mod_cast min_fac_dvd (eval ↑b (cyclotomic k ℤ)).nat_abs },
  have hpb : ¬(p ∣ b) :=
    hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic hk0.bot_lt hroot).symm,
  refine ⟨p, hprime.1, not_le.1 $ λ habs, _, _⟩,
  { exact hpb (dvd_mul_of_dvd_right (dvd_factorial (min_fac_pos _) habs) _) },
  { have hdiv : order_of (b : zmod p) ∣ p - 1 :=
      zmod.order_of_dvd_card_sub_one (mt (char_p.cast_eq_zero_iff _ _ _).1 hpb),
    haveI : ne_zero (k : zmod p) :=
      ne_zero.of_not_dvd (zmod p) (λ hpk, hpb (dvd_mul_of_dvd_left hpk _)),
    have : k = order_of (b : zmod p) := (is_root_cyclotomic_iff.mp hroot).eq_order_of,
    rw [← this] at hdiv,
    exact ((modeq_iff_dvd' hprime.1.pos).2 hdiv).symm }
end

lemma frequently_at_top_modeq_one {k : ℕ} (hk0 : k ≠ 0) :
  ∃ᶠ p in at_top, nat.prime p ∧ p ≡ 1 [MOD k] :=
begin
  refine frequently_at_top.2 (λ n, _),
  obtain ⟨p, hp⟩ := exists_prime_gt_modeq_one n hk0,
  exact ⟨p, ⟨hp.2.1.le, hp.1, hp.2.2⟩⟩
end

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
lemma infinite_set_of_prime_modeq_one {k : ℕ} (hk0 : k ≠ 0) :
  set.infinite {p : ℕ | nat.prime p ∧ p ≡ 1 [MOD k]} :=
frequently_at_top_iff_infinite.1 (frequently_at_top_modeq_one hk0)

end nat
