/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.big_operators data.nat.gcd

open finset

namespace nat

def totient (n : ℕ) : ℕ := ((range n).filter (nat.coprime n)).card

local notation `φ` := totient

lemma totient_le (n : ℕ) : φ n ≤ n :=
calc totient n ≤ (range n).card : card_le_of_subset (filter_subset _)
           ... = n              : card_range _

lemma totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ h, card_pos.2 (mt eq_empty_iff_forall_not_mem.1
(not_forall_of_exists_not ⟨1, not_not.2 $ mem_filter.2 ⟨mem_range.2 dec_trivial, by simp [coprime]⟩⟩))

lemma sum_totient (n : ℕ) : ((range n.succ).filter (∣ n)).sum φ = n :=
if hn0 : n = 0 then by rw hn0; refl
else
calc ((range n.succ).filter (∣ n)).sum φ
    = ((range n.succ).filter (∣ n)).sum (λ d, ((range (n / d)).filter (λ m, gcd (n / d) m = 1)).card) :
  eq.symm $ sum_bij (λ d _, n / d)
    (λ d hd, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _,
      by conv {to_rhs, rw ← nat.mul_div_cancel' (mem_filter.1 hd).2}; simp⟩)
    (λ _ _, rfl)
    (λ a b ha hb h,
      have ha : a * (n / a) = n, from nat.mul_div_cancel' (mem_filter.1 ha).2,
      have (n / a) > 0, from nat.pos_of_ne_zero (λ h, by simp [*, lt_irrefl] at *),
      by rw [← nat.mul_right_inj this, ha, h, nat.mul_div_cancel' (mem_filter.1 hb).2])
    (λ b hb,
      have hb : b < n.succ ∧ b ∣ n, by simpa [-range_succ] using hb,
      have hbn : (n / b) ∣ n, from ⟨b, by rw nat.div_mul_cancel hb.2⟩,
      have hnb0 : (n / b) ≠ 0, from λ h, by simpa [h, ne.symm hn0] using nat.div_mul_cancel hbn,
      ⟨n / b, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _, hbn⟩,
        by rw [← nat.mul_right_inj (nat.pos_of_ne_zero hnb0),
          nat.mul_div_cancel' hb.2, nat.div_mul_cancel hbn]⟩)
... = ((range n.succ).filter (∣ n)).sum (λ d, ((range n).filter (λ m, gcd n m = d)).card) :
  sum_congr rfl (λ d hd,
    have hd : d ∣ n, from (mem_filter.1 hd).2,
    have hd0 : 0 < d, from nat.pos_of_ne_zero (λ h, hn0 (eq_zero_of_zero_dvd $ h ▸ hd)),
    card_congr (λ m hm, d * m)
      (λ m hm, have hm : m < n / d ∧ gcd (n / d) m = 1, by simpa using hm,
        mem_filter.2 ⟨mem_range.2 $ nat.mul_div_cancel' hd ▸
          (mul_lt_mul_left hd0).2 hm.1,
          by rw [← nat.mul_div_cancel' hd, gcd_mul_left, hm.2, mul_one]⟩)
      (λ a b ha hb h, (nat.mul_left_inj hd0).1 h)
      (λ b hb, have hb : b < n ∧ gcd n b = d, by simpa using hb,
        ⟨b / d, mem_filter.2 ⟨mem_range.2 ((mul_lt_mul_left (show 0 < d, from hb.2 ▸ hb.2.symm ▸ hd0)).1
            (by rw [← hb.2, nat.mul_div_cancel' (gcd_dvd_left _ _),
              nat.mul_div_cancel' (gcd_dvd_right _ _)]; exact hb.1)),
                hb.2 ▸ coprime_div_gcd_div_gcd (hb.2.symm ▸ hd0)⟩,
          hb.2 ▸ nat.mul_div_cancel' (gcd_dvd_right _ _)⟩))
... = ((filter (∣ n) (range n.succ)).bind (λ d, (range n).filter (λ m, gcd n m = d))).card :
  (card_bind (by simp [finset.ext]; cc)).symm
... = (range n).card :
  congr_arg card (finset.ext.2 (λ m, ⟨by finish,
    λ hm, have h : m < n, from mem_range.1 hm,
      mem_bind.2 ⟨gcd n m, mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd (lt_of_le_of_lt (nat.zero_le _) h)
        (gcd_dvd_left _ _))), gcd_dvd_left _ _⟩, mem_filter.2 ⟨hm, rfl⟩⟩⟩))
... = n : card_range _

end nat