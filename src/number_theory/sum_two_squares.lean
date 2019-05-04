/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares
-/

import data.zsqrtd.gaussian_int data.zmod.quadratic_reciprocity ring_theory.principal_ideal_domain

open gaussian_int principal_ideal_domain zsqrtd

local notation `ℤ[i]` := gaussian_int

namespace nat
namespace prime

lemma sum_two_squares {p : ℕ} (hp : p.prime) (hp1 : p % 4 = 1) :
  ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
let ⟨k, hk⟩ := (zmodp.exists_pow_two_eq_neg_one_iff_mod_four_ne_three hp).2 $
  by rw hp1; exact dec_trivial in
have hpk : p ∣ k.val ^ 2 + 1,
  by rw [← zmodp.eq_zero_iff_dvd_nat hp]; simp *,
have hkmul : (k.val ^ 2 + 1 : ℤ[i]) = ⟨k.val, 1⟩ * ⟨k.val, -1⟩ :=
  by simp [_root_.pow_two, zsqrtd.ext],
have hpne1 : p ≠ 1, from (ne_of_lt (hp.gt_one)).symm,
have hkltp : 1 + k.val * k.val < p * p,
  from calc 1 + k.val * k.val ≤ k.val + k.val * k.val :
    add_le_add_right (nat.pos_of_ne_zero
      (λ hk0, by clear_aux_decl; simp [*, nat.pow_succ] at *)) _
  ... = k.val * (k.val + 1) : by simp [mul_add]
  ... < p * p : mul_lt_mul k.2 k.2 (nat.succ_pos _) (nat.zero_le _),
have hpk₁ : ¬ (p : ℤ[i]) ∣ ⟨k.val, -1⟩ :=
  λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm.nat_abs $
    calc (norm (p * x : ℤ[i])).nat_abs = (norm ⟨k.val, -1⟩).nat_abs : by rw hx
    ... < (norm (p : ℤ[i])).nat_abs : by simpa [norm] using hkltp
    ... ≤ (norm (p * x : ℤ[i])).nat_abs : norm_le_norm_mul_left _
      (λ hx0, (show (-1 : ℤ) ≠ 0, from dec_trivial) $
         by simpa [hx0] using congr_arg zsqrtd.im hx),
have hpk₂ : ¬ (p : ℤ[i]) ∣ ⟨k.val, 1⟩ :=
  λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm.nat_abs $
    calc (norm (p * x : ℤ[i])).nat_abs = (norm ⟨k.val, 1⟩).nat_abs : by rw hx
    ... < (norm (p : ℤ[i])).nat_abs : by simpa [norm] using hkltp
    ... ≤ (norm (p * x : ℤ[i])).nat_abs : norm_le_norm_mul_left _
      (λ hx0, (show (1 : ℤ) ≠ 0, from dec_trivial) $
          by simpa [hx0] using congr_arg zsqrtd.im hx),
have hpu : ¬ is_unit (p : ℤ[i]), from mt norm_eq_one_iff.2 $
  by rw [norm_nat_cast, int.nat_abs_mul, nat.mul_eq_one_iff];
  exact λ h, (ne_of_lt hp.gt_one).symm h.1,
let ⟨y, hy⟩ := hpk in
have hpi : ¬ irreducible (p : ℤ[i]),
  from mt irreducible_iff_prime.1
    (λ hp, by have := hp.2.2 ⟨k.val, 1⟩ ⟨k.val, -1⟩
        ⟨y, by rw [← hkmul, ← nat.cast_mul p, ← hy]; simp⟩;
      clear_aux_decl; tauto),
have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬ is_unit a ∧ ¬ is_unit b,
  by simpa [irreducible, hpu, classical.not_forall, not_or_distrib] using hpi,
let ⟨a, b, hpab, hau, hbu⟩ := hab in
have hnap : (norm a).nat_abs = p, from ((hp.mul_eq_prime_pow_two_iff
    (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 $
  by rw [← int.coe_nat_inj', int.coe_nat_pow, _root_.pow_two,
    ← @norm_nat_cast (-1), hpab];
    simp).1,
⟨a.re.nat_abs, a.im.nat_abs, by simpa [nat_abs_norm_eq, pow_two] using hnap⟩

end prime
end nat
