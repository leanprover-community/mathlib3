/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import number_theory.zsqrtd.gaussian_int
import number_theory.legendre_symbol.quadratic_reciprocity

/-!
# Facts about the gaussian integers relying on quadratic reciprocity.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

-/

open zsqrtd complex
open_locale complex_conjugate

local notation `ℤ[i]` := gaussian_int

namespace gaussian_int

open principal_ideal_ring

lemma mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : fact p.prime] (hpi : prime (p : ℤ[i])) :
  p % 4 = 3 :=
hp.1.eq_two_or_odd.elim
  (λ hp2, absurd hpi (mt irreducible_iff_prime.2 $
    λ ⟨hu, h⟩, begin
      have := h ⟨1, 1⟩ ⟨1, -1⟩ (hp2.symm ▸ rfl),
      rw [← norm_eq_one_iff, ← norm_eq_one_iff] at this,
      exact absurd this dec_trivial
    end))
  (λ hp1, by_contradiction $ λ hp3 : p % 4 ≠ 3,
    have hp41 : p % 4 = 1,
      begin
        rw [← nat.mod_mul_left_mod p 2 2, show 2 * 2 = 4, from rfl] at hp1,
        have := nat.mod_lt p (show 0 < 4, from dec_trivial),
        revert this hp3 hp1,
        generalize : p % 4 = m, dec_trivial!,
      end,
    let ⟨k, hk⟩ := zmod.exists_sq_eq_neg_one_iff.2 $
      by rw hp41; exact dec_trivial in
    begin
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (h : k' < p), (k' : zmod p) = k,
      { refine ⟨k.val, k.val_lt, zmod.nat_cast_zmod_val k⟩ },
      have hpk : p ∣ k ^ 2 + 1,
        by { rw [pow_two, ← char_p.cast_eq_zero_iff (zmod p) p, nat.cast_add, nat.cast_mul,
                 nat.cast_one, ← hk, add_left_neg], },
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ :=
        by simp [sq, zsqrtd.ext],
      have hpne1 : p ≠ 1 := ne_of_gt hp.1.one_lt,
      have hkltp : 1 + k * k < p * p,
        from calc 1 + k * k ≤ k + k * k :
          add_le_add_right (nat.pos_of_ne_zero
            (λ hk0, by clear_aux_decl; simp [*, pow_succ'] at *)) _
        ... = k * (k + 1) : by simp [add_comm, mul_add]
        ... < p * p : mul_lt_mul k_lt_p k_lt_p (nat.succ_pos _) (nat.zero_le _),
      have hpk₁ : ¬ (p : ℤ[i]) ∣ ⟨k, -1⟩ :=
        λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm.nat_abs $
          calc (norm (p * x : ℤ[i])).nat_abs = (zsqrtd.norm ⟨k, -1⟩).nat_abs : by rw hx
          ... < (norm (p : ℤ[i])).nat_abs : by simpa [add_comm, zsqrtd.norm] using hkltp
          ... ≤ (norm (p * x : ℤ[i])).nat_abs : norm_le_norm_mul_left _
            (λ hx0, (show (-1 : ℤ) ≠ 0, from dec_trivial) $
              by simpa [hx0] using congr_arg zsqrtd.im hx),
      have hpk₂ : ¬ (p : ℤ[i]) ∣ ⟨k, 1⟩ :=
        λ ⟨x, hx⟩, lt_irrefl (p * x : ℤ[i]).norm.nat_abs $
          calc (norm (p * x : ℤ[i])).nat_abs = (zsqrtd.norm ⟨k, 1⟩).nat_abs : by rw hx
          ... < (norm (p : ℤ[i])).nat_abs : by simpa [add_comm, zsqrtd.norm] using hkltp
          ... ≤ (norm (p * x : ℤ[i])).nat_abs : norm_le_norm_mul_left _
            (λ hx0, (show (1 : ℤ) ≠ 0, from dec_trivial) $
                by simpa [hx0] using congr_arg zsqrtd.im hx),
      have hpu : ¬ is_unit (p : ℤ[i]), from mt norm_eq_one_iff.2
        (by rw [norm_nat_cast, int.nat_abs_mul, mul_eq_one];
        exact λ h, (ne_of_lt hp.1.one_lt).symm h.1),
      obtain ⟨y, hy⟩ := hpk,
      have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← nat.cast_mul p, ← hy]; simp⟩,
      clear_aux_decl, tauto
    end)

lemma prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [hp : fact p.prime] (hp3 : p % 4 = 3) :
  prime (p : ℤ[i]) :=
irreducible_iff_prime.1 $ classical.by_contradiction $ λ hpi,
  let ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi in
have ∀ a b : zmod 4, a^2 + b^2 ≠ p, by erw [← zmod.nat_cast_mod p 4, hp3]; exact dec_trivial,
this a b (hab ▸ by simp)

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
lemma prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : fact p.prime] :
  prime (p : ℤ[i]) ↔ p % 4 = 3 :=
⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩

end gaussian_int
