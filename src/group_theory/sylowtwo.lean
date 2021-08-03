/-
Copyright (c) 2021 Anna Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anna Wright
-/
import data.zmod.basic
import data.fintype.card
import number_theory.padics.padic_norm
import data.nat.prime
/-!
# Sylow theorems

## Main statements

## TODO

* Prove the second and third of the Sylow theorems.
* Sylow theorems for infinite groups
-/
open fintype subgroup
universe u
variables {G : Type u} [group G] [fintype G]

open_locale classical

namespace sylow

/-- define a sylow subgroup given a prime p, and subgroup L -/
def is_sylow_subgroup (p : ℕ) [fact p.prime] (L : subgroup G)  :=
  ∃ m n : ℕ, card L = p ^ n ∧ card G = p ^ n * m ∧ ¬ p ∣ m

lemma is_sylow_def (p : ℕ) [fact p.prime] (L : subgroup G) :
is_sylow_subgroup p L ↔ ∃ m n : ℕ, card L = p ^ n ∧ card G = p ^ n * m ∧ ¬ p ∣ m := iff.rfl

namespace is_sylow_subgroup

variables (p : ℕ) [fact p.prime] (G)

/-- unique n which characterises sylow subgroup p -/
local notation `n` := padic_val_nat p (card G)

/-- unique m which characterises sylow subgroup p -/
local notation `m` := card G / p ^ n

lemma card_G : card G = p ^ n * m :=
begin
  rw ← nat.div_eq_iff_eq_mul_right (pow_pos (nat.prime.pos (fact.out _ )) n) pow_padic_val_nat_dvd,
end

lemma not_p_div_m : ¬ p ∣ m :=
begin
  rintros ⟨x, hx⟩,
  have h : p ^ (n + 1) ∣ card G,
  { refine ⟨x, _⟩,
    conv_lhs {rw card_G G p},
    simp [hx, pow_add, mul_assoc] },
  exact pow_succ_padic_val_nat_not_dvd (card_pos_iff.2 has_one.nonempty) h,
end

lemma card_L {L : subgroup G} (h : is_sylow_subgroup p L) : card L = p ^ n :=
begin
  rcases h with ⟨x, y, hy1, hy2, hy3⟩,
  rw [hy1, hy2],
  congr,
  have h : 0 ≠ card G := ne_of_lt (card_pos_iff.2 has_one.nonempty),
  rw hy2 at h,
  rw padic_val_nat.mul p _ (right_ne_zero_of_mul (ne.symm h)),
  { rw [padic_val_nat_of_not_dvd hy3, add_zero],
  exact (valuation_prime_pow_eq_pow p y).symm, },
  exact pow_ne_zero _ (nat.prime.ne_zero (fact.out _)),
end

end is_sylow_subgroup

end sylow
