/-
Copyright (c) 2021 Anna Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anna Wright
-/
import data.zmod.basic
import data.fintype.card
import number_theory.padics.padic_norm
import data.nat.prime

open fintype subgroup
universe u
variables {G : Type u} [group G]

open_locale classical

namespace sylow

/-- define a sylow subgroup given a prime p, and subgroup L -/
def is_sylow_subgroup [fintype G] (p : ℕ) [fact p.prime] (L : subgroup G)  :=
  ∃ m n : ℕ, card L = p ^ n ∧ card G = p ^ n * m ∧ ¬ p ∣ m

namespace is_sylow_subgroup

variables (G) [fintype G] {L : subgroup G} (p : ℕ) [fact p.prime] (h : is_sylow_subgroup p L)

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
  exact pow_succ_padic_val_nat_not_dvd p (card_pos_iff.2 has_one.nonempty) h,
end

include h
lemma card_L : card L = p ^ n :=
begin
  rcases h with ⟨x, y, hy1, hy2, hy3⟩,
  rw [hy2, hy1],
  congr,
  rw padic_val_nat.mul p _ _,
  {
    rw [padic_val_nat_of_not_dvd hy3, add_zero, padic_val_nat_eq_factors_count],

    sorry, },
  {  exact pow_ne_zero _ (nat.prime.ne_zero (fact.out _)) },
  {
    have h : 0 ≠ card G := ne_of_lt (card_pos_iff.2 has_one.nonempty),
    rw hy2 at h,
    exact right_ne_zero_of_mul (ne.symm h) }
end


end is_sylow_subgroup

end sylow
