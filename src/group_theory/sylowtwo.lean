/-
Copyright (c) 2021 Anna Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anna Wright
-/
import data.zmod.basic
import data.fintype.card
import number_theory.padics.padic_norm

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

lemma card_P : card L = p ^ n :=
begin
  sorry
end

end is_sylow_subgroup

lemma exists_sylow_subgroup [fintype G] {p : ℕ} [fact p.prime]
: ∃ L : subgroup G, is_sylow_subgroup p L :=
begin
  -- establish m and n exist st card G = p ^ n * m from uniqueness of factors
  -- n and m only unique when ¬ p ∣ m as this maximises n
  -- need to show an L exists st card L = p ^ n
  -- what theorem guarantees this existence?
  sorry,
end


end sylow

#lint

-- will eventually need some lemma enforcing uniqueness of m and n
-- otherwise my sylow two proof won't work
