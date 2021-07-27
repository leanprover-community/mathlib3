import data.zmod.basic
import data.fintype.card
import number_theory.padics.padic_numbers

open fintype subgroup
universe u
variables {G : Type u} [group G]

open_locale classical

namespace sylow

/-- define a sylow subgroup given a prime p, and subgroup L -/
def is_sylow_subgroup [fintype G] (p : ℕ) [fact p.prime] (L : subgroup G)  :=
  ∃ m n : ℕ, card L = p ^ n ∧ card G = p ^ n * m ∧ ¬ p ∣ m

namespace is_sylow_subgroup

variables [fintype G] {L : subgroup G} {p : ℕ} [hp : fact p.prime] (h : is_sylow_subgroup p L)

variables (G) (p)
/-- unique n which characterises sylow subgroup p -/
abbreviation n := padic_val_nat p (fintype.card G)

/-- unique m which characterises sylow subgroup p -/
abbreviation m := fintype.card G / p ^ (n G p)

variables {G} {p}

include hp
lemma card_G : card G = p ^ (n G p) * (m G p) :=
begin
  rw ← nat.div_eq_iff_eq_mul_right (pow_pos (nat.prime.pos hp.elim) (n G p)),
  sorry,
end

lemma not_p_div_m : ¬ p ∣ (m G p) := sorry
lemma card_P : card L = p ^ (n G p) := sorry

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
