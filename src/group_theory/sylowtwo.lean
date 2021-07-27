import data.zmod.basic
import data.fintype.card

open fintype subgroup
universe u
variables {G : Type u} [group G]

open_locale classical

namespace sylow

/-- define a sylow subgroup given a prime p, and subgroup L -/
def is_sylow_subgroup [fintype G] (p : ℕ) [fact p.prime] (L : subgroup G)  :=
  ∃ m n : ℕ, card L = p ^ n ∧ card G = p ^ n * m ∧ ¬ p ∣ m

namespace is_sylow_subgroup

variables [fintype G] {L : subgroup G} {p : ℕ} [fact p.prime] (h : is_sylow_subgroup p L)

/-- unique m which characterises sylow subgroup p -/
noncomputable def m := classical.some h
/-- unique n which characterises sylow subgroup p -/
noncomputable def n := classical.some (classical.some_spec h)

lemma card_G : card G = p ^ h.n * h.m := (classical.some_spec (classical.some_spec h)).2.1
lemma not_p_div_m : ¬ p ∣ h.m :=  (classical.some_spec (classical.some_spec h)).2.2
lemma card_P : card L = p ^ h.n := (classical.some_spec (classical.some_spec h)).1

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
