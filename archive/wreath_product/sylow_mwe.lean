import group_theory.sylow
import tactic

open fintype

variables {G : Type*} [group G]

def card_eq_multiplicity_to_sylow [fintype G] {p : ℕ} [hp : fact (nat.prime p)]
  (H : subgroup G) [fintype H]
  (eq_card: card H = p ^ nat.factorization (card G) p) : sylow p G :=
{
  to_subgroup := H,
  is_p_group' := is_p_group.of_card eq_card,
  is_maximal' := begin
    intros Q is_p_Q hHQ,
    obtain ⟨P, hQP⟩ := is_p_group.exists_le_sylow is_p_Q,
    have eq_HP : H.subgroup_of ↑P = ⊤ := begin
      classical,
      apply subgroup.eq_top_of_card_eq,
      rw card_congr ((subgroup.subgroup_of_equiv_of_le (le_trans hHQ hQP)).to_equiv),
      rw eq_card,
      have coe_eq : ↥(↑ P : subgroup G) = ↥ P  := begin
        rw ← sylow.to_subgroup_eq_coe,
        refl,
      end,
      rw card_congr (equiv.cast coe_eq),
      symmetry,
      exact (sylow.card_eq_multiplicity P),
    end,
    rw subgroup.subgroup_of_eq_top at eq_HP,
    exact le_antisymm (le_trans hQP eq_HP) hHQ,
  end,
}

@[simp]
lemma card_eq_multiplicity_to_sylow_coe [fintype G] {p : ℕ} [hp : fact (nat.prime p)]
  (H : subgroup G) [fintype H]
  (eq_card: card H = p ^ nat.factorization (card G) p) : ↑(card_eq_multiplicity_to_sylow H eq_card) = H := rfl
