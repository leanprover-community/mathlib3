import data.nat.pow
import group_theory.sylow
import logic.equiv.fin

import .iterated

open nat

noncomputable lemma sylow_perm_prime_power (p n : ℕ) [fact (nat.prime p)]
  (G : Type*) [group G] [fintype G] (h : fintype.card G = p)
  (P : sylow p (equiv.perm (fin (p^n)))) : ↥P ≃* iterated_wreath_product G n :=begin
  sorry
end
