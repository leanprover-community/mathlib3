import algebra.gcd_monoid.multiset
import combinatorics.partition
import group_theory.perm.cycles
import ring_theory.int.basic
import tactic.linarith


lemma sign (h : is_three_cycle σ) : sign σ = 1 :=
begin
  rw [sign_of_cycle_type', h.cycle_type],
  refl,
end
