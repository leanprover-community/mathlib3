/-
Copyright (c) 2020 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ashwin Iyengar
-/

import ring_theory.ideals
import ring_theory.principal_ideal_domain

universe u

class discrete_valuation_ring (R : Type u) extends principal_ideal_domain R :=
(prime_ideal' : ideal R)
(primality : prime_ideal'.is_prime)
(is_nonzero : prime_ideal' ≠ ⊥)
(unique_nonzero_prime_ideal : ∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = prime_ideal')

def discrete_valuation_ring.prime_ideal (R : Type u) [discrete_valuation_ring R] : ideal R :=
discrete_valuation_ring.prime_ideal'

namespace integral_domain

variable {R : Type u}
variable [integral_domain R]

lemma principal_ideal_generators_differ_by_units (a b : R) (h: ideal.span ({a} : set R) = ideal.span ({b} : set R)) (nonzero: ideal.span ({a} : set R) ≠ ⊥) : ∃ u : units R, a = u * b :=
begin
  rw ne.def at nonzero,
  rw le_antisymm_iff at h,
  cases h with hL hR,
  rw [ideal.span_singleton_le_span_singleton] at hL hR,
  cases hL with u hL,
  cases hR with v hR,
  have hL' := hL,
  rw [hR, mul_assoc] at hL,
  conv at hL begin
    to_lhs,
    rw ← mul_one a,
  end,
  rw not_iff_not_of_iff ideal.span_singleton_eq_bot at nonzero,
  have h3 : 1 = v * u := eq_of_mul_eq_mul_left nonzero hL,
  have h4 := h3,
  rw mul_comm at h4,
  use {val := u, inv := v, val_inv := eq.symm h4, inv_val := eq.symm h3},
  rw mul_comm at hL',
  assumption
end

end integral_domain

namespace discrete_valuation_ring

variable {R : Type u}
variable [discrete_valuation_ring R]

lemma prime_ideal_is_maximal : (prime_ideal R).is_maximal :=
begin
  split,
  { exact primality.left },
  { intros J h,
    contrapose h,
    obtain ⟨M, hMl, hMr⟩ := J.exists_le_maximal h,
    intro w,
    have h3 := lt_of_lt_of_le w hMr,
    have hQ := unique_nonzero_prime_ideal M hMl.is_prime,
    revert h3,
    rcases hQ; rw hQ,
    { simp },
    { exact lt_irrefl _ } }
end

lemma unique_max_ideal : ∃! I : ideal R, I.is_maximal :=
begin
  use prime_ideal R,
  split,
  { exact prime_ideal_is_maximal },
  { intros y a,
    cases discrete_valuation_ring.unique_nonzero_prime_ideal y a.is_prime,
    { exfalso,
      rw h at a,
      apply discrete_valuation_ring.primality.left,
      have h5 : prime_ideal R ≠ ⊥ := discrete_valuation_ring.is_nonzero,
      rw ← bot_lt_iff_ne_bot at h5,
      exact a.right (prime_ideal R) h5 },
    { assumption } }
end

instance is_local_ring : local_ring R := local_of_unique_max_ideal unique_max_ideal

def uniformizers : set R := { π | prime_ideal R = ideal.span {π} }

lemma exists_uniformizer : ∃ π, π ∈ (uniformizers : set R) := (principal_ideal_domain.principal (prime_ideal R)).principal

/-lemma uniformizers_differ_by_units (π₁ : R) (h1: π₁ ∈ (uniformizers : set R)) (π₂ : R) (h2: π₂ ∈ (uniformizers : set R)) : ∃ u : units R, π₁ = u * π₂ :=
begin
  have h := eq.trans h1.symm h2,
  have h3 := is_nonzero,
  rw (show prime_ideal R = ideal.span ({π₁} : set R), from h1) at h3,
  exact integral_domain.principal_ideal_generators_differ_by_units _ _ (eq.trans h1.symm h2) is_nonzero,
end-/


end discrete_valuation_ring
