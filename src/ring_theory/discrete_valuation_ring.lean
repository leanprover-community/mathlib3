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

variables (S : Type u) [singleton S]

structure discrete_valuation_ring.discrete_valuation (R : Type u) [discrete_valuation_ring R] extends R →* with_zero (free_group S) :=
(map_top' : to_fun 0 = 1)
(map_add_leq' : ∀ x y, to_fun (x + y) ≤ max (to_fun x) (to_fun y))

namespace integral_domain

variable {R : Type u}
variable [integral_domain R]

lemma principal_ideal_generators_associated {a b : R} (h: ideal.span ({a} : set R) = ideal.span ({b} : set R)) (nonzero: ideal.span ({a} : set R) ≠ ⊥) : associated a b :=
begin
  rw [h,ne.def] at nonzero,
  rw le_antisymm_iff at h,
  cases h with hL hR,
  rw [ideal.span_singleton_le_span_singleton] at hL hR,
  cases hL with u hL,
  cases hR with v hR,
  have hR' := eq.symm hR,
  rw [hL, mul_assoc] at hR,
  conv at hR begin
    to_lhs,
    rw ← mul_one b,
  end,
  rw not_iff_not_of_iff ideal.span_singleton_eq_bot at nonzero,
  have h3 : 1 = u * v := eq_of_mul_eq_mul_left nonzero hR,
  have h4 := h3,
  rw mul_comm at h4,
  use {val := v, inv := u, val_inv := eq.symm h4, inv_val := eq.symm h3},
  assumption,
end

end integral_domain

namespace discrete_valuation_ring

variable {R : Type u}
variable [discrete_valuation_ring R]

instance is_prime : ideal.is_prime (prime_ideal R) := primality

noncomputable instance is_unique_factorization_domain : unique_factorization_domain R := principal_ideal_domain.to_unique_factorization_domain

lemma prime_ideal_is_maximal : (prime_ideal R).is_maximal :=
is_prime.to_maximal_ideal is_nonzero

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
      exact a.right (prime_ideal R) (bot_lt_iff_ne_bot.2 discrete_valuation_ring.is_nonzero) },
    { assumption } }
end

instance is_local_ring : local_ring R := local_of_unique_max_ideal unique_max_ideal

def uniformizers : set R := { π | prime_ideal R = ideal.span {π} }

lemma exists_uniformizer : ∃ π, π ∈ (uniformizers : set R) :=
⟨ideal.is_principal.generator (prime_ideal R), eq.symm (ideal.is_principal.span_singleton_generator (prime_ideal R))⟩

lemma uniformizers_are_associated {π₁ π₂ : R} (h₁ : π₁ ∈ (uniformizers : set R)) (h₂ : π₂ ∈ (uniformizers : set R)) : associated π₁ π₂ :=
integral_domain.principal_ideal_generators_associated (eq.trans (eq.symm h₁) h₂) (ne.symm (ne_of_ne_of_eq (ne.symm is_nonzero) h₁))

open_locale classical

def to_discrete_valuation : discrete_valuation R :=
{ to_fun := λ r : R, if r = 0 then ⊤ else 0,
  map_zero' := begin  end,
  map_add' := sorry,
  map_top' := sorry,
  map_add_leq' := sorry}

lemma element_of_dvr (r : R) (nonzero: r ≠ 0) (π : R) (unif: π ∈ (uniformizers : set R)) : ∃! (n : ℕ) , associated r (π ^ n) :=
begin
  have prod := unique_factorization_domain.factors_prod nonzero,
  have primal := unique_factorization_domain.prime_factors nonzero,
  have prime_is_unif : ∀ x : R, prime x → x ∈ (uniformizers : set R),
  { intros x a,
    have b := a.left,
    rw ← ideal.span_singleton_prime b at a,
    cases unique_nonzero_prime_ideal (ideal.span {x}) a,
    { exfalso,
        rw ideal.span_singleton_eq_bot at h,
      contradiction },
    { unfold uniformizers,
      exact eq.symm h } },
  have nonzero : ∀ x : R, x ∈ unique_factorization_domain.factors r → x ≠ 0,
  { intros x h,
    exact (primal x h).left },
  have assoc : ∀ a b : R, a ∈ unique_factorization_domain.factors r ∧ b ∈ unique_factorization_domain.factors r → associated a b,
  { intros a b h,
    cases h with ha hb,
    exact uniformizers_are_associated (prime_is_unif a (primal a ha)) (prime_is_unif b (primal b hb)) },

end

end discrete_valuation_ring
