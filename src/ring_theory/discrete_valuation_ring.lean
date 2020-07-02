/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.principal_ideal_domain
import tactic

/-!
# Discrete valuation rings

There are ten definitions on Wikipedia.

## Important definitions

### Notation

### Definitions

## Implementation notes

## Tags

discrete valuation ring
-/

open_locale classical

universe u

open ideal local_ring

/-- A commutative ring is a discrete valuation ring if it's a local PID which is not a field -/
class discrete_valuation_ring (R : Type u) [integral_domain R]
  extends is_principal_ideal_ring R, local_ring R : Prop :=
(not_a_field' : maximal_ideal R ≠ ⊥)

namespace discrete_valuation_ring

variables (R : Type u) [integral_domain R] [discrete_valuation_ring R]

-- TODO: this should be localised
local notation `is_uniformiser` := irreducible

def not_a_field : maximal_ideal R ≠ ⊥ := not_a_field'

variable {R}
theorem uniformiser_iff_generator (ϖ : R) :
  is_uniformiser ϖ ↔ maximal_ideal R = ideal.span {ϖ} :=
begin
  split,
  { intro hϖ,
    cases (is_principal_ideal_ring.principal $ maximal_ideal R).principal with m hm,
    have hϖ2 : ϖ ∈ maximal_ideal R := hϖ.1,
    rw hm at hϖ2,
    rw submodule.mem_span_singleton at hϖ2,
    cases hϖ2 with a ha,
    -- rw algebra.id.smul_eq_mul at ha,
    cases hϖ.2 _ _ ha.symm,
    { rw hm,
      show ideal.span {m} = _,
      rw ←ha,
      exact (span_singleton_mul_left_unit h _).symm},
    { have h2 : ¬(is_unit m) := show m ∈ maximal_ideal R,
      from hm.symm ▸ submodule.mem_span_singleton_self m,
      exact absurd h h2}},
  { intro h,
    have h2 : ¬(is_unit ϖ) := show ϖ ∈ maximal_ideal R,
      from h.symm ▸ submodule.mem_span_singleton_self ϖ,
    split, exact h2,
    intros a b hab,
    by_contra h,
    push_neg at h,
    cases h with ha hb,
    change a ∈ maximal_ideal R at ha,
    change b ∈ maximal_ideal R at hb,
    rw h at ha hb,
    rw mem_span_singleton' at ha hb,
    rcases ha with ⟨a, rfl⟩,
    rcases hb with ⟨b, rfl⟩,
    rw (show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)), by ring) at hab,
    have h3 := eq_zero_of_mul_eq_self_right _ hab.symm,
    { apply not_a_field R,
      simp [h, h3]},
    { intro hh, apply h2,
      refine is_unit_of_dvd_one ϖ _,
      use a * b, exact hh.symm}
    }
end

theorem exists_uniformiser : ∃ ϖ : R, is_uniformiser ϖ :=
by {simp_rw [uniformiser_iff_generator],
    exact (is_principal_ideal_ring.principal $ maximal_ideal R).principal}

/-
Proving a result in Cassels-Froehlich: a DVR is a PID with exactly one non-zero prime ideal
-/

lemma local_of_unique_nonzero_prime (R : Type u) [comm_ring R]
  (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
local_of_unique_max_ideal begin
  rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
  refine ⟨P, ⟨hPnot_top, _⟩, λ M hM, hPunique _ ⟨_, is_maximal.is_prime hM⟩⟩,
  { refine maximal_of_no_maximal (λ M hPM hM, ne_of_lt hPM _),
    exact (hPunique _ ⟨ne_bot_of_gt hPM, is_maximal.is_prime hM⟩).symm },
  { rintro rfl,
    exact hPnot_top (hM.2 P (bot_lt_iff_ne_bot.2 hPnonzero)) },
end

-- -- delete this
-- lemma local_of_unique_nonzero_prime'' (R : Type u) [comm_ring R]
-- (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
-- local_of_unique_max_ideal
-- begin
--   rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
--   use P,
--   split,
--   { split, exact hPnot_top,
--     apply maximal_of_no_maximal,
--     intros M hPM hM,
--     apply ne_of_lt hPM,
--     symmetry,
--     apply hPunique,
--     split, apply ne_bot_of_gt hPM,
--     exact is_maximal.is_prime hM},
--   { intros M hM,
--     apply hPunique,
--     split,
--     { rintro rfl,
--       cases hM with hM1 hM2,
--       specialize hM2 P (bot_lt_iff_ne_bot.2 hPnonzero),
--       exact hPnot_top hM2},
--     { exact is_maximal.is_prime hM}}
-- end

-- lemma local_of_unique_nonzero_prime' (R : Type u) [comm_ring R]
-- (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
-- let ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩ := h in
-- local_of_unique_max_ideal ⟨P, ⟨hPnot_top,
--   maximal_of_no_maximal $ λ M hPM hM, ne_of_lt hPM $ (hPunique _ ⟨ne_bot_of_gt hPM, is_maximal.is_prime hM⟩).symm⟩,
--   _
--  λ M hM, hPunique _ ⟨λ h, hPnot_top $ hM.2 _ (_ : M < P), is_maximal.is_prime hM⟩⟩

-- lemma local_of_unique_nonzero_prime' (R : Type u) [comm_ring R]
-- (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
-- let ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩ := h in
-- local_of_unique_max_ideal ⟨P, ⟨hPnot_top,
--   maximal_of_no_maximal $ λ M hPM hM, ne_of_lt hPM $ (hPunique _ ⟨ne_bot_of_gt hPM, is_maximal.is_prime hM⟩).symm⟩,
--   λ M hM, hPunique _ ⟨λ (h : M = ⊥), hPnot_top $ hM.2 _ (h.symm ▸ (bot_lt_iff_ne_bot.2 hPnonzero : ⊥ < P) : M < P), is_maximal.is_prime hM⟩⟩

-- a DVR is a PID with exactly one non-zero prime ideal

theorem iff_PID_with_one_nonzero_prime (R : Type u) [integral_domain R] :
  discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P :=
begin
  split,
  { rintro ⟨RPID, Rlocal, Rnotafield⟩,
    split, assumption,
    resetI,
    use local_ring.maximal_ideal R,
    split, split,
    { assumption},
    { apply_instance},
    { rintro Q ⟨hQ1, hQ2⟩,
      obtain ⟨q, rfl⟩ := (is_principal_ideal_ring.principal Q).1,
      have hq : q ≠ 0,
      { rintro rfl,
        apply hQ1,
        simp,
      },
      erw span_singleton_prime hq at hQ2,

      -- lunch time; back around 2 to 2:15

      -- q is prime and hence irreducible
      -- say max ideal of R is gen by m
      -- Q ⊆ M so q=tm ∈ Q and so t is a unit
      sorry}},
  { rintro ⟨RPID, Punique⟩,
    haveI : local_ring R := local_of_unique_nonzero_prime R Punique,
    refine {not_a_field' := _},
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, hP3⟩,
    have hPM : P ≤ maximal_ideal R := le_maximal_ideal (hP2.1),
    intro h, rw [h, le_bot_iff] at hPM, exact hP1 hPM}
end

end discrete_valuation_ring

/-
Wikipedia:
In abstract algebra, a discrete valuation ring (DVR) is a principal ideal domain (PID)
with exactly one non-zero maximal ideal.

This means a DVR is an integral domain R which satisfies any one of the following equivalent conditions:

-- USED    R is a local principal ideal domain, and not a field.
    R is a valuation ring with a value group isomorphic to the integers under addition.
    R is a local Dedekind domain and not a field.
    R is a Noetherian local domain whose maximal ideal is principal, and not a field.[1]
    R is an integrally closed Noetherian local ring with Krull dimension one.
-- WORKING ON THIS    R is a principal ideal domain with a unique non-zero prime ideal.
    R is a principal ideal domain with a unique irreducible element (up to multiplication by units).
    R is a unique factorization domain with a unique irreducible element (up to multiplication by units).
    R is Noetherian, not a field, and every nonzero fractional ideal of R is irreducible in the sense that it cannot be written as a finite intersection of fractional ideals properly containing it.
    There is some discrete valuation ν on the field of fractions K of R such that R = {x : x in K, ν(x) ≥ 0}.

Serre defines a DVR to be a PID with a unique non-zero prime ideal and one can build the
theory relatively quickly from this.
-/
