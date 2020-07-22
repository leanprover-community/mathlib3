/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.principal_ideal_domain order.conditionally_complete_lattice
import ring_theory.multiplicity
import ring_theory.valuation.basic
import tactic

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `discrete_valuation_ring R` : a predicate expressing that R is a DVR

### Notation

It's a theorem that an element of a DVR is a uniformiser if and only if it's irreducible.
We do not hence define `uniformiser` at all, because we can use `irreducible` instead.

### Definitions

## Implementation notes

## Tags

discrete valuation ring
-/

open_locale classical

universe u

open ideal local_ring

section prio
set_option default_priority 100 -- see Note [default priority]
/-- An integral domain is a discrete valuation ring if it's a local PID which is not a field -/
class discrete_valuation_ring (R : Type u) [integral_domain R]
  extends is_principal_ideal_ring R, local_ring R : Prop :=
(not_a_field' : maximal_ideal R ≠ ⊥)
end prio

namespace discrete_valuation_ring

variables (R : Type u) [integral_domain R] [discrete_valuation_ring R]

lemma not_a_field : maximal_ideal R ≠ ⊥ := not_a_field'

variable {R}

open principal_ideal_ring

/-- An element of a DVR is irreducible iff it is a uniformiser, that is, generates the
  maximal ideal of R -/
theorem irreducible_iff_uniformiser (ϖ : R) :
  irreducible ϖ ↔ maximal_ideal R = ideal.span {ϖ} :=
⟨λ hϖ, (eq_maximal_ideal (is_maximal_of_irreducible hϖ)).symm,
begin
  intro h,
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
end⟩

variable (R)

/-- Uniformisers exist in a DVR -/
theorem exists_irreducible : ∃ ϖ : R, irreducible ϖ :=
by {simp_rw [irreducible_iff_uniformiser],
    exact (is_principal_ideal_ring.principal $ maximal_ideal R).principal}

/-- an integral domain is a DVR iff it's a PID with a unique non-zero prime ideal -/
theorem iff_PID_with_one_nonzero_prime (R : Type u) [integral_domain R] :
  discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P :=
begin
  split,
  { intro RDVR,
    rcases id RDVR with ⟨RPID, Rlocal, Rnotafield⟩,
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
      replace hQ2 := irreducible_of_prime hQ2,
      rw irreducible_iff_uniformiser at hQ2,
      exact hQ2.symm}},
  { rintro ⟨RPID, Punique⟩,
    haveI : local_ring R := local_of_unique_nonzero_prime R Punique,
    refine {not_a_field' := _},
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, hP3⟩,
    have hPM : P ≤ maximal_ideal R := le_maximal_ideal (hP2.1),
    intro h, rw [h, le_bot_iff] at hPM, exact hP1 hPM}
end

lemma associated_of_irreducible {a b : R} (ha : irreducible a) (hb : irreducible b) :
  associated a b :=
begin
  rw irreducible_iff_uniformiser at ha hb,
  rw [←span_singleton_eq_span_singleton, ←ha, hb],
end

end discrete_valuation_ring
