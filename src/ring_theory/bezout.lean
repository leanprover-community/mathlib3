/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.principal_ideal_domain
import algebra.gcd_monoid.integrally_closed

/-!

# Bézout rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A Bézout ring (Bezout ring) is a ring whose finitely generated ideals are principal.
Notible examples include principal ideal rings, valuation rings, and the ring of algebraic integers.

## Main results
- `is_bezout.iff_span_pair_is_principal`: It suffices to verify every `span {x, y}` is principal.
- `is_bezout.to_gcd_monoid`: Every Bézout domain is a GCD domain. This is not an instance.
- `is_bezout.tfae`: For a Bézout domain, noetherian ↔ PID ↔ UFD ↔ ACCP

-/

universes u v

variables (R : Type u) [comm_ring R]

/-- A Bézout ring is a ring whose finitely generated ideals are principal. -/
class is_bezout : Prop :=
(is_principal_of_fg : ∀ I : ideal R, I.fg → I.is_principal)

namespace is_bezout

variables {R}

instance span_pair_is_principal [is_bezout R] (x y : R) :
  (ideal.span {x, y} : ideal R).is_principal :=
by { classical, exact is_principal_of_fg (ideal.span {x, y}) ⟨{x, y}, by simp⟩ }

lemma iff_span_pair_is_principal :
  is_bezout R ↔ (∀ x y : R, (ideal.span {x, y} : ideal R).is_principal) :=
begin
  classical,
  split,
  { introsI H x y, apply_instance },
  { intro H,
    constructor,
    apply submodule.fg_induction,
    { exact λ _, ⟨⟨_, rfl⟩⟩ },
    { rintro _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩, rw ← submodule.span_insert, exact H _ _ } },
end

section gcd

variable [is_bezout R]

/-- The gcd of two elements in a bezout domain. -/
noncomputable
def gcd (x y : R) : R :=
submodule.is_principal.generator (ideal.span {x, y})

lemma span_gcd (x y : R) : (ideal.span {gcd x y} : ideal R) = ideal.span {x, y} :=
ideal.span_singleton_generator _

lemma gcd_dvd_left (x y : R) : gcd x y ∣ x :=
(submodule.is_principal.mem_iff_generator_dvd _).mp (ideal.subset_span (by simp))

lemma gcd_dvd_right (x y : R) : gcd x y ∣ y :=
(submodule.is_principal.mem_iff_generator_dvd _).mp (ideal.subset_span (by simp))

lemma dvd_gcd {x y z : R} (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y :=
begin
  rw [← ideal.span_singleton_le_span_singleton] at hx hy ⊢,
  rw [span_gcd, ideal.span_insert, sup_le_iff],
  exact ⟨hx, hy⟩
end

lemma gcd_eq_sum (x y : R) : ∃ a b : R, a * x + b * y = gcd x y :=
ideal.mem_span_pair.mp (by { rw ← span_gcd, apply ideal.subset_span, simp })

variable (R)

/-- Any bezout domain is a GCD domain. This is not an instance since `gcd_monoid` contains data,
and this might not be how we would like to construct it. -/
noncomputable
def to_gcd_domain [is_domain R] [decidable_eq R] :
  gcd_monoid R :=
gcd_monoid_of_gcd gcd gcd_dvd_left gcd_dvd_right
  (λ _ _ _, dvd_gcd)

end gcd

local attribute [instance] to_gcd_domain

-- Note that the proof, despite being `infer_instance`, depends on the `local attribute [instance]`
-- lemma above, and is thus necessary to be restated.
@[priority 100]
instance [is_domain R] [is_bezout R] : is_integrally_closed R :=
by classical; exact gcd_monoid.to_is_integrally_closed

lemma _root_.function.surjective.is_bezout {S : Type v} [comm_ring S] (f : R →+* S)
  (hf : function.surjective f) [is_bezout R] : is_bezout S :=
begin
  rw iff_span_pair_is_principal,
  intros x y,
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ⟨hf x, hf y⟩,
  use f (gcd x y),
  transitivity ideal.map f (ideal.span {gcd x y}),
  { rw [span_gcd, ideal.map_span, set.image_insert_eq, set.image_singleton] },
  { rw [ideal.map_span, set.image_singleton], refl }
end

@[priority 100]
instance of_is_principal_ideal_ring [is_principal_ideal_ring R] : is_bezout R :=
⟨λ I _, is_principal_ideal_ring.principal I⟩

lemma tfae [is_bezout R] [is_domain R] :
  tfae [is_noetherian_ring R,
    is_principal_ideal_ring R,
    unique_factorization_monoid R,
    wf_dvd_monoid R] :=
begin
  classical,
  tfae_have : 1 → 2,
  { introI H, exact ⟨λ I, is_principal_of_fg _ (is_noetherian.noetherian _)⟩ },
  tfae_have : 2 → 3,
  { introI _, apply_instance },
  tfae_have : 3 → 4,
  { introI _, apply_instance },
  tfae_have : 4 → 1,
  { rintro ⟨h⟩,
    rw [is_noetherian_ring_iff, is_noetherian_iff_fg_well_founded],
    apply rel_embedding.well_founded _ h,
    have : ∀ I : { J : ideal R // J.fg }, ∃ x : R, (I : ideal R) = ideal.span {x} :=
      λ ⟨I, hI⟩, (is_bezout.is_principal_of_fg I hI).1,
    choose f hf,
    exact
    { to_fun := f,
      inj' := λ x y e, by { ext1, rw [hf, hf, e] },
      map_rel_iff' := λ x y,
      by { dsimp, rw [← ideal.span_singleton_lt_span_singleton, ← hf, ← hf], refl } } },
  tfae_finish
end

end is_bezout
