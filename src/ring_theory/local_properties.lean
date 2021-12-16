/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.localization
import data.equiv.transfer_instance
import group_theory.submonoid.pointwise
import ring_theory.nilpotent

/-!
# Local properties of commutative rings

In this file, we provide the proofs of various local properties.

## Naming Conventions

* `localization_P` : `P` holds for `S⁻¹R` if `P` holds for `R`.
* `P_of_localization_maximal` : `P` holds for `R` if `P` holds for `Aₘ` for all maximal `m`.
* `P_of_localization_span` : `P` holds for `R` if given a spanning set `{fᵢ}`, `P` holds for all
  `A_{fᵢ}`.

## Main results

The following properties are covered:

* The triviality of an ideal or an element:
  `ideal_eq_zero_of_localization`, `eq_zero_of_localization`
* `is_reduced` : `localization_is_reduced`, `is_reduced_of_localization_maximal`.

-/

open_locale pointwise classical big_operators

universe u

variables {R S : Type u} [comm_ring R] [comm_ring S] (M : submonoid R)
variables (N : submonoid S) (R' S' : Type u) [comm_ring R'] [comm_ring S'] (f : R →+* S)
variables [algebra R R'] [algebra S S']

section properties

section comm_ring
variable (P : ∀ (R : Type u) [comm_ring R], Prop)

include P

/-- A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`. -/
def localization_preserves : Prop :=
  ∀ {R : Type u} [hR : comm_ring R] (M : by exactI submonoid R) (S : Type u) [hS : comm_ring S]
    [by exactI algebra R S] [by exactI is_localization M S], @P R hR → @P S hS

/-- A property `P` of comm rings satisfies `of_localization_maximal` if
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`. -/
def of_localization_maximal : Prop :=
  ∀ (R : Type u) [comm_ring R],
    by exactI (∀ (J : ideal R) (hJ : J.is_maximal), by exactI P (localization.at_prime J)) → P R

end comm_ring


end properties

section ideal

-- This proof should work for all modules, but we do not know how to localize a module yet.
/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
lemma ideal_eq_zero_of_localization (I : ideal R)
   (h : ∀ (J : ideal R) (hJ : J.is_maximal),
      by exactI is_localization.coe_submodule (localization.at_prime J) I = 0) : I = 0 :=
begin
  by_contradiction hI,
  obtain ⟨x, hx, hx'⟩ := set.exists_of_ssubset (bot_lt_iff_ne_bot.mpr hI),
  rw [submodule.bot_coe, set.mem_singleton_iff] at hx',
  have H : (ideal.span ({x} : set R)).annihilator ≠ ⊤,
  { rw [ne.def, submodule.annihilator_eq_top_iff],
    by_contra,
    apply hx',
    rw [← set.mem_singleton_iff, ← @submodule.bot_coe R, ← h],
    exact ideal.subset_span (set.mem_singleton x) },
  obtain ⟨p, hp₁, hp₂⟩ := ideal.exists_le_maximal _ H,
  resetI,
  specialize h p hp₁,
  have : algebra_map R (localization.at_prime p) x = 0,
  { rw ← set.mem_singleton_iff,
    change algebra_map R (localization.at_prime p) x ∈ (0 : submodule R (localization.at_prime p)),
    rw ← h,
    exact submodule.mem_map_of_mem hx },
  rw is_localization.map_eq_zero_iff p.prime_compl at this,
  obtain ⟨m, hm⟩ := this,
  apply m.prop,
  refine hp₂ _,
  erw submodule.mem_annihilator_span_singleton,
  rwa mul_comm at hm,
end

lemma eq_zero_of_localization (r : R)
   (h : ∀ (J : ideal R) (hJ : J.is_maximal),
      by exactI algebra_map R (localization.at_prime J) r = 0) : r = 0 :=
begin
  rw ← ideal.span_singleton_eq_bot,
  apply ideal_eq_zero_of_localization,
  intros J hJ,
  delta is_localization.coe_submodule,
  erw [submodule.map_span, submodule.span_eq_bot],
  rintro _ ⟨_, h', rfl⟩,
  cases set.mem_singleton_iff.mpr h',
  exact h J hJ,
end

end ideal

section reduced

lemma localization_is_reduced : localization_preserves (λ R hR, by exactI is_reduced R) :=
begin
  introv R _ _,
  resetI,
  constructor,
  rintro x ⟨(_|n), e⟩,
  { simpa using congr_arg (*x) e },
  obtain ⟨⟨y, m⟩, hx⟩ := is_localization.surj M x,
  dsimp only at hx,
  let hx' := congr_arg (^ n.succ) hx,
  simp only [mul_pow, e, zero_mul, ← ring_hom.map_pow] at hx',
  rw [← (algebra_map R S).map_zero] at hx',
  obtain ⟨m', hm'⟩ := (is_localization.eq_iff_exists M S).mp hx',
  apply_fun (*m'^n) at hm',
  simp only [mul_assoc, zero_mul] at hm',
  rw [mul_comm, ← pow_succ, ← mul_pow] at hm',
  replace hm' := is_nilpotent.eq_zero ⟨_, hm'.symm⟩,
  rw [← (is_localization.map_units S m).mul_left_inj, hx, zero_mul,
    is_localization.map_eq_zero_iff M],
  exact ⟨m', by rw [← hm', mul_comm]⟩
end

instance [is_reduced R] : is_reduced (localization M) := localization_is_reduced M _ infer_instance

lemma is_reduced_of_localization_maximal :
  of_localization_maximal (λ R hR, by exactI is_reduced R) :=
begin
  introv R h,
  constructor,
  intros x hx,
  apply eq_zero_of_localization,
  intros J hJ,
  specialize h J hJ,
  resetI,
  exact (hx.map $ algebra_map R $ localization.at_prime J).eq_zero,
end

end reduced
