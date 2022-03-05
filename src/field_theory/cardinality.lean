/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import ring_theory.localization.cardinality
import set_theory.cardinal_divisibility
import field_theory.finite.galois_field
import data.equiv.transfer_instance
import algebra.ring.ulift
import data.mv_polynomial.cardinal
import data.rat.denumerable

/-!
# Cardinality of Fields

In this file we show all the possible cardinalities of fields. All infinite cardinals can harbour
a field structure, and so can all types with prime power cardinalities, and this is sharp.

## Main statements

* `fintype.nonempty_field_iff`: A `fintype` can be given a field structure iff its cardinality is a
  prime power.
* `infinite.nonempty_field` : Any infinite type can be endowed a field structure.
* `field.nonempty_iff` : There is a field structure on type iff its cardinality is a prime power.

-/

local notation `‖` x `‖` := fintype.card x

open_locale cardinal non_zero_divisors

universe u

/-- A finite field has prime power cardinality. -/
lemma fintype.is_prime_pow_card_of_field {α} [fintype α] [field α] : is_prime_pow (‖α‖) :=
begin
  casesI char_p.exists α with p _,
  haveI hp := fact.mk (char_p.char_is_prime α p),
  let b := is_noetherian.finset_basis (zmod p) α,
  rw [module.card_fintype b, zmod.card, is_prime_pow_pow_iff],
  { exact hp.1.is_prime_pow },
  rw ←finite_dimensional.finrank_eq_card_basis b,
  exact finite_dimensional.finrank_pos.ne'
end

/-- A `fintype` can be given a field structure iff its cardinality is a prime power. -/
lemma fintype.nonempty_field_iff {α} [fintype α] : nonempty (field α) ↔ is_prime_pow (‖α‖) :=
begin
  refine ⟨λ ⟨h⟩, by exactI fintype.is_prime_pow_card_of_field, _⟩,
  rintros ⟨p, n, hp, hn, hα⟩,
  haveI := fact.mk (nat.prime_iff.mpr hp),
  exact ⟨(fintype.equiv_of_card_eq ((galois_field.card p n hn.ne').trans hα)).symm.field⟩,
end

lemma fintype.not_is_field_of_card_not_prime_pow {α} [fintype α] [ring α] :
  ¬ is_prime_pow (‖α‖) → ¬ is_field α :=
mt $ λ h, fintype.nonempty_field_iff.mp ⟨h.to_field α⟩

/-- Any infinite type can be endowed a field structure. -/
lemma infinite.nonempty_field {α : Type u} [infinite α] : nonempty (field α) :=
begin
  letI K := fraction_ring (mv_polynomial α $ ulift.{u} ℚ),
  suffices : #α = #K,
  { obtain ⟨e⟩ := cardinal.eq.1 this,
    exact ⟨e.field⟩ },
  rw ←is_localization.card (mv_polynomial α $ ulift.{u} ℚ)⁰ K le_rfl,
  apply le_antisymm,
  { refine ⟨⟨λ a, mv_polynomial.monomial (finsupp.single a 1) (1 : ulift.{u} ℚ), λ x y h, _⟩⟩,
    simpa [mv_polynomial.monomial_eq_monomial_iff, finsupp.single_eq_single_iff] using h },
  { simpa using @mv_polynomial.cardinal_mk_le_max α (ulift.{u} ℚ) _ }
end

/-- There is a field structure on type if and only if its cardinality is a prime power. -/
lemma field.nonempty_iff {α : Type u} : nonempty (field α) ↔ is_prime_pow (#α) :=
begin
  rw cardinal.is_prime_pow_iff,
  casesI fintype_or_infinite α with h h,
  { simpa only [cardinal.mk_fintype, nat.cast_inj, exists_eq_left',
        (cardinal.nat_lt_omega _).not_le, false_or]
      using fintype.nonempty_field_iff },
  { simpa only [← cardinal.infinite_iff, h, true_or, iff_true]
      using infinite.nonempty_field },
end
