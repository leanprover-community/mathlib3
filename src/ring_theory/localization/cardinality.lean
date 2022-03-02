/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import ring_theory.localization.basic
import set_theory.cardinal_ordinal
import ring_theory.integral_domain

/-!
# Cardinality of localizations

In this file, we establish the cardinality of localizations. In most cases, a localization has
cardinality equal to the base ring (even in the finite case!); however, this can be muddled by
zero-divisors.

## Main statements

* `is_localization.cardinal_mk`: All infinite localizations of rings at submonoids smaller than the
  non-zero divisors have the same cardinality as the base ring.
* `is_localization.card`: All localizations of finite integral domains at submonoids not containing
  zero have the same cardinality as the base domain.

## Implementation details

Note that in `is_localization.card`, the second `fintype` is not an instance, and is instead
provided by `is_localization.fintype' S L`.

-/


open_locale cardinal non_zero_divisors

universes u v

namespace is_localization

variables {R : Type u} [comm_ring R] (S : submonoid R) {L : Type u} [comm_ring L]
  [algebra R L] [hl : is_localization S L]
include hl

lemma algebra_map_surj [fintype R] : function.surjective (algebra_map R L) :=
begin
  classical,
  haveI : fintype L := is_localization.fintype' S L,
  intro x, have := hl.surj, rcases this x with ⟨⟨r,s⟩,h⟩,
  have hu := hl.map_units, have := exists_pow_eq_one (hu s).unit,
  rcases (is_of_fin_order_iff_pow_eq_one _).1 this with ⟨n,hn,hp⟩,
  rw [units.ext_iff, units.coe_pow] at hp, change algebra_map R L s ^ n = 1 at hp,
  rw [← nat.succ_pred_eq_of_pos hn, pow_succ] at hp,
  use r * s ^ (n-1), erw [map_mul, map_pow, ← h, mul_assoc, hp, mul_one],
end

lemma card_le : #L ≤ #R :=
begin
  classical, by_cases infinite R, resetI,
  { erw [←cardinal.mul_eq_self $ cardinal.omega_le_mk R],
    let f : R × R → L := λ aa, is_localization.mk' _ aa.1 (if h : aa.2 ∈ S then ⟨aa.2, h⟩ else 1),
    refine @cardinal.mk_le_of_surjective _ _ f (λ a, _),
    obtain ⟨x, y, h⟩ := is_localization.mk'_surjective S a,
    use (x, y),
    dsimp [f],
    rwa [dif_pos $ show ↑y ∈ S, from y.2, set_like.eta] },
  haveI : fintype R := fintype_of_not_infinite h,
  exact cardinal.mk_le_of_surjective (algebra_map_surj S),
end

/-- All infinite localizations of rings at submonoids smaller than the non-zero divisors have the
same cardinality as the base ring. -/
lemma cardinal_mk {R : Type u} [comm_ring R] {S : submonoid R} (L : Type u) [comm_ring L]
  [algebra R L] [infinite R] [is_localization S L] (hS : S ≤ R⁰) : #R = #L :=
begin
  classical,
  apply (cardinal.mk_le_of_injective (is_localization.injective L hS)).antisymm,
  erw [←cardinal.mul_eq_self $ cardinal.omega_le_mk R],
  let f : R × R → L := λ aa, is_localization.mk' _ aa.1 (if h : aa.2 ∈ S then ⟨aa.2, h⟩ else 1),
  refine @cardinal.mk_le_of_surjective _ _ f (λ a, _),
  obtain ⟨x, y, h⟩ := is_localization.mk'_surjective S a,
  use (x, y),
  dsimp [f],
  rwa [dif_pos $ show ↑y ∈ S, from y.2, set_like.eta]
end

/-- All finite localizations of integral domains at submonoids not containing zero have the same
cardinality as the base domain. -/
lemma card {R : Type u} [comm_ring R] {S : submonoid R} {L : Type v} [comm_ring L] [algebra R L]
  [fintype R] [is_domain R] [is_localization S L] (hS : ↑0 ∉ S) :
  fintype.card R = @fintype.card L (fintype' S L) :=
begin
  casesI subsingleton_or_nontrivial R,
  { haveI := unique R L S,
    haveI := unique_of_subsingleton (0 : R),
    simp only [fintype.card_unique] },
  letI := fintype' S L,
  exact fintype.card_of_bijective ((fintype.is_field_of_domain R).localization_map_bijective hS),
end

end is_localization
