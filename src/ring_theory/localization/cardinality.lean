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
cardinality equal to the base ring. If there are zero-divisors, however, this is no longer true -
for example, `zmod 6` localized at `{2, 4}` is equal to `zmod 3`, and if you have zero in your
submonoid, then your localization is trivial (see `is_localization.unique_of_zero_mem`).

## Main statements

* `is_localization.card_le`: A localization has cardinality no larger than the base ring.
* `is_localization.card`: If you don't localize at zero-divisors, the localization of a ring has
  cardinality equal to its base ring,

-/


open_locale cardinal non_zero_divisors

universes u v

namespace is_localization

variables {R : Type u} [comm_ring R] (S : submonoid R) {L : Type u} [comm_ring L]
          [algebra R L] [is_localization S L]
include S

/-- Localizing a finite ring can only reduce the amount of elements. -/
lemma algebra_map_surjective_of_fintype [fintype R] : function.surjective (algebra_map R L) :=
begin
  classical,
  haveI : fintype L := is_localization.fintype' S L,
  intro x,
  obtain ⟨⟨r, s⟩, h : x * (algebra_map R L) ↑s = (algebra_map R L) r⟩ := is_localization.surj S x,
  obtain ⟨n, hn, hp⟩ :=
    (is_of_fin_order_iff_pow_eq_one _).1 (exists_pow_eq_one (is_localization.map_units L s).unit),
  rw [units.ext_iff, units.coe_pow, is_unit.unit_spec, ←nat.succ_pred_eq_of_pos hn, pow_succ] at hp,
  exact ⟨r * s ^ (n - 1), by erw [map_mul, map_pow, ←h, mul_assoc, hp, mul_one]⟩
end

/-- A localization always has cardinality less than or equal to the base ring. -/
lemma card_le : #L ≤ #R :=
begin
  classical,
  casesI fintype_or_infinite R,
  { exact cardinal.mk_le_of_surjective (algebra_map_surjective_of_fintype S) },
  erw [←cardinal.mul_eq_self $ cardinal.omega_le_mk R],
  set f : R × R → L := λ aa, is_localization.mk' _ aa.1 (if h : aa.2 ∈ S then ⟨aa.2, h⟩ else 1),
  refine @cardinal.mk_le_of_surjective _ _ f (λ a, _),
  obtain ⟨x, y, h⟩ := is_localization.mk'_surjective S a,
  use (x, y),
  dsimp [f],
  rwa [dif_pos $ show ↑y ∈ S, from y.2, set_like.eta]
end

variables (L)

/-- If you do not localize at any zero-divisors, localization preserves cardinality. -/
lemma card (hS : S ≤ R⁰) : #R = #L :=
(cardinal.mk_le_of_injective (is_localization.injective L hS)).antisymm (card_le S)

end is_localization
