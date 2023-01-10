/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import set_theory.cardinal.ordinal
import ring_theory.artinian

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

/-- A localization always has cardinality less than or equal to the base ring. -/
lemma card_le : #L ≤ #R :=
begin
  classical,
  casesI fintype_or_infinite R,
  { exact cardinal.mk_le_of_surjective (is_artinian_ring.localization_surjective S _) },
  erw [←cardinal.mul_eq_self $ cardinal.aleph_0_le_mk R],
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

lemma eq_one_of_zero_mem (h : (0 : R) ∈ S) (x : L) : x = 1 :=
suffices eq0 : mk' L (sec S x).1 (sec S x).2 = mk' L 1 (1 : S),
by rwa [mk'_sec, mk'_one, map_one] at eq0,
is_localization.eq.mpr ⟨⟨0, h⟩, by rw [subtype.coe_mk, mul_zero, mul_zero]⟩

lemma subsingleton_of_zero_mem (h : (0 : R) ∈ S) : subsingleton L :=
⟨λ x y, by rw [eq_one_of_zero_mem S L h x, eq_one_of_zero_mem S L h y]⟩

lemma zero_mem_of_subsingleton [subsingleton L] : (0 : R) ∈ S :=
begin
  have eq0 : mk' L 0 (1 : S) = mk' L 1 (1 : S) := subsingleton.elim _ _,
  rw [is_localization.eq, submonoid.coe_one, zero_mul, one_mul] at eq0,
  obtain ⟨c, hc⟩ := eq0,
  rw [one_mul, zero_mul] at hc,
  rw hc,
  exact c.2,
end

lemma subsingleton_iff_zero_mem : subsingleton L ↔ (0 : R) ∈ S :=
⟨λ h, by exactI zero_mem_of_subsingleton S L, subsingleton_of_zero_mem _ _⟩

end is_localization
