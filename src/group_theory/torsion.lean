/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/

import group_theory.exponent
import group_theory.order_of_element
import group_theory.quotient_group

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `monoid.is_torsion` is a predicate asserting a monoid `G` is a torsion monoid, i.e. that all
  elements are of finite order. Torsion groups are also known as periodic groups.
* `add_monoid.is_torsion` the additive version of `monoid.is_torsion`.

## Main results

-/

universe u

variable {G : Type u}

open_locale classical

namespace monoid

variables (G) [monoid G]

/--A predicate on a monoid saying that all elements are of finite order.-/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def is_torsion := ∀ g : G, is_of_fin_order g

end monoid

open monoid

variables [group G] {N : subgroup G}

/--Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
lemma subgroup.is_torsion {tG : is_torsion G} (H : subgroup G) : is_torsion H := begin
  intro g,
  obtain ⟨n, ⟨npos, hn⟩⟩ := (is_of_fin_order_iff_pow_eq_one ↑g).mp (tG _),
  rw is_of_fin_order_iff_pow_eq_one,
  refine ⟨n, npos, subtype.coe_injective _⟩,
  simp only [hn, subgroup.coe_pow, subgroup.coe_one],
end

/--Quotient groups of torsion groups are torsion groups. -/
lemma quotient_group.is_torsion [nN : N.normal] (tG : is_torsion G) : is_torsion (G ⧸ N) :=
λ g, quotient.induction_on' g $ λ a, begin
  rw is_of_fin_order_iff_pow_eq_one,
  obtain ⟨n, ⟨npos, hn⟩⟩ := (is_of_fin_order_iff_pow_eq_one _).mp (tG a),
  exact ⟨n, npos, (quotient_group.con N).eq.mpr (hn ▸ (quotient_group.con N).eq.mp rfl)⟩,
end

/--If a group exponent exists, the group is torsion. -/
lemma exponent_exists.is_torsion (h : exponent_exists G) : is_torsion G := begin
  intro g,
  obtain ⟨n, ⟨npos, hn⟩⟩ := h,
  exact ⟨n, npos, (is_periodic_pt_mul_iff_pow_eq_one _).mpr $ hn g⟩,
end

/--Finite groups are torsion groups.-/
lemma is_torsion_of_fintype [fintype G] : is_torsion G :=
exponent_exists.is_torsion $ exponent_exists_iff_ne_zero.mpr exponent_ne_zero_of_fintype
