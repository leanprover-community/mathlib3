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

* `torsion G`, the torsion subgroup of an abelian group `G`
* `monoid.is_torsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `add_monoid.is_torsion` the additive version of `monoid.is_torsion`.

## Implementation

All torsion monoids are really groups (which is proven here as `monoid.is_torsion.group`), but since
the definition can be stated on monoids it is implemented on `monoid` to match other declarations in
the group theory library.

## Tags

periodic groups, torsion subgroup, torsion abelian group

## Future work

* torsion-free groups
-/

variable {G : Type*}

namespace monoid

variables (G) [monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def is_torsion := ∀ g : G, is_of_fin_order g

end monoid

open monoid

/-- Torsion monoids are really groups. -/
@[to_additive "Torsion additive monoids are really additive groups"]
noncomputable def is_torsion.group [monoid G] (tG : is_torsion G) : group G :=
{ inv := λ g, g ^ (order_of g - 1),
  mul_left_inv := λ g,
  begin
    erw [←pow_succ', tsub_add_cancel_of_le, pow_order_of_eq_one],
    exact order_of_pos' (tG g)
  end,
  ..‹monoid G› }

section group

variables [group G] {N : subgroup G}

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
lemma is_torsion.subgroup (tG : is_torsion G) (H : subgroup G) : is_torsion H :=
λ h, (is_of_fin_order_iff_coe _ h).mpr $ tG h

/-- Quotient groups of torsion groups are torsion groups. -/
@[to_additive "Quotient groups of additive torsion groups are additive torsion groups."]
lemma is_torsion.quotient_group [nN : N.normal] (tG : is_torsion G) : is_torsion (G ⧸ N) :=
λ h, quotient_group.induction_on' h $ λ g, (tG g).quotient N g

/-- If a group exponent exists, the group is torsion. -/
@[to_additive exponent_exists.is_add_torsion
  "If a group exponent exists, the group is additively torsion."]
lemma exponent_exists.is_torsion (h : exponent_exists G) : is_torsion G := begin
  obtain ⟨n, npos, hn⟩ := h,
  intro g,
  exact (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, npos, hn g⟩,
end

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive is_add_torsion.exponent_exists
  "The group exponent exists for any bounded additive torsion group."]
lemma is_torsion.exponent_exists
  (tG : is_torsion G) (bounded : (set.range (λ g : G, order_of g)).finite) :
  exponent_exists G :=
exponent_exists_iff_ne_zero.mpr $
  (exponent_ne_zero_iff_range_order_of_finite (λ g, order_of_pos' (tG g))).mpr bounded

/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_fintype "Finite additive groups are additive torsion groups."]
lemma is_torsion_of_fintype [fintype G] : is_torsion G :=
exponent_exists.is_torsion $ exponent_exists_iff_ne_zero.mpr exponent_ne_zero_of_fintype

end group

section comm_group

variables (G) [comm_group G]

/-- The torsion subgroup of an abelian group. -/
@[to_additive add_tor "The torsion subgroup of an additive abelian group."]
def torsion : subgroup G :=
{ carrier := {x | is_of_fin_order x},
  one_mem' := is_of_fin_order_one,
  inv_mem' := λ x, is_of_fin_order.inv,
  mul_mem' := λ _ _ hx hy, hx.mul hy }

variables {G}

/-- Torsion subgroups are torsion. -/
@[to_additive "Additive torsion subgroups are additively torsion."]
lemma torsion.is_torsion : is_torsion $ torsion G :=
λ ⟨_, n, npos, hn⟩,
  ⟨n, npos, subtype.ext $
    by rw [mul_left_iterate, _root_.mul_one, subgroup.coe_pow,
           subtype.coe_mk, subgroup.coe_one, (is_periodic_pt_mul_iff_pow_eq_one _).mp hn]⟩

namespace monoid.is_torsion

/-- The torsion subgroup of a torsion group is `⊤`. -/
@[simp, to_additive "The additive torsion subgroup of an additive torsion group is `⊤`."]
lemma torsion_eq_top (tG : is_torsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion group is isomorphic to its own torsion group. -/
@[to_additive "A torsion additive group is isomorphic to its own torsion group."]
def torsion_mul_equiv (tG : is_torsion G) : torsion G ≃* G :=
by rw tG.torsion_eq_top; exact subgroup.top_equiv

end monoid.is_torsion

/-- Torsion subgroups of torsion subgroups are isomorphic to the subgroup. -/
@[simp, to_additive
  "Additive torsion subgroups of additive torsion subgroups are isomorphic to the subgroup."]
def torsion.of_torsion : (torsion (torsion G)) ≃* (torsion G) :=
monoid.is_torsion.torsion_mul_equiv torsion.is_torsion

end comm_group
